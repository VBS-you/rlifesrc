//! The search process.

use crate::{
    cells::{CellRef, ConflReason, SetReason, State},
    // clause::Clause,
    config::NewState,
    rules::Rule,
    world::World,
};

#[cfg(feature = "stdweb")]
use serde::{Deserialize, Serialize};

/// Search status.
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "stdweb", derive(Serialize, Deserialize))]
pub enum Status {
    /// A result is found.
    Found,
    /// Such pattern does not exist.
    None,
    /// Still searching.
    Searching,
    /// Paused.
    Paused,
}

impl<'a, R: Rule> World<'a, R> {
    /// Consistifies a cell.
    ///
    /// Examines the state and the neighborhood descriptor of the cell,
    /// and makes sure that it can validly produce the cell in the next
    /// generation. If possible, determines the states of some of the
    /// cells involved.
    ///
    /// If there is a conflict, returns its reason.
    fn consistify(&mut self, cell: CellRef<'a, R>) -> Result<(), ConflReason<'a, R>> {
        Rule::consistify(self, cell)
    }

    /// Consistifies a cell, its neighbors, and its predecessor.
    ///
    /// If there is a conflict, returns its reason.
    fn consistify10(&mut self, cell: CellRef<'a, R>) -> Result<(), ConflReason<'a, R>> {
        self.consistify(cell)?;
        if let Some(pred) = cell.pred {
            self.consistify(pred)?;
        }
        for &neigh in cell.nbhd.iter() {
            self.consistify(neigh.unwrap())?;
        }
        Ok(())
    }

    /// Deduces all the consequences by `consistify` and symmetry.
    ///
    /// If there is a conflict, returns its reason.
    fn proceed(&mut self) -> Result<(), ConflReason<'a, R>> {
        while self.check_index < self.set_stack.len() {
            let cell = self.set_stack[self.check_index];
            let state = cell.state.get().unwrap();

            // Determines some cells by symmetry.
            for &sym in cell.sym.iter() {
                if let Some(old_state) = sym.state.get() {
                    if state != old_state {
                        return Err(ConflReason::Sym(cell, sym));
                    }
                } else {
                    self.set_cell(sym, state, SetReason::Sym(cell, sym))?;
                }
            }

            // Determines some cells by `consistify`.
            self.consistify10(cell)?;

            self.check_index += 1;
        }
        Ok(())
    }

    /// Backtracks to the last time when a unknown cell is assumed,
    /// and returns this cell and its state.
    ///
    /// Returns `None` if it goes back to the time before the first cell is set.
    fn cancel(&mut self) -> Option<(CellRef<'a, R>, State)> {
        while let Some(cell) = self.set_stack.pop() {
            match cell.reason.get() {
                Some(SetReason::Assume(i)) => {
                    self.check_index = self.set_stack.len();
                    self.search_index = i + 1;
                    let state = cell.state.get().unwrap();
                    self.clear_cell(cell);
                    return Some((cell, state));
                }
                None => unreachable!(),
                _ => {
                    self.clear_cell(cell);
                }
            }
        }
        self.check_index = 0;
        self.search_index = 0;
        None
    }

    /// Backtracks to the last time when a unknown cell is assumed,
    /// and switch that cell to the other state.
    ///
    /// Returns `false` if it goes back to the time before the first cell is set.
    fn backup(&mut self) -> bool {
        while let Some((cell, state)) = self.cancel() {
            if self.set_cell(cell, !state, SetReason::Conflict).is_ok() {
                return true;
            }
        }
        false
    }

    /// Backtracks to the last time when a unknown cell is assumed,
    /// switch that cell to the other state, and learns a clause from the
    /// conflict.
    ///
    /// Returns `true` if it backtracks successfully,
    /// `false` if it goes back to the time before the first cell is set.
    fn analyze(&mut self, reason: ConflReason<'a, R>) -> bool {
        match reason {
            ConflReason::Conflict | ConflReason::CellCount | ConflReason::Succeed => self.backup(),
            _ => {
                let mut reason_clause = reason.to_lits(None);
                let mut seen = Vec::new();
                let mut max_level = 0;
                let mut counter = 0;
                loop {
                    for &lit in reason_clause.iter() {
                        if !seen.contains(&lit.cell) {
                            seen.push(lit.cell);
                            let level = lit.cell.level.get();
                            if level == Some(self.level) {
                                counter += 1;
                            } else if level.is_some() && level.unwrap() > 0 {
                                max_level = max_level.max(level.unwrap())
                            }
                        }
                    }
                    if let Some(cell) = self.set_stack.pop() {
                        let reason = cell.reason.get().unwrap();
                        match reason {
                            SetReason::Assume(i) => {
                                self.check_index = self.set_stack.len();
                                self.search_index = i + 1;
                                let state = cell.state.get().unwrap();
                                self.clear_cell(cell);
                                if self.set_cell(cell, !state, SetReason::Conflict).is_ok() {
                                    return true;
                                } else {
                                    return self.backup();
                                }
                            }
                            SetReason::Conflict | SetReason::Init => {
                                self.clear_cell(cell);
                                return self.backup();
                            }
                            _ => {
                                if seen.contains(&cell) {
                                    let state = cell.state.get().unwrap();
                                    self.clear_cell(cell);
                                    if counter == 1 {
                                        while max_level < self.level {
                                            self.cancel();
                                        }
                                        if self.set_cell(cell, !state, SetReason::Conflict).is_ok()
                                        {
                                            return true;
                                        } else {
                                            return self.backup();
                                        }
                                    } else {
                                        reason_clause = reason.to_lits(Some(cell));
                                        if cell.level.get() == Some(self.level) {
                                            counter -= 1;
                                        }
                                    }
                                } else {
                                    reason_clause.clear();
                                    self.clear_cell(cell);
                                }
                            }
                        }
                    } else {
                        self.check_index = 0;
                        self.search_index = 0;
                        return false;
                    }
                }
            }
        }
    }

    /// Keeps proceeding and backtracking,
    /// until there are no more cells to examine (and returns `true`),
    /// or the backtracking goes back to the time before the first cell is set
    /// (and returns `false`).
    ///
    /// It also records the number of steps it has walked in the parameter
    /// `step`. A step consists of a `proceed` and a `backup`.
    ///
    /// The difference between `step` and `self.steps` is that the former
    /// will be resetted in each `search`.
    fn go(&mut self, step: &mut u64) -> bool {
        loop {
            *step += 1;
            match self.proceed() {
                Ok(()) => return true,
                Err(reason) => {
                    self.conflicts += 1;
                    if !self.analyze(reason) {
                        return false;
                    }
                }
            }
        }
    }

    /// Makes a decision.
    ///
    /// Chooses an unknown cell, assigns a state for it,
    /// and push a reference to it to the `set_stack`.
    ///
    /// Returns `None` is there is no unknown cell,
    /// `Some(false)` if the new state leads to an immediate conflict.
    fn decide(&mut self) -> Option<Result<(), ConflReason<'a, R>>> {
        if let Some((i, cell)) = self.get_unknown(self.search_index) {
            self.search_index = i + 1;
            let state = match self.new_state {
                NewState::Choose(State::Dead) => cell.background,
                NewState::Choose(State::Alive) => !cell.background,
                NewState::Random => rand::random(),
            };
            Some(self.set_cell(cell, state, SetReason::Assume(i)))
        } else {
            None
        }
    }

    /// The search function.
    ///
    /// Returns `Found` if a result is found,
    /// `None` if such pattern does not exist,
    /// `Searching` if the number of steps exceeds `max_step`
    /// and no results are found.
    pub fn search(&mut self, max_step: Option<u64>) -> Status {
        let mut step_count = 0;
        if self.get_unknown(0).is_none() && !self.backup() {
            return Status::None;
        }
        while self.go(&mut step_count) {
            if let Some(result) = self.decide() {
                if result.is_err() && !self.backup() {
                    return Status::None;
                }
            } else if self.nontrivial() {
                if self.reduce_max {
                    let cell_count = *self.cell_count.iter().min().unwrap();
                    self.max_cell_count = Some(cell_count - 1);
                }
                return Status::Found;
            } else if !self.backup() {
                return Status::None;
            }

            if let Some(max) = max_step {
                if step_count > max {
                    return Status::Searching;
                }
            }
        }
        Status::None
    }
}

/// A trait for `World`.
///
/// So that we can switch between different rule types using trait objects.
pub trait Search {
    /// The search function.
    ///
    /// Returns `Found` if a result is found,
    /// `None` if such pattern does not exist,
    /// `Searching` if the number of steps exceeds `max_step`
    /// and no results are found.
    fn search(&mut self, max_step: Option<u64>) -> Status;

    /// Displays the whole world in some generation.
    ///
    /// * **Dead** cells are represented by `.`;
    /// * **Living** cells are represented by `O`;
    /// * **Unknown** cells are represented by `?`.
    fn display_gen(&self, t: isize) -> String;

    /// Period of the pattern.
    fn period(&self) -> isize;

    /// Number of known living cells in the first generation.
    fn cell_count(&self, t: isize) -> usize;

    /// Number of conflicts during the search.
    fn conflicts(&self) -> u64;

    /// Set the max cell counts.
    ///
    /// Currently this is the only parameter that you can change
    /// during the search.
    fn set_max_cell_count(&mut self, max_cell_count: Option<usize>);
}

/// The `Search` trait is implemented for every `World`.
impl<'a, R: Rule> Search for World<'a, R> {
    fn search(&mut self, max_step: Option<u64>) -> Status {
        self.search(max_step)
    }

    fn display_gen(&self, t: isize) -> String {
        self.display_gen(t)
    }

    fn period(&self) -> isize {
        self.period
    }

    fn cell_count(&self, t: isize) -> usize {
        self.cell_count[t as usize]
    }

    fn conflicts(&self) -> u64 {
        self.conflicts
    }

    fn set_max_cell_count(&mut self, max_cell_count: Option<usize>) {
        self.max_cell_count = max_cell_count;
        if let Some(max) = self.max_cell_count {
            while *self.cell_count.iter().min().unwrap() > max {
                if !self.backup() {
                    break;
                }
            }
        }
    }
}
