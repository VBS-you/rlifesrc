//! The search process.

use crate::{
    cells::{CellRef, Reason, State},
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
    fn consistify(&mut self, cell: CellRef<'a, R>) -> Result<(), Reason<'a, R>> {
        Rule::consistify(self, cell)
    }

    /// Consistifies a cell, its neighbors, and its predecessor.
    ///
    /// If there is a conflict, returns its reason.
    fn consistify10(&mut self, cell: CellRef<'a, R>) -> Result<(), Reason<'a, R>> {
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
    fn proceed(&mut self) -> Result<(), Reason<'a, R>> {
        while self.check_index < self.set_stack.len() {
            // Tests if the number of living cells exceeds the `max_cell_count`.
            if let Some(max) = self.max_cell_count {
                if self.gen0_cell_count > max {
                    return Err(Reason::Conflict);
                }
            }

            // Tests if the first row / column is empty.
            if self.non_empty_front && self.front_cell_count == 0 {
                return Err(Reason::Conflict);
            }

            let cell = self.set_stack[self.check_index];
            let state = cell.state.get().unwrap();

            // Determines some cells by symmetry.
            for &sym in cell.sym.iter() {
                if let Some(old_state) = sym.state.get() {
                    if state != old_state {
                        return Err(Reason::Sym(cell));
                    }
                } else {
                    self.set_cell(sym, state, Reason::Sym(cell));
                }
            }

            // Determines some cells by `consistify`.
            self.consistify10(cell)?;

            self.check_index += 1;
        }
        Ok(())
    }

    /// Backtracks to the last time when a unknown cell is decided by choice,
    /// and switch that cell to the other state.
    ///
    /// Returns `true` if it backtracks successfully,
    /// `false` if it goes back to the time before the first cell is set.
    fn backup(&mut self) -> bool {
        while let Some(cell) = self.set_stack.pop() {
            match cell.reason.get() {
                Some(Reason::Decide(i)) => {
                    self.check_index = self.set_stack.len();
                    self.search_index = i + 1;
                    let state = !cell.state.get().unwrap();
                    self.set_cell(cell, state, Reason::Conflict);
                    return true;
                }
                None => unreachable!(),
                _ => {
                    self.clear_cell(cell);
                }
            }
        }
        self.check_index = 0;
        self.search_index = 0;
        false
    }

    /// Backtracks to the last time when a unknown cell is decided by choice,
    /// and switch that cell to the other state.
    ///
    /// Returns `true` if it backtracks successfully,
    /// `false` if it goes back to the time before the first cell is set.
    fn backup_with_reason(&mut self, _reason: Reason<'a, R>) -> bool {
        while let Some(cell) = self.set_stack.pop() {
            match cell.reason.get() {
                Some(Reason::Decide(i)) => {
                    self.check_index = self.set_stack.len();
                    self.search_index = i + 1;
                    let state = !cell.state.get().unwrap();
                    self.set_cell(cell, state, Reason::Conflict);
                    return true;
                }
                None => unreachable!(),
                _ => {
                    self.clear_cell(cell);
                }
            }
        }
        self.check_index = 0;
        self.search_index = 0;
        false
    }

    /// Keeps proceeding and backtracking,
    /// until there are no more cells to examine (and returns `true`),
    /// or the backtracking goes back to the time before the first cell is set
    /// (and returns `false`).
    ///
    /// It also records the number of steps it has walked in the parameter
    /// `step`. A step consists of a `proceed` and a `backup`.
    fn go(&mut self, step: &mut u32) -> bool {
        loop {
            *step += 1;
            match self.proceed() {
                Ok(()) => return true,
                Err(reason) => {
                    if !self.backup_with_reason(reason) {
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
    /// Returns `false` is there is no unknown cell.
    fn decide(&mut self) -> bool {
        if let Some((i, cell)) = self.get_unknown(self.search_index) {
            self.search_index = i + 1;
            let state = match self.new_state {
                NewState::Choose(State::Dead) => cell.background,
                NewState::Choose(State::Alive) => !cell.background,
                NewState::Random => rand::random(),
            };
            self.set_cell(cell, state, Reason::Decide(i));
            true
        } else {
            false
        }
    }

    /// The search function.
    ///
    /// Returns `Found` if a result is found,
    /// `None` if such pattern does not exist,
    /// `Searching` if the number of steps exceeds `max_step`
    /// and no results are found.
    pub fn search(&mut self, max_step: Option<u32>) -> Status {
        let mut step_count = 0;
        if self.get_unknown(0).is_none() && !self.backup() {
            return Status::None;
        }
        while self.go(&mut step_count) {
            if !self.decide() {
                if self.nontrivial() {
                    return Status::Found;
                } else if !self.backup() {
                    return Status::None;
                }
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
    fn search(&mut self, max_step: Option<u32>) -> Status;

    /// Displays the whole world in some generation.
    ///
    /// * **Dead** cells are represented by `.`;
    /// * **Living** cells are represented by `O`;
    /// * **Unknown** cells are represented by `?`.
    fn display_gen(&self, t: isize) -> String;

    /// Period of the pattern.
    fn period(&self) -> isize;

    /// Number of known living cells in the first generation.
    fn gen0_cell_count(&self) -> u32;
}

/// The `Search` trait is implemented for every `World`.
impl<'a, R: Rule> Search for World<'a, R> {
    fn search(&mut self, max_step: Option<u32>) -> Status {
        self.search(max_step)
    }

    fn display_gen(&self, t: isize) -> String {
        self.display_gen(t)
    }

    fn period(&self) -> isize {
        self.period
    }

    fn gen0_cell_count(&self) -> u32 {
        self.gen0_cell_count
    }
}
