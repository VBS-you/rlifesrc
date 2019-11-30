use crate::{
    cells::{CellRef, ConflReason, SetReason, State},
    rules::Rule,
};
use std::{iter::once, ops::Not};

/// A `Lit` says that some `cell` has some `state`.
pub(crate) struct Lit<'a, R: Rule> {
    pub(crate) cell: CellRef<'a, R>,
    pub(crate) state: State,
}

impl<'a, R: Rule> Clone for Lit<'a, R> {
    fn clone(&self) -> Self {
        Lit {
            cell: self.cell,
            state: self.state,
        }
    }
}

impl<'a, R: Rule> Copy for Lit<'a, R> {}

impl<'a, R: Rule> PartialEq for Lit<'a, R> {
    fn eq(&self, other: &Self) -> bool {
        self.cell == other.cell && self.state == other.state
    }
}

impl<'a, R: Rule> Eq for Lit<'a, R> {}

impl<'a, R: Rule> Not for Lit<'a, R> {
    type Output = Self;

    fn not(self) -> Self::Output {
        Lit {
            cell: self.cell,
            state: !self.state,
        }
    }
}

pub(crate) struct Clause<'a, R: Rule> {
    pub(crate) lits: Vec<Lit<'a, R>>,
}

impl<'a, R: Rule> Clone for Clause<'a, R> {
    fn clone(&self) -> Self {
        Clause {
            lits: self.lits.clone(),
        }
    }
}

impl<'a, R: Rule> SetReason<'a, R> {
    pub(crate) fn to_lits(self, cell: CellRef<'a, R>) -> Vec<Lit<'a, R>> {
        match self {
            SetReason::Rule(cell0) => cell0
                .nbhd
                .iter()
                .chain(once(&Some(cell0)))
                .chain(once(&cell0.succ))
                .filter_map(|&c| {
                    c.and_then(|c| {
                        if c != cell {
                            c.state.get().map(|state| Lit { cell: c, state })
                        } else {
                            None
                        }
                    })
                })
                .collect(),
            SetReason::Sym(sym) => vec![Lit {
                cell: sym,
                state: sym.state.get().unwrap(),
            }],
            _ => Vec::new(),
        }
    }
}

impl<'a, R: Rule> ConflReason<'a, R> {
    pub(crate) fn to_lits(self) -> Vec<Lit<'a, R>> {
        match self {
            ConflReason::Rule(cell) => cell
                .nbhd
                .iter()
                .chain(once(&Some(cell)))
                .chain(once(&cell.succ))
                .filter_map(|&c| c.and_then(|c| c.state.get().map(|state| Lit { cell: c, state })))
                .collect(),
            ConflReason::Sym(cell, sym) => vec![
                Lit {
                    cell,
                    state: cell.state.get().unwrap(),
                },
                Lit {
                    cell: sym,
                    state: sym.state.get().unwrap(),
                },
            ],
            _ => Vec::new(),
        }
    }
}
