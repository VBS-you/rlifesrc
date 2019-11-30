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
    pub(crate) fn to_lits(self, cell: Option<CellRef<'a, R>>) -> Vec<Lit<'a, R>> {
        match self {
            SetReason::Rule(cell1) => cell1
                .nbhd
                .iter()
                .chain(once(&Some(cell1)))
                .chain(once(&cell1.succ))
                .filter_map(|&c| match c {
                    Some(c) if Some(c) != cell => c.state.get().map(|state| Lit { cell: c, state }),
                    _ => None,
                })
                .collect(),
            SetReason::Sym(cell1, sym) => once(&Some(cell1))
                .chain(once(&Some(sym)))
                .filter_map(|&c| match c {
                    Some(c) if Some(c) != cell => c.state.get().map(|state| Lit { cell: c, state }),
                    _ => None,
                })
                .collect(),
            _ => Vec::new(),
        }
    }
}

impl<'a, R: Rule> ConflReason<'a, R> {
    pub(crate) fn to_lits(self, cell: Option<CellRef<'a, R>>) -> Vec<Lit<'a, R>> {
        match self {
            ConflReason::Rule(cell1) => cell1
                .nbhd
                .iter()
                .chain(once(&Some(cell1)))
                .chain(once(&cell1.succ))
                .filter_map(|&c| match c {
                    Some(c) if Some(c) != cell => c.state.get().map(|state| Lit { cell: c, state }),
                    _ => None,
                })
                .collect(),
            ConflReason::Sym(cell1, sym) => once(&Some(cell1))
                .chain(once(&Some(sym)))
                .filter_map(|&c| match c {
                    Some(c) if Some(c) != cell => c.state.get().map(|state| Lit { cell: c, state }),
                    _ => None,
                })
                .collect(),
            _ => Vec::new(),
        }
    }
}
