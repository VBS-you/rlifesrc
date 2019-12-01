//! This mod is not yet used.

use crate::cells::{CellRef, State};
use std::ops::Not;

/// A `Lit` says that some `cell` has some `state`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct Lit<'a> {
    pub(crate) cell: CellRef<'a>,
    pub(crate) state: State,
}

impl<'a> Not for Lit<'a> {
    type Output = Self;

    fn not(self) -> Self::Output {
        Lit {
            cell: self.cell,
            state: !self.state,
        }
    }
}

#[derive(Clone)]
pub(crate) struct Clause<'a> {
    pub(crate) lits: Vec<Lit<'a>>,
}
