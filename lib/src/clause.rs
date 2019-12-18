//! Reasons and clauses.

use crate::cells::CellRef;

// use std::ops::Not;

// /// A `Lit` says that some `cell` has some `state`.
// #[derive(Clone, Copy, PartialEq, Eq)]
// pub(crate) struct Lit<'a> {
//     pub(crate) cell: CellRef<'a>,
//     pub(crate) state: State,
// }

// impl<'a> Not for Lit<'a> {
//     type Output = Self;

//     fn not(self) -> Self::Output {
//         Lit {
//             cell: self.cell,
//             state: !self.state,
//         }
//     }
// }

// #[derive(Clone)]
// pub(crate) struct Clause<'a> {
//     pub(crate) lits: Vec<Lit<'a>>,
// }

/// Reasons for setting a cell.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SetReason<'a> {
    /// Assumed when nothing can be deduced.
    ///
    /// The number is its position in the `search_list` of the world.
    Assume(usize),

    /// Deduced during the initialization.
    Init,

    /// Deduced from the rule when constitifying another cell.
    Rule(CellRef<'a>),

    /// Deduced from symmetry.
    Sym(CellRef<'a>),

    /// Deduced from a learnt clause.
    Clause(Vec<CellRef<'a>>),

    /// Deduced from conflicts.
    Conflict,
}

impl<'a> SetReason<'a> {
    pub(crate) fn cells(self, cell: CellRef<'a>) -> Vec<CellRef<'a>> {
        match self {
            SetReason::Rule(cell0) => {
                let desc = cell0.desc.get();
                let mut cells = Vec::with_capacity(10);
                if desc.0 & 0b11 != 0 && cell != cell0 {
                    cells.push(cell0);
                }
                if desc.0 & 0b11 << 2 != 0 {
                    if let Some(succ) = cell0.succ {
                        if cell != succ {
                            cells.push(succ);
                        }
                    }
                }
                for i in 0..8 {
                    if desc.0 & 0x0101 << i << 4 != 0 {
                        if let Some(neigh) = cell0.nbhd[i] {
                            if cell != neigh {
                                cells.push(neigh);
                            }
                        }
                    }
                }
                cells
            }
            SetReason::Sym(sym) => vec![sym],
            SetReason::Clause(clause) => clause,
            _ => Vec::new(),
        }
    }
}

/// Reasons for a conflict.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ConflReason<'a> {
    /// Deduced from the rule when constitifying another cell.
    Rule(CellRef<'a>),

    /// Deduced from symmetry.
    Sym(CellRef<'a>, CellRef<'a>),

    /// Deduced from conditions about cell counts.
    CellCount,
}

impl<'a> ConflReason<'a> {
    pub(crate) fn cells(self) -> Vec<CellRef<'a>> {
        match self {
            ConflReason::Rule(cell) => {
                let desc = cell.desc.get();
                let mut cells = Vec::with_capacity(10);
                if desc.0 & 0b11 != 0 {
                    cells.push(cell);
                }
                if desc.0 & 0b11 << 2 != 0 {
                    if let Some(succ) = cell.succ {
                        cells.push(succ);
                    }
                }
                for i in 0..8 {
                    if desc.0 & 0x0101 << i << 4 != 0 {
                        if let Some(neigh) = cell.nbhd[i] {
                            cells.push(neigh);
                        }
                    }
                }
                cells
            }
            ConflReason::Sym(cell, sym) => vec![cell, sym],
            _ => Vec::new(),
        }
    }
}
