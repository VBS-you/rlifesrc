//! Cells in the cellular automaton.

use crate::rules::Rule;
use rand::{
    distributions::{Distribution, Standard},
    Rng,
};
use std::{
    cell::Cell,
    fmt::{Debug, Error, Formatter},
    ops::Not,
};
pub use State::{Alive, Dead};

#[cfg(feature = "stdweb")]
use serde::{Deserialize, Serialize};

/// Possible states of a known cell.
///
/// During the search, the state of a cell is represented by `Option<State>`,
/// where `None` means that the state of the cell is unknown.
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "stdweb", derive(Serialize, Deserialize))]
pub enum State {
    Alive = 0b01,
    Dead = 0b10,
}

/// Flips the state.
impl Not for State {
    type Output = State;

    fn not(self) -> Self::Output {
        match self {
            Alive => Dead,
            Dead => Alive,
        }
    }
}

/// Randomly chooses between `Alive` and `Dead`.
///
/// The probability of either state is 1/2.
impl Distribution<State> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> State {
        match rng.gen_range(0, 2) {
            0 => Dead,
            _ => Alive,
        }
    }
}

/// A cell in the cellular automaton.
///
/// The name `LifeCell` is chosen to avoid ambiguity with
/// [`std::cell::Cell`](https://doc.rust-lang.org/std/cell/struct.Cell.html).
pub struct LifeCell<'a, R: Rule> {
    /// The background state of a cell.
    ///
    /// For rules without `B0`, it is always dead.
    /// For rules with `B0`, it is dead on even generations,
    /// alive on odd generations.
    pub(crate) background: State,

    /// The state of the cell.
    ///
    /// `None` means that the state of the cell is unknown.
    pub(crate) state: Cell<Option<State>>,

    /// The “neighborhood descriptors” of the cell.
    ///
    /// It describes the states of the cell itself, its neighbors,
    /// and its successor.
    pub(crate) desc: Cell<R::Desc>,

    /// The predecessor of the cell.
    ///
    /// The cell in the last generation at the same position.
    pub(crate) pred: Option<&'a LifeCell<'a, R>>,
    /// The successor of the cell.
    ///
    /// The cell in the next generation at the same position.
    pub(crate) succ: Option<&'a LifeCell<'a, R>>,
    /// The eight cells in the neighborhood.
    pub(crate) nbhd: [Option<&'a LifeCell<'a, R>>; 8],
    /// The cells in the same generation that must has the same state
    /// with this cell because of the symmetry.
    pub(crate) sym: Vec<&'a LifeCell<'a, R>>,

    /// Whether the cell is in the first generation.
    pub(crate) is_gen0: bool,
    /// Whether the cell is on the first row or column.
    ///
    /// Here the choice of row or column depends on the search order.
    pub(crate) is_front: bool,
}

impl<'a, R: Rule> LifeCell<'a, R> {
    /// Generates a new cell with state `state`, such that its neighborhood
    /// descriptor says that all neighboring cells also have the same state.
    ///
    /// `first_gen` and `first_col` are set to `false`.
    pub(crate) fn new(background: State, b0: bool) -> Self {
        let succ_state = if b0 { !background } else { background };
        LifeCell {
            background,
            state: Cell::new(Some(background)),
            desc: Cell::new(R::new_desc(background, succ_state)),
            pred: Default::default(),
            succ: Default::default(),
            nbhd: Default::default(),
            sym: Default::default(),
            is_gen0: false,
            is_front: false,
        }
    }

    pub(crate) fn update_desc(&self, old_state: Option<State>, state: Option<State>) {
        R::update_desc(self, old_state, state);
    }
}

impl<'a, R: Rule<Desc = D>, D: Copy + Debug> Debug for LifeCell<'a, R> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(
            f,
            "LifeCell {{ state: {:?}, desc: {:?} }}",
            self.state.get(),
            self.desc.get()
        )
    }
}