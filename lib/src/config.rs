//! World configuration.

use crate::{
    cells::State,
    rules::{Life, NtLife},
    search::Search,
    world::World,
};
use std::{
    cmp::Ordering,
    fmt::{Debug, Error, Formatter},
    str::FromStr,
};

#[cfg(feature = "stdweb")]
use serde::{Deserialize, Serialize};

/// Transformations (rotations and reflections) after the last generation.
///
/// After the last generation, the pattern will return to
/// the first generation, applying this transformation first,
/// and then the translation defined by `dx` and `dy`.
///
/// 8 different values corresponds to 8 elements of the dihedral group
/// _D_<sub>8</sub>.
///
/// `Id` is the identity transformation.
///
/// `R` means rotations around the center of the world.
/// The number after it is the counterclockwise rotation angle in degrees.
///
/// `F` means reflections (flips).
/// The symbol after it is the axis of reflection.
///
/// Some of the transformations are only valid when the world is square.
#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(feature = "stdweb", derive(Serialize, Deserialize))]
pub enum Transform {
    /// `Id`.
    ///
    /// Identity transformation.
    Id,
    /// `R90`.
    ///
    /// 90° rotation counterclockwise.
    Rotate90,
    /// `R180`.
    ///
    /// 180° rotation counterclockwise.
    Rotate180,
    /// `R270`.
    ///
    /// 270° rotation counterclockwise.
    Rotate270,
    /// `F-`.
    ///
    /// Reflection across the middle row.
    FlipRow,
    /// `F|`.
    ///
    /// Reflection across the middle column.
    FlipCol,
    /// `F\`.
    ///
    /// Reflection across the diagonal.
    FlipDiag,
    /// `F/`.
    ///
    /// Reflection across the antidiagonal.
    FlipAntidiag,
}

impl FromStr for Transform {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "Id" => Ok(Transform::Id),
            "R90" => Ok(Transform::Rotate90),
            "R180" => Ok(Transform::Rotate180),
            "R270" => Ok(Transform::Rotate270),
            "F-" => Ok(Transform::FlipRow),
            "F|" => Ok(Transform::FlipCol),
            "F\\" => Ok(Transform::FlipDiag),
            "F/" => Ok(Transform::FlipAntidiag),
            _ => Err(String::from("invalid Transform")),
        }
    }
}

impl Debug for Transform {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        let s = match self {
            Transform::Id => "Id",
            Transform::Rotate90 => "R90",
            Transform::Rotate180 => "R180",
            Transform::Rotate270 => "R270",
            Transform::FlipRow => "F-",
            Transform::FlipCol => "F|",
            Transform::FlipDiag => "F\\",
            Transform::FlipAntidiag => "F/",
        };
        write!(f, "{}", s)?;
        Ok(())
    }
}

/// The default transformation is the `Id`.
impl Default for Transform {
    fn default() -> Self {
        Transform::Id
    }
}

impl Transform {
    /// Whether the transformation requires the world to be square.
    ///
    /// Returns `true` for `R90`, `R270`, `F\` and `F/`.
    pub fn square_world(self) -> bool {
        match self {
            Transform::Rotate90
            | Transform::Rotate270
            | Transform::FlipDiag
            | Transform::FlipAntidiag => true,
            _ => false,
        }
    }
}

/// Symmetries of the pattern.
///
/// 10 different values corresponds to 10 subgroups of the dihedral group
/// _D_<sub>8</sub>.
///
/// The notation is stolen from Oscar Cunningham's
/// [Logic Life Search](https://github.com/OscarCunningham/logic-life-search).
///
/// Some of the symmetries are only valid when the world is square.
#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(feature = "stdweb", derive(Serialize, Deserialize))]
pub enum Symmetry {
    /// `C1`.
    ///
    /// No symmetry at all.
    C1,
    /// `C2`.
    ///
    /// Symmetry under 180° rotation.
    C2,
    /// `C4`.
    ///
    /// Symmetry under 90° rotation.
    C4,
    /// `D2-`.
    ///
    /// Symmetry under reflection across the middle row.
    D2Row,
    /// `D2|`.
    ///
    /// Symmetry under reflection across the middle column.
    D2Col,
    /// `D2\`.
    ///
    /// Symmetry under reflection across the diagonal.
    D2Diag,
    /// `D2/`.
    ///
    /// Symmetry under reflection across the antidiagonal.
    D2Antidiag,
    /// `D4+`.
    ///
    /// Symmetry under reflections across the middle row
    /// and the middle column.
    D4Ortho,
    /// `D4X`.
    ///
    /// Symmetry under reflections across the diagonal
    /// and the antidiagonal.
    D4Diag,
    /// `D8`.
    ///
    /// Symmetry under all 8 transformations.
    D8,
}

impl FromStr for Symmetry {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "C1" => Ok(Symmetry::C1),
            "C2" => Ok(Symmetry::C2),
            "C4" => Ok(Symmetry::C4),
            "D2-" => Ok(Symmetry::D2Row),
            "D2|" => Ok(Symmetry::D2Col),
            "D2\\" => Ok(Symmetry::D2Diag),
            "D2/" => Ok(Symmetry::D2Antidiag),
            "D4+" => Ok(Symmetry::D4Ortho),
            "D4X" => Ok(Symmetry::D4Diag),
            "D8" => Ok(Symmetry::D8),
            _ => Err(String::from("invalid symmetry")),
        }
    }
}

impl Debug for Symmetry {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        let s = match self {
            Symmetry::C1 => "C1",
            Symmetry::C2 => "C2",
            Symmetry::C4 => "C4",
            Symmetry::D2Row => "D2-",
            Symmetry::D2Col => "D2|",
            Symmetry::D2Diag => "D2\\",
            Symmetry::D2Antidiag => "D2/",
            Symmetry::D4Ortho => "D4+",
            Symmetry::D4Diag => "D4X",
            Symmetry::D8 => "D8",
        };
        write!(f, "{}", s)?;
        Ok(())
    }
}

/// The default symmetry is the `C1`.
impl Default for Symmetry {
    fn default() -> Self {
        Symmetry::C1
    }
}

impl Symmetry {
    /// Whether the transformation requires the world to be square.
    ///
    /// Returns `true` for `C4`, `D2\`, `D2/`, `D4X` and `D8`.
    pub fn square_world(self) -> bool {
        match self {
            Symmetry::C4
            | Symmetry::D2Diag
            | Symmetry::D2Antidiag
            | Symmetry::D4Diag
            | Symmetry::D8 => true,
            _ => false,
        }
    }
}

/// The order to find a new unknown cell.
///
/// It will always search all generations of a cell first,
/// and the go to another cell.
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "stdweb", derive(Serialize, Deserialize))]
pub enum SearchOrder {
    /// Searches all cells of a row first,
    /// and the go to the next row.
    ///
    /// ```plaintext
    /// 123
    /// 456
    /// 789
    /// ```
    RowFirst,

    /// Searches all cells of a column first,
    /// and the go to the next column.
    ///
    /// ```plaintext
    /// 147
    /// 258
    /// 369
    /// ```
    ColumnFirst,
}

/// How to choose a state for an unknown cell.
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "stdweb", derive(Serialize, Deserialize))]
pub enum NewState {
    /// Chooses the given state.
    Choose(State),
    /// Random. The probability of either state is 1/2.
    Random,
}

impl Default for NewState {
    fn default() -> Self {
        NewState::Choose(State::Alive)
    }
}

/// World configuration.
///
/// The world will be generated from this configuration.
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "stdweb", derive(Serialize, Deserialize))]
pub struct Config {
    /// Width.
    pub width: isize,

    /// Height.
    pub height: isize,

    /// Period.
    pub period: isize,

    /// Horizontal translation.
    pub dx: isize,

    /// Vertical translation.
    pub dy: isize,

    /// Transformations (rotations and reflections) after the last generation.
    ///
    /// After the last generation, the pattern will return to
    /// the first generation, applying this transformation first,
    /// and then the translation defined by `dx` and `dy`.
    pub transform: Transform,

    /// Symmetries of the pattern.
    pub symmetry: Symmetry,

    /// The order to find a new unknown cell.
    ///
    /// It will always search all generations of a cell first,
    /// and then go to another cell.
    ///
    /// `None` means that it will automatically choose a search order
    /// according to the width and height of the world.
    pub search_order: Option<SearchOrder>,

    /// How to choose a state for an unknown cell.
    pub new_state: NewState,

    /// The number of living cells in generation 0 must not exceed
    /// this number.
    ///
    /// `None` means that there is no limit for the cell count.
    pub max_cell_count: Option<usize>,

    /// Whether to force the first row/column to be nonempty.
    ///
    /// Here 'front' means the first row or column to search,
    /// according to the search order.
    pub non_empty_front: bool,

    /// The rule string of the cellular automaton.
    pub rule_string: String,
}

impl Config {
    /// Sets up a new configuration with given size.
    pub fn new(width: isize, height: isize, period: isize) -> Self {
        Config {
            width,
            height,
            period,
            ..Config::default()
        }
    }

    /// Sets the translations `(dx, dy)`.
    pub fn set_translate(mut self, dx: isize, dy: isize) -> Self {
        self.dx = dx;
        self.dy = dy;
        self
    }

    /// Sets the transformation.
    pub fn set_transform(mut self, transform: Transform) -> Self {
        self.transform = transform;
        self
    }

    /// Sets the symmetry.
    pub fn set_symmetry(mut self, symmetry: Symmetry) -> Self {
        self.symmetry = symmetry;
        self
    }

    /// Sets the search order.
    pub fn set_search_order(mut self, search_order: Option<SearchOrder>) -> Self {
        self.search_order = search_order;
        self
    }

    /// Sets how to choose a state for an unknown cell.
    pub fn set_new_state(mut self, new_state: NewState) -> Self {
        self.new_state = new_state;
        self
    }

    /// Sets the maximal number of living cells in generation 0.
    pub fn set_max_cell_count(mut self, max_cell_count: Option<usize>) -> Self {
        self.max_cell_count = max_cell_count;
        self
    }

    /// Sets whether to force the first row/column to be nonempty.
    pub fn set_non_empty_front(mut self, non_empty_front: bool) -> Self {
        self.non_empty_front = non_empty_front;
        self
    }

    /// Sets the rule string.
    pub fn set_rule_string(mut self, rule_string: String) -> Self {
        self.rule_string = rule_string;
        self
    }

    /// Automatically determines the search order if `search_order` is `None`.
    pub(crate) fn auto_search_order(&self) -> SearchOrder {
        self.search_order.unwrap_or_else(|| {
            let (width, height) = match self.symmetry {
                Symmetry::D2Row => (self.width, (self.height + 1) / 2),
                Symmetry::D2Col => ((self.width + 1) / 2, self.height),
                _ => (self.width, self.height),
            };
            match width.cmp(&height) {
                Ordering::Greater => SearchOrder::ColumnFirst,
                Ordering::Less => SearchOrder::RowFirst,
                Ordering::Equal => {
                    if self.dx.abs() >= self.dy.abs() {
                        SearchOrder::ColumnFirst
                    } else {
                        SearchOrder::RowFirst
                    }
                }
            }
        })
    }

    /// Creates a new world from the configuration.
    /// Returns an error if the rule string is invalid.
    ///
    /// In rules that contain `B0`, cells outside the search range are
    /// considered `Dead` in even generations, `Alive` in odd generations.
    /// In other rules, all cells outside the search range are `Dead`.
    ///
    /// After the last generation, the pattern will return to
    /// the first generation, applying the transformation first,
    /// and then the translation defined by `dx` and `dy`.
    pub fn set_world(&self) -> Result<Box<dyn Search>, String> {
        if let Ok(rule) = Life::parse_rule(&self.rule_string) {
            Ok(Box::new(World::new(&self, rule)))
        } else {
            let rule = NtLife::parse_rule(&self.rule_string)?;
            Ok(Box::new(World::new(&self, rule)))
        }
    }
}

impl Default for Config {
    fn default() -> Self {
        Config {
            width: 16,
            height: 16,
            period: 1,
            dx: 0,
            dy: 0,
            transform: Transform::Id,
            symmetry: Symmetry::C1,
            search_order: None,
            new_state: NewState::Choose(State::Alive),
            max_cell_count: None,
            non_empty_front: true,
            rule_string: String::from("B3/S23"),
        }
    }
}
