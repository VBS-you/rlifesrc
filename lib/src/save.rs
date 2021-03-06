#![cfg(feature = "serialize")]
//! Saves the world.

use crate::{
    cells::{Coord, State},
    config::Config,
    error::Error,
    rules::{Life, LifeGen, NtLife, NtLifeGen, Rule},
    search::{Reason, SetCell},
    traits::Search,
    world::World,
};
use serde::{Deserialize, Serialize};

/// A representation of `SetCell` which can be easily serialized.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct SetCellSer {
    /// The coordinates of the set cell.
    coord: Coord,

    /// The state.
    state: State,

    /// The reason for setting a cell.
    reason: Reason,
}

impl<'a, R: Rule> SetCell<'a, R> {
    fn ser(&self) -> SetCellSer {
        SetCellSer {
            coord: self.cell.coord,
            state: self.cell.state.get().unwrap(),
            reason: self.reason,
        }
    }
}

/// A representation of the world which can be easily serialized.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorldSer {
    /// World configuration.
    config: Config,

    /// Number of conflicts during the search.
    conflicts: u64,

    /// A stack to records the cells whose values are set during the search.
    ///
    /// The cells in this table always have known states.
    ///
    /// It is used in the backtracking.
    set_stack: Vec<SetCellSer>,

    /// The position in the `set_stack` of the next cell to be examined.
    ///
    /// See `proceed` for details.
    check_index: usize,

    /// The position in the `search_list` of the last decided cell.
    search_index: usize,
}

impl WorldSer {
    /// Restores the world from the `WorldSer`, with the given rule.
    fn world_with_rule<'a, R: Rule>(&self, rule: R) -> Result<World<'a, R>, Error> {
        let mut world = World::new(&self.config, rule);
        for &SetCellSer {
            coord,
            state,
            reason,
        } in self.set_stack.iter()
        {
            let cell = world.find_cell(coord).ok_or(Error::SetCellError(coord))?;
            if let Some(old_state) = cell.state.get() {
                if old_state != state {
                    return Err(Error::SetCellError(coord));
                }
            } else {
                world.set_cell(cell, state, reason);
            }
        }
        world.conflicts = self.conflicts;
        world.check_index = self.check_index;
        world.search_index = self.search_index;
        Ok(world)
    }

    /// Restores the world from the `WorldSer`.
    pub fn world(&self) -> Result<Box<dyn Search>, Error> {
        if let Ok(rule) = self.config.rule_string.parse::<Life>() {
            let world = self.world_with_rule(rule)?;
            Ok(Box::new(world))
        } else if let Ok(rule) = self.config.rule_string.parse::<NtLife>() {
            let world = self.world_with_rule(rule)?;
            Ok(Box::new(world))
        } else if let Ok(rule) = self.config.rule_string.parse::<LifeGen>() {
            if rule.gen() > 2 {
                let world = self.world_with_rule(rule)?;
                Ok(Box::new(world))
            } else {
                let rule = rule.non_gen();
                let world = self.world_with_rule(rule)?;
                Ok(Box::new(world))
            }
        } else {
            let rule = self.config.rule_string.parse::<NtLifeGen>()?;
            if rule.gen() > 2 {
                let world = self.world_with_rule(rule)?;
                Ok(Box::new(world))
            } else {
                let rule = rule.non_gen();
                let world = self.world_with_rule(rule)?;
                Ok(Box::new(world))
            }
        }
    }
}

impl<'a, R: Rule> World<'a, R> {
    /// Saves the world as a `WorldSer`.
    pub fn ser(&self) -> WorldSer {
        WorldSer {
            config: self.config.clone(),
            conflicts: self.conflicts,
            set_stack: self.set_stack.iter().map(|s| s.ser()).collect(),
            check_index: self.check_index,
            search_index: self.search_index,
        }
    }
}
