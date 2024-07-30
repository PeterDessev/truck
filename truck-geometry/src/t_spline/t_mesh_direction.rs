use super::*;
use std::fmt;

impl TMeshDirection {
    /// Returns an iterable object which rotates clockwise starting from UP.
    pub fn iter() -> impl Iterator<Item = TMeshDirection> {
        [
            TMeshDirection::UP,
            TMeshDirection::RIGHT,
            TMeshDirection::DOWN,
            TMeshDirection::LEFT,
        ]
        .iter()
        .copied()
    }

    /// Rotates `self` a quarter of a rotation clockwise.
    pub fn clockwise(self) -> Self {
        match self {
            TMeshDirection::UP => TMeshDirection::RIGHT,
            TMeshDirection::RIGHT => TMeshDirection::DOWN,
            TMeshDirection::DOWN => TMeshDirection::LEFT,
            TMeshDirection::LEFT => TMeshDirection::UP,
        }
    }

    /// Rotates `self` a quarter of a turn anti-clockwise.
    pub fn anti_clockwise(self) -> Self {
        match self {
            TMeshDirection::UP => TMeshDirection::LEFT,
            TMeshDirection::LEFT => TMeshDirection::DOWN,
            TMeshDirection::DOWN => TMeshDirection::RIGHT,
            TMeshDirection::RIGHT => TMeshDirection::UP,
        }
    }

    /// Flips `self`, rotating it half a turn.
    pub fn flip(self) -> Self {
        match self {
            TMeshDirection::UP => TMeshDirection::DOWN,
            TMeshDirection::DOWN => TMeshDirection::UP,
            TMeshDirection::LEFT => TMeshDirection::RIGHT,
            TMeshDirection::RIGHT => TMeshDirection::LEFT,
        }
    }

    /// Returns true if the direction is UP or DOWN
    pub fn virtical(self) -> bool {
        match self {
            TMeshDirection::UP => true,
            TMeshDirection::DOWN => true,
            TMeshDirection::LEFT => false,
            TMeshDirection::RIGHT => false,
        }
    }

    /// Returns true if the direction is RIGHT or LEFT
    pub fn horizontal(self) -> bool {
        match self {
            TMeshDirection::UP => false,
            TMeshDirection::DOWN => false,
            TMeshDirection::LEFT => true,
            TMeshDirection::RIGHT => true,
        }
    }

    /// Returns true if a knot interval in the direction is a positive delta.
    pub fn knot_delta_positive(self) -> bool {
        match self {
            TMeshDirection::UP => true,
            TMeshDirection::DOWN => false,
            TMeshDirection::LEFT => false,
            TMeshDirection::RIGHT => true,
        }
    }

    /// Returns true if a knot interval in the direction is a negative delta.
    pub fn knot_delta_negative(self) -> bool {
        match self {
            TMeshDirection::UP => false,
            TMeshDirection::DOWN => true,
            TMeshDirection::LEFT => true,
            TMeshDirection::RIGHT => false,
        }
    }
}

impl fmt::Display for TMeshDirection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let dir_string = match self {
            TMeshDirection::UP => "up",
            TMeshDirection::DOWN => "down",
            TMeshDirection::LEFT => "left",
            TMeshDirection::RIGHT => "right",
        };

        write!(f, "{}", dir_string)
    }
}
