use super::*;
use std::fmt;

impl fmt::Display for TnurccConnection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TnurccConnection::LeftAcw => write!(f, "Anti-clockwise Left"),
            TnurccConnection::RightAcw => write!(f, "Anti-clockwise Right"),
            TnurccConnection::LeftCw => write!(f, "Clockwise Left"),
            TnurccConnection::RightCw => write!(f, "Clockwise Right"),
        }
    }
}