/// Display rotation.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum Rotation {
    /// No rotation.
    Deg0,
    /// 90° clockwise rotation.
    Deg90,
    /// 180° clockwise rotation.
    Deg180,
    /// 270° clockwise rotation.
    Deg270,
}

impl Rotation {
    /// Returns the rotation in degrees.
    pub const fn degree(self) -> i32 {
        match self {
            Self::Deg0 => 0,
            Self::Deg90 => 90,
            Self::Deg180 => 180,
            Self::Deg270 => 270,
        }
    }

    /// Converts an angle into a rotation.
    ///
    /// Returns an error if the angle isn't an integer multiple of 90°.
    pub const fn try_from_degree(mut angle: i32) -> Result<Self, InvalidAngleError> {
        if angle < 0 || angle > 270 {
            angle = angle.rem_euclid(360)
        }

        Ok(match angle {
            0 => Self::Deg0,
            90 => Self::Deg90,
            180 => Self::Deg180,
            270 => Self::Deg270,
            _ => return Err(InvalidAngleError),
        })
    }

    /// Rotates one rotation by another rotation.
    #[must_use]
    pub const fn rotate(self, other: Rotation) -> Self {
        match Self::try_from_degree(self.degree() + other.degree()) {
            Ok(r) => r,
            Err(_) => unreachable!(),
        }
    }

    /// Returns `true` if the rotation is horizontal (0° or 180°).
    pub const fn is_horizontal(self) -> bool {
        matches!(self, Self::Deg0 | Self::Deg180)
    }

    /// Returns `true` if the rotation is vertical (90° or 270°).
    pub const fn is_vertical(self) -> bool {
        matches!(self, Self::Deg90 | Self::Deg270)
    }
}

/// Invalid angle error.
///
/// The error type returned by [`Rotation::try_from_degree`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct InvalidAngleError;

/// Display orientation.
///
/// A display orientation describes how the display content is oriented relative
/// to the default orientation of the display.
///
/// # Examples
///
/// ```
/// use mipidsi::options::{Orientation, Rotation};
///
/// // Rotate display content by 90 degree clockwise.
/// let rotated = Orientation::new().rotate(Rotation::Deg90);
///
/// // Flip display content horizontally.
/// let flipped = Orientation::new().flip_horizontal();
/// ```
///
/// Multiple transformations can be combined to build more complex orientations:
///
/// ```
/// use mipidsi::options::{Orientation, Rotation};
///
/// let orientation = Orientation::new().rotate(Rotation::Deg270).flip_vertical();
///
/// // Note that the order of operations is important:
/// assert_ne!(orientation, Orientation::new().flip_vertical().rotate(Rotation::Deg270));
/// assert_eq!(orientation, Orientation::new().flip_vertical().rotate(Rotation::Deg90));
/// ```
///
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct Orientation {
    /// Rotation.
    pub rotation: Rotation,
    /// Mirrored.
    pub mirrored: bool,
}

impl Orientation {
    /// Creates a default orientation.
    pub const fn new() -> Self {
        Self {
            rotation: Rotation::Deg0,
            mirrored: false,
        }
    }

    /// Rotates the orientation.
    #[must_use]
    pub const fn rotate(self, rotation: Rotation) -> Self {
        Self {
            rotation: self.rotation.rotate(rotation),
            mirrored: self.mirrored,
        }
    }

    /// Flips the orientation across the horizontal display axis.
    #[must_use]
    const fn flip_horizontal_absolute(self) -> Self {
        Self {
            rotation: self.rotation,
            mirrored: !self.mirrored,
        }
    }

    /// Flips the orientation across the vertical display axis.
    #[must_use]
    const fn flip_vertical_absolute(self) -> Self {
        Self {
            rotation: self.rotation.rotate(Rotation::Deg180),
            mirrored: !self.mirrored,
        }
    }

    /// Flips the orientation across the horizontal axis.
    #[must_use]
    pub const fn flip_horizontal(self) -> Self {
        if self.rotation.is_vertical() {
            self.flip_vertical_absolute()
        } else {
            self.flip_horizontal_absolute()
        }
    }

    /// Flips the orientation across the vertical axis.
    #[must_use]
    pub const fn flip_vertical(self) -> Self {
        if self.rotation.is_vertical() {
            self.flip_horizontal_absolute()
        } else {
            self.flip_vertical_absolute()
        }
    }
}

impl Default for Orientation {
    fn default() -> Self {
        Self::new()
    }
}

/// Memory mapping.
///
/// A memory mapping describes how a framebuffer is mapped to the physical
/// row and columns of a display.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct MemoryMapping {
    /// Rows and columns are swapped.
    pub swap_rows_and_columns: bool,

    /// Rows are reversed.
    pub reverse_rows: bool,
    /// Columns are reversed.
    pub reverse_columns: bool,
}

impl MemoryMapping {
    /// `const` variant of `From<Orientation>` impl.
    pub const fn from_orientation(orientation: Orientation) -> Self {
        let (reverse_rows, reverse_columns) = match orientation.rotation {
            Rotation::Deg0 => (false, false),
            Rotation::Deg90 => (false, true),
            Rotation::Deg180 => (true, true),
            Rotation::Deg270 => (true, false),
        };

        Self {
            reverse_rows,
            reverse_columns: reverse_columns ^ orientation.mirrored,
            swap_rows_and_columns: orientation.rotation.is_vertical(),
        }
    }
}

impl From<Orientation> for MemoryMapping {
    fn from(orientation: Orientation) -> Self {
        Self::from_orientation(orientation)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn try_from_degree() {
        let mut expected = [
            Rotation::Deg0,
            Rotation::Deg90,
            Rotation::Deg180,
            Rotation::Deg270,
        ]
        .iter()
        .copied()
        .cycle();

        for angle in (-720..=720).step_by(90) {
            assert_eq!(
                Rotation::try_from_degree(angle).unwrap(),
                expected.next().unwrap(),
                "{angle}"
            );
        }
    }

    #[test]
    fn try_from_degree_error() {
        assert_eq!(Rotation::try_from_degree(1), Err(InvalidAngleError));
        assert_eq!(Rotation::try_from_degree(-1), Err(InvalidAngleError));
        assert_eq!(Rotation::try_from_degree(i32::MIN), Err(InvalidAngleError));
        assert_eq!(Rotation::try_from_degree(i32::MAX), Err(InvalidAngleError));
    }

    /// Abbreviated constructor for orientations.
    const fn orientation(rotation: Rotation, mirrored: bool) -> Orientation {
        Orientation { rotation, mirrored }
    }

    #[test]
    fn flip_horizontal() {
        use Rotation::*;

        for ((rotation, mirrored), (expected_rotation, expected_mirrored)) in [
            ((Deg0, false), (Deg0, true)),
            ((Deg90, false), (Deg270, true)),
            ((Deg180, false), (Deg180, true)),
            ((Deg270, false), (Deg90, true)),
            ((Deg0, true), (Deg0, false)),
            ((Deg90, true), (Deg270, false)),
            ((Deg180, true), (Deg180, false)),
            ((Deg270, true), (Deg90, false)),
        ]
        .iter()
        .copied()
        {
            assert_eq!(
                orientation(rotation, mirrored).flip_horizontal(),
                orientation(expected_rotation, expected_mirrored)
            );
        }
    }

    #[test]
    fn flip_vertical() {
        use Rotation::*;

        for ((rotation, mirrored), (expected_rotation, expected_mirrored)) in [
            ((Deg0, false), (Deg180, true)),
            ((Deg90, false), (Deg90, true)),
            ((Deg180, false), (Deg0, true)),
            ((Deg270, false), (Deg270, true)),
            ((Deg0, true), (Deg180, false)),
            ((Deg90, true), (Deg90, false)),
            ((Deg180, true), (Deg0, false)),
            ((Deg270, true), (Deg270, false)),
        ]
        .iter()
        .copied()
        {
            assert_eq!(
                orientation(rotation, mirrored).flip_vertical(),
                orientation(expected_rotation, expected_mirrored)
            );
        }
    }

    fn draw_memory_mapping(order: MemoryMapping) -> [[u8; 3]; 3] {
        let mut buffer = [[0u8; 3]; 3];

        let (max_x, max_y) = if order.swap_rows_and_columns {
            (1, 2)
        } else {
            (2, 1)
        };

        let mut i = 1..;
        for y in 0..2 {
            for x in 0..3 {
                let (x, y) = if order.swap_rows_and_columns {
                    (y, x)
                } else {
                    (x, y)
                };
                let x = if order.reverse_columns { max_x - x } else { x };
                let y = if order.reverse_rows { max_y - y } else { y };

                buffer[y as usize][x as usize] = i.next().unwrap();
            }
        }

        buffer
    }

    #[test]
    fn test_draw_memory_mapping() {
        assert_eq!(
            &draw_memory_mapping(MemoryMapping {
                reverse_rows: false,
                reverse_columns: false,
                swap_rows_and_columns: false,
            }),
            &[
                [1, 2, 3], //
                [4, 5, 6], //
                [0, 0, 0], //
            ]
        );

        assert_eq!(
            &draw_memory_mapping(MemoryMapping {
                reverse_rows: true,
                reverse_columns: false,
                swap_rows_and_columns: false,
            }),
            &[
                [4, 5, 6], //
                [1, 2, 3], //
                [0, 0, 0], //
            ]
        );

        assert_eq!(
            &draw_memory_mapping(MemoryMapping {
                reverse_rows: false,
                reverse_columns: true,
                swap_rows_and_columns: false,
            }),
            &[
                [3, 2, 1], //
                [6, 5, 4], //
                [0, 0, 0], //
            ]
        );

        assert_eq!(
            &draw_memory_mapping(MemoryMapping {
                reverse_rows: true,
                reverse_columns: true,
                swap_rows_and_columns: false,
            }),
            &[
                [6, 5, 4], //
                [3, 2, 1], //
                [0, 0, 0], //
            ]
        );

        assert_eq!(
            &draw_memory_mapping(MemoryMapping {
                reverse_rows: false,
                reverse_columns: false,
                swap_rows_and_columns: true,
            }),
            &[
                [1, 4, 0], //
                [2, 5, 0], //
                [3, 6, 0], //
            ]
        );

        assert_eq!(
            &draw_memory_mapping(MemoryMapping {
                reverse_rows: true,
                reverse_columns: false,
                swap_rows_and_columns: true,
            }),
            &[
                [3, 6, 0], //
                [2, 5, 0], //
                [1, 4, 0], //
            ]
        );

        assert_eq!(
            &draw_memory_mapping(MemoryMapping {
                reverse_rows: false,
                reverse_columns: true,
                swap_rows_and_columns: true,
            }),
            &[
                [4, 1, 0], //
                [5, 2, 0], //
                [6, 3, 0], //
            ]
        );

        assert_eq!(
            &draw_memory_mapping(MemoryMapping {
                reverse_rows: true,
                reverse_columns: true,
                swap_rows_and_columns: true,
            }),
            &[
                [6, 3, 0], //
                [5, 2, 0], //
                [4, 1, 0], //
            ]
        );
    }

    #[test]
    fn into_memory_order_not_mirrored() {
        assert_eq!(
            &draw_memory_mapping(orientation(Rotation::Deg0, false).into()),
            &[
                [1, 2, 3], //
                [4, 5, 6], //
                [0, 0, 0], //
            ]
        );

        assert_eq!(
            &draw_memory_mapping(orientation(Rotation::Deg90, false).into()),
            &[
                [4, 1, 0], //
                [5, 2, 0], //
                [6, 3, 0], //
            ]
        );

        assert_eq!(
            &draw_memory_mapping(orientation(Rotation::Deg180, false).into()),
            &[
                [6, 5, 4], //
                [3, 2, 1], //
                [0, 0, 0], //
            ]
        );

        assert_eq!(
            &draw_memory_mapping(orientation(Rotation::Deg270, false).into()),
            &[
                [3, 6, 0], //
                [2, 5, 0], //
                [1, 4, 0], //
            ]
        );
    }

    #[test]
    fn into_memory_order_mirrored() {
        assert_eq!(
            &draw_memory_mapping(orientation(Rotation::Deg0, true).into()),
            &[
                [3, 2, 1], //
                [6, 5, 4], //
                [0, 0, 0], //
            ]
        );

        assert_eq!(
            &draw_memory_mapping(orientation(Rotation::Deg90, true).into()),
            &[
                [1, 4, 0], //
                [2, 5, 0], //
                [3, 6, 0], //
            ]
        );

        assert_eq!(
            &draw_memory_mapping(orientation(Rotation::Deg180, true).into()),
            &[
                [4, 5, 6], //
                [1, 2, 3], //
                [0, 0, 0], //
            ]
        );

        assert_eq!(
            &draw_memory_mapping(orientation(Rotation::Deg270, true).into()),
            &[
                [6, 3, 0], //
                [5, 2, 0], //
                [4, 1, 0], //
            ]
        );
    }

    #[test]
    fn equivalent_orientations() {
        let o1 = Orientation::new().rotate(Rotation::Deg270).flip_vertical();
        let o2 = Orientation::new().rotate(Rotation::Deg90).flip_horizontal();
        let o3 = Orientation::new()
            .flip_horizontal()
            .rotate(Rotation::Deg270);
        let o4 = Orientation::new().flip_vertical().rotate(Rotation::Deg90);

        assert_eq!(o1, o2);
        assert_eq!(o1, o3);
        assert_eq!(o1, o4);
    }
}
