use core::marker::PhantomData;

use embedded_graphics_core::{
    geometry::{AnchorPoint, AnchorX},
    prelude::*,
    primitives::Rectangle,
};

/// Test image.
///
/// The test image can be used to check if the display is working and to
/// identify the correct orientation and color settings.
///
/// # Expected output
///
#[doc = include_str!("../assets/test_image.svg")]
///
/// Note that the gray border around the image above is only added to make the
/// white border visible on the light rustdoc theme and will not be visible when
/// the test image is drawn.
///
/// - There should be a one pixel white border around the display.  
///   Modify the [display size](crate::Builder::display_size) and [display
///   offset](crate::Builder::display_offset) settings, if at least one
///   edge of the white border isn't drawn or if there is a gap between the
///   white border and the edge of the display.
/// - A white triangle should be drawn in the top left corner and the RGB label text should not be mirrored.  
///   Modify the [orientation](crate::Builder::orientation) setting to
///   rotate and mirror the display until the test image is displayed correctly.
///   Note that the white triangle might not be visible on displays with rounded
///   corners.
/// - The colored bars should match the labels.  
///   Use the [color inversion](crate::Builder::invert_colors) and [color
///   order](crate::Builder::color_order) settings until the colored bars
///   and labels match.
#[derive(Default)]
pub struct TestImage<C: RgbColor> {
    color_type: PhantomData<C>,
}

impl<C: RgbColor> TestImage<C> {
    /// Creates a new test image
    pub const fn new() -> Self {
        Self {
            color_type: PhantomData,
        }
    }
}

const BORDER_WIDTH: u32 = 1;
const BORDER_PADDING: u32 = 4;
const TOP_LEFT_MARKER_SIZE: u32 = 20;

impl<C: RgbColor> Drawable for TestImage<C> {
    type Color = C;
    type Output = ();

    fn draw<D>(&self, target: &mut D) -> Result<Self::Output, D::Error>
    where
        D: DrawTarget<Color = Self::Color>,
    {
        draw_border(target, BORDER_WIDTH)?;

        let color_bar_area = target
            .bounding_box()
            .offset(-i32::try_from(BORDER_WIDTH + BORDER_PADDING).unwrap());
        draw_color_bars(target, &color_bar_area)?;

        draw_top_left_marker(target, &color_bar_area, TOP_LEFT_MARKER_SIZE)?;

        Ok(())
    }
}

/// Draws a white border around the draw target.
fn draw_border<D>(target: &mut D, width: u32) -> Result<(), D::Error>
where
    D: DrawTarget,
    D::Color: RgbColor,
{
    let bounding_box = target.bounding_box();
    let inner_box = bounding_box.offset(-i32::try_from(width).unwrap());

    target.fill_contiguous(
        &bounding_box,
        bounding_box.points().map(|p| {
            if inner_box.contains(p) {
                D::Color::BLACK
            } else {
                D::Color::WHITE
            }
        }),
    )
}

/// Draws RGB color bars and labels.
fn draw_color_bars<D>(target: &mut D, area: &Rectangle) -> Result<(), D::Error>
where
    D: DrawTarget,
    D::Color: RgbColor,
{
    target.fill_solid(area, RgbColor::GREEN)?;
    Character::new(G, area.center()).draw(target)?;

    let rect = area.resized_width(area.size.width / 3, AnchorX::Left);
    target.fill_solid(&rect, RgbColor::RED)?;
    Character::new(R, rect.center()).draw(target)?;

    let rect = area.resized_width(area.size.width / 3, AnchorX::Right);
    target.fill_solid(&rect, RgbColor::BLUE)?;
    Character::new(B, rect.center()).draw(target)?;

    Ok(())
}

// Draws a triangular marker in the top left corner.
fn draw_top_left_marker<D>(target: &mut D, area: &Rectangle, size: u32) -> Result<(), D::Error>
where
    D: DrawTarget,
    D::Color: RgbColor,
{
    let mut rect = area.resized(Size::new(size, 1), AnchorPoint::TopLeft);

    while rect.size.width > 0 {
        target.fill_solid(&rect, D::Color::WHITE)?;

        rect.top_left.y += 1;
        rect.size.width -= 1;
    }

    Ok(())
}

const R: &[u8] = &[
    0, 0, 0, 0, 0, 0, 0, 0, 0, //
    0, 0, 0, 0, 0, 0, 0, 0, 0, //
    0, 0, 1, 1, 1, 1, 0, 0, 0, //
    0, 0, 1, 0, 0, 0, 1, 0, 0, //
    0, 0, 1, 0, 0, 0, 1, 0, 0, //
    0, 0, 1, 1, 1, 1, 0, 0, 0, //
    0, 0, 1, 0, 1, 0, 0, 0, 0, //
    0, 0, 1, 0, 0, 1, 0, 0, 0, //
    0, 0, 1, 0, 0, 0, 1, 0, 0, //
    0, 0, 0, 0, 0, 0, 0, 0, 0, //
    0, 0, 0, 0, 0, 0, 0, 0, 0, //
];

const G: &[u8] = &[
    0, 0, 0, 0, 0, 0, 0, 0, 0, //
    0, 0, 0, 0, 0, 0, 0, 0, 0, //
    0, 0, 0, 1, 1, 1, 1, 0, 0, //
    0, 0, 1, 0, 0, 0, 0, 0, 0, //
    0, 0, 1, 0, 0, 0, 0, 0, 0, //
    0, 0, 1, 0, 1, 1, 1, 0, 0, //
    0, 0, 1, 0, 0, 0, 1, 0, 0, //
    0, 0, 1, 0, 0, 0, 1, 0, 0, //
    0, 0, 0, 1, 1, 1, 1, 0, 0, //
    0, 0, 0, 0, 0, 0, 0, 0, 0, //
    0, 0, 0, 0, 0, 0, 0, 0, 0, //
];

const B: &[u8] = &[
    0, 0, 0, 0, 0, 0, 0, 0, 0, //
    0, 0, 0, 0, 0, 0, 0, 0, 0, //
    0, 0, 1, 1, 1, 1, 0, 0, 0, //
    0, 0, 1, 0, 0, 0, 1, 0, 0, //
    0, 0, 1, 0, 0, 0, 1, 0, 0, //
    0, 0, 1, 1, 1, 1, 0, 0, 0, //
    0, 0, 1, 0, 0, 0, 1, 0, 0, //
    0, 0, 1, 0, 0, 0, 1, 0, 0, //
    0, 0, 1, 1, 1, 1, 0, 0, 0, //
    0, 0, 0, 0, 0, 0, 0, 0, 0, //
    0, 0, 0, 0, 0, 0, 0, 0, 0, //
];

struct Character<C> {
    data: &'static [u8],
    center: Point,
    color_type: PhantomData<C>,
}

impl<C> Character<C> {
    fn new(data: &'static [u8], center: Point) -> Self {
        Self {
            data,
            center,
            color_type: PhantomData,
        }
    }
}

impl<C: RgbColor> Drawable for Character<C> {
    type Color = C;
    type Output = ();

    fn draw<D>(&self, target: &mut D) -> Result<(), D::Error>
    where
        D: DrawTarget<Color = Self::Color>,
    {
        let rect = Rectangle::with_center(self.center, Size::new(9, 11));

        target.fill_contiguous(
            &rect,
            self.data.iter().map(|d| {
                if *d == 0 {
                    RgbColor::BLACK
                } else {
                    RgbColor::WHITE
                }
            }),
        )
    }
}
