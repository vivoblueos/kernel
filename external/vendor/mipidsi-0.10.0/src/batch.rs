//! Original code from: [this repo](https://github.com/lupyuen/piet-embedded/blob/master/piet-embedded-graphics/src/batch.rs)
//! Batch the pixels to be rendered into Pixel Rows and Pixel Blocks (contiguous Pixel Rows).
//! This enables the pixels to be rendered efficiently as Pixel Blocks, which may be transmitted in a single Non-Blocking SPI request.
use crate::{
    interface::{Interface, InterfacePixelFormat},
    models::Model,
    Display,
};
use embedded_graphics_core::prelude::*;
use embedded_hal::digital::OutputPin;

pub trait DrawBatch<DI, M, I>
where
    DI: Interface,
    M: Model,
    M::ColorFormat: InterfacePixelFormat<DI::Word>,
    I: IntoIterator<Item = Pixel<M::ColorFormat>>,
{
    fn draw_batch(&mut self, item_pixels: I) -> Result<(), DI::Error>;
}

impl<DI, M, RST, I> DrawBatch<DI, M, I> for Display<DI, M, RST>
where
    DI: Interface,
    M: Model,
    M::ColorFormat: InterfacePixelFormat<DI::Word>,
    I: IntoIterator<Item = Pixel<M::ColorFormat>>,
    RST: OutputPin,
{
    fn draw_batch(&mut self, item_pixels: I) -> Result<(), DI::Error> {
        //  Get the pixels for the item to be rendered.
        let pixels = item_pixels.into_iter();
        //  Batch the pixels into Pixel Rows.
        let rows = to_rows(pixels);
        //  Batch the Pixel Rows into Pixel Blocks.
        let blocks = to_blocks(rows);
        //  For each Pixel Block...
        for PixelBlock {
            x_left,
            x_right,
            y_top,
            y_bottom,
            colors,
            ..
        } in blocks
        {
            //  Render the Pixel Block.
            self.set_pixels(x_left, y_top, x_right, y_bottom, colors)?;

            //  Dump out the Pixel Blocks for the square in test_display()
            /* if x_left >= 60 && x_left <= 150 && x_right >= 60 && x_right <= 150 && y_top >= 60 && y_top <= 150 && y_bottom >= 60 && y_bottom <= 150 {
                console::print("pixel block ("); console::printint(x_left as i32); console::print(", "); console::printint(y_top as i32); ////
                console::print("), ("); console::printint(x_right as i32); console::print(", "); console::printint(y_bottom as i32); console::print(")\n"); ////
            } */
        }
        Ok(())
    }
}

/// Max number of pixels per Pixel Row
const MAX_ROW_SIZE: usize = 50;
/// Max number of pixels per Pixel Block
const MAX_BLOCK_SIZE: usize = 100;

/// Consecutive color words for a Pixel Row
type RowColors<C> = heapless::Vec<C, MAX_ROW_SIZE>;
/// Consecutive color words for a Pixel Block
type BlockColors<C> = heapless::Vec<C, MAX_BLOCK_SIZE>;

/// Iterator for each Pixel Row in the pixel data. A Pixel Row consists of contiguous pixels on the same row.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct RowIterator<C, P>
where
    C: PixelColor,
    P: Iterator<Item = Pixel<C>>,
{
    /// Pixels to be batched into rows
    pixels: P,
    /// Start column number
    x_left: u16,
    /// End column number
    x_right: u16,
    /// Row number
    y: u16,
    /// List of pixel colours for the entire row
    colors: RowColors<C>,
    /// True if this is the first pixel for the row
    first_pixel: bool,
}

/// Iterator for each Pixel Block in the pixel data. A Pixel Block consists of contiguous Pixel Rows with the same start and end column number.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct BlockIterator<C, R>
where
    C: PixelColor,
    R: Iterator<Item = PixelRow<C>>,
{
    /// Pixel Rows to be batched into blocks
    rows: R,
    /// Start column number
    x_left: u16,
    /// End column number
    x_right: u16,
    /// Start row number
    y_top: u16,
    /// End row number
    y_bottom: u16,
    /// List of pixel colours for the entire block, row by row
    colors: BlockColors<C>,
    /// True if this is the first row for the block
    first_row: bool,
}

/// A row of contiguous pixels
pub struct PixelRow<C>
where
    C: PixelColor,
{
    /// Start column number
    pub x_left: u16,
    /// End column number
    pub x_right: u16,
    /// Row number
    pub y: u16,
    /// List of pixel colours for the entire row
    pub colors: RowColors<C>,
}

/// A block of contiguous pixel rows with the same start and end column number
pub struct PixelBlock<C>
where
    C: PixelColor,
{
    /// Start column number
    pub x_left: u16,
    /// End column number
    pub x_right: u16,
    /// Start row number
    pub y_top: u16,
    /// End row number
    pub y_bottom: u16,
    /// List of pixel colours for the entire block, row by row
    pub colors: BlockColors<C>,
}

/// Batch the pixels into Pixel Rows, which are contiguous pixels on the same row.
/// P can be any Pixel Iterator (e.g. a rectangle).
fn to_rows<C, P>(pixels: P) -> RowIterator<C, P>
where
    C: PixelColor,
    P: Iterator<Item = Pixel<C>>,
{
    RowIterator::<C, P> {
        pixels,
        x_left: 0,
        x_right: 0,
        y: 0,
        colors: RowColors::new(),
        first_pixel: true,
    }
}

/// Batch the Pixel Rows into Pixel Blocks, which are contiguous Pixel Rows with the same start and end column number
/// R can be any Pixel Row Iterator.
fn to_blocks<C, R>(rows: R) -> BlockIterator<C, R>
where
    C: PixelColor,
    R: Iterator<Item = PixelRow<C>>,
{
    BlockIterator::<C, R> {
        rows,
        x_left: 0,
        x_right: 0,
        y_top: 0,
        y_bottom: 0,
        colors: BlockColors::new(),
        first_row: true,
    }
}

/// Implement the Iterator for Pixel Rows.
/// P can be any Pixel Iterator (e.g. a rectangle).
impl<C, P> Iterator for RowIterator<C, P>
where
    C: PixelColor,
    P: Iterator<Item = Pixel<C>>,
{
    /// This Iterator returns Pixel Rows
    type Item = PixelRow<C>;

    /// Return the next Pixel Row of contiguous pixels on the same row
    fn next(&mut self) -> Option<Self::Item> {
        //  Loop over all pixels until we have composed a Pixel Row, or we have run out of pixels.
        loop {
            //  Get the next pixel.
            let next_pixel = self.pixels.next();
            match next_pixel {
                None => {
                    //  If no more pixels...
                    if self.first_pixel {
                        return None; //  No pixels to group
                    }
                    //  Else return previous pixels as row.
                    let row = PixelRow {
                        x_left: self.x_left,
                        x_right: self.x_right,
                        y: self.y,
                        colors: self.colors.clone(),
                    };
                    self.colors.clear();
                    self.first_pixel = true;
                    return Some(row);
                }
                Some(Pixel(coord, color)) => {
                    if coord.x < 0 || coord.y < 0 {
                        continue;
                    }
                    //  If there is a pixel...
                    let x = coord.x as u16;
                    let y = coord.y as u16;
                    //  Save the first pixel as the row start and handle next pixel.
                    if self.first_pixel {
                        self.first_pixel = false;
                        self.x_left = x;
                        self.x_right = x;
                        self.y = y;
                        self.colors.clear();
                        if self.colors.push(color).is_err() {
                            return None;
                        }
                        continue;
                    }
                    //  If this pixel is adjacent to the previous pixel, add to the row.
                    if x == self.x_right.wrapping_add(1)
                        && y == self.y
                        && self.colors.push(color).is_ok()
                    {
                        // Don't add pixel if too many pixels in the row.
                        self.x_right = x;
                        continue;
                    }
                    //  Else return previous pixels as row.
                    let row = PixelRow {
                        x_left: self.x_left,
                        x_right: self.x_right,
                        y: self.y,
                        colors: self.colors.clone(),
                    };
                    self.x_left = x;
                    self.x_right = x;
                    self.y = y;
                    self.colors.clear();
                    if self.colors.push(color).is_err() {
                        return None;
                    }
                    return Some(row);
                }
            }
        }
    }
}

/// Implement the Iterator for Pixel Blocks.
/// R can be any Pixel Row Iterator.
impl<C, R> Iterator for BlockIterator<C, R>
where
    C: PixelColor,
    R: Iterator<Item = PixelRow<C>>,
{
    /// This Iterator returns Pixel Blocks
    type Item = PixelBlock<C>;

    /// Return the next Pixel Block of contiguous Pixel Rows with the same start and end column number
    fn next(&mut self) -> Option<Self::Item> {
        //  Loop over all Pixel Rows until we have composed a Pixel Block, or we have run out of Pixel Rows.
        loop {
            //  Get the next Pixel Row.
            let next_row = self.rows.next();
            match next_row {
                None => {
                    //  If no more Pixel Rows...
                    if self.first_row {
                        return None; //  No rows to group
                    }
                    //  Else return previous rows as block.
                    let row = PixelBlock {
                        x_left: self.x_left,
                        x_right: self.x_right,
                        y_top: self.y_top,
                        y_bottom: self.y_bottom,
                        colors: self.colors.clone(),
                    };
                    self.colors.clear();
                    self.first_row = true;
                    return Some(row);
                }
                Some(PixelRow {
                    x_left,
                    x_right,
                    y,
                    colors,
                    ..
                }) => {
                    //  If there is a Pixel Row...
                    //  Save the first row as the block start and handle next block.
                    if self.first_row {
                        self.first_row = false;
                        self.x_left = x_left;
                        self.x_right = x_right;
                        self.y_top = y;
                        self.y_bottom = y;
                        self.colors.clear();
                        self.colors.extend_from_slice(&colors).expect("never");
                        continue;
                    }
                    //  If this row is adjacent to the previous row and same size, add to the block.
                    if y == self.y_bottom + 1 && x_left == self.x_left && x_right == self.x_right {
                        //  Don't add row if too many pixels in the block.
                        if self.colors.extend_from_slice(&colors).is_ok() {
                            self.y_bottom = y;
                            continue;
                        }
                    }
                    //  Else return previous rows as block.
                    let row = PixelBlock {
                        x_left: self.x_left,
                        x_right: self.x_right,
                        y_top: self.y_top,
                        y_bottom: self.y_bottom,
                        colors: self.colors.clone(),
                    };
                    self.x_left = x_left;
                    self.x_right = x_right;
                    self.y_top = y;
                    self.y_bottom = y;
                    self.colors.clear();
                    self.colors.extend_from_slice(&colors).expect("never");
                    return Some(row);
                }
            }
        }
    }
}
