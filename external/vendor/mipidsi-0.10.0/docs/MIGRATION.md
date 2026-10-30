# Migration guide for `mipidsi` crate

## v0.8 -> 0.9

### Users

* The `display_interface` dependency has been removed in favor of our own trait and implementations. This gives significantly better performance (#149)

  * Replace `display_interface_spi::SPIInterface` with `mipidsi::interface::SpiInterface`. Note that it requires a small/medium sized `&mut [u8]` buffer. 512 bytes works well, your milage may vary.
  ```rust
  // before
  use display_interface_spi::SPIInterface;

  let di = SPIInterface::new(spi_device, dc);

  // after
  use mipidsi::interface::SpiInterface;

  let mut buffer = [0_u8; 512];
  let di = SpiInterface::new(spi_device, dc, &mut buffer);
  ```

  * Replace `display_interface_parallel_gpio::PGPIO{8,16}BitInterface` with `mipidsi::interface::ParallelInterface` and use `Generic{8,16}BitBus` from `mipidsi::interface`
  ```rust
  // before
  use display_interface_parallel_gpio::Generic8BitBus;
  use display_interface_parallel_gpio::PGPIO8BitInterface;

  let bus = Generic8BitBus::new(pins);
  let di = PGPIO8BitInterface::new(bus, dc, wr);

  // after
  use mipidsi::interface::Generic8BitBus;
  use mipidsi::interface::ParallelInterface;

  let bus = Generic8BitBus::new(pins);
  let di = ParallelInterface::new(bus, dc, wr);
  ```

  * If you have a custom impl of the `display_interface_parallel_gpio::OutputBus` trait, replace it with `mipidsi::interface::OutputBus`. This trait is identical except that it uses an associated error type instead of being hardcoded to `display_interface::DisplayError`

  * If you are using `stm32f4xx-hal`'s fsmc, you can copy and paste this adapter:
  ```rust
  pub struct FsmcAdapter<S, WORD>(pub Lcd<S, WORD>);

  impl<S, WORD> Interface for FsmcAdapter<S, WORD>
  where
      S: SubBank,
      WORD: Word + Copy + From<u8>,
  {
      type Word = WORD;

      type Error = Infallible;

      fn send_command(&mut self, command: u8, args: &[u8]) -> Result<(), Self::Error> {
          self.0.write_command(command.into());
          for &arg in args {
              self.0.write_data(arg.into());
          }

          Ok(())
      }

      fn send_pixels<const N: usize>(
          &mut self,
          pixels: impl IntoIterator<Item = [Self::Word; N]>,
      ) -> Result<(), Self::Error> {
          for pixel in pixels {
              for word in pixel {
                  self.0.write_data(word);
              }
          }

          Ok(())
      }

      fn send_repeated_pixel<const N: usize>(
          &mut self,
          pixel: [Self::Word; N],
          count: u32,
      ) -> Result<(), Self::Error> {
          self.send_pixels((0..count).map(|_| pixel))
      }
    }
    ```


## v0.7 -> 0.8

### Users

* The dependencies for the `embedded-hal` and `display-interface` crates have been updated to make `mipidsi` compatible with the 1.0 release of `embedded-hal`.

* The model specific constructors (like `Builder::ili9341_rgb565`) have been removed. Use the generic `Builder::new` constructor instead:
  ```rust
  // 0.7
  use mipidsi::Builder;
  let display = Builder::ili9341_rgb565(di)
    .init(&mut delay, None)?;

  // 0.8
  use mipidsi::{Builder, models::ILI9341Rgb565};
  let display = Builder::new(ILI9341Rgb565, di)
    .init(&mut delay)?;
  ```
* The reset pin parameter from `Builder::init` has been removed. Use the `Builder::reset_pin` setter instead:
  ```rust
  // 0.7
  use mipidsi::Builder;
  let display = Builder::new(ili9341_rgb565, di)
    .init(&mut delay, Some(rst))?;

  // 0.8
  use mipidsi::{Builder, models::ILI9341Rgb565};
  let display = Builder::new(ILI9341Rgb565, di)
    .reset_pin(rst)
    .init(&mut delay)?;
  ```

* The `Builder::with_*` methods were renamed to versions without the `with_` prefix to bring the library in compliance with Rust API guidelines (see [this issue](https://github.com/almindor/mipidsi/issues/113) for more info):
  ```rust
  // 0.7
  use mipidsi::Builder;
  let display = Builder::new(ili9341_rgb565, di)
    .with_invert_colors(ColorInversion::Normal)
    .with_orientation(Orienation::default())
    .init(&mut delay, Some(rst))?;

  // 0.8
  use mipidsi::{Builder, models::ILI9341Rgb565};
  let display = Builder::new(ILI9341Rgb565, di)
    .invert_colors(ColorInversion::Normal)
    .orientation(Orienation::default())
    .reset_pin(rst)
    .init(&mut delay)?;
  ```

* The default values for the `invert_colors` and `color_order` settings were inconsistent between different models in `mipidsi` 0.7. In 0.8 all models use the same default values with no color inversion and RGB subpixel order. Take a look at the [troubleshooting guide](https://github.com/almindor/mipidsi/blob/master/docs/TROUBLESHOOTING.md#incorrect-colors) if your display shows incorrect colors after the update.

### Model writers

* The `default_options` function has been removed from the `Model` trait to make the default options consistent between the models. The maximum framebuffer size is now defined by the added `FRAMEBUFFER_SIZE` constant.

* The type of the `DELAY` parameter in the `init` method has been changed to the `embedded-hal` 1.0 type `DelayNs`.

## v0.6 -> 0.7

No breaking changes.

## v0.5 -> 0.6

### Users

* no change, addition of `Builder::with_invert_colors(bool)` allows more combinations of display variants.

### Model writers and specific variants

`Model::init` now expects the `options: &ModelOptions` instead of just `madcl: u8` argument. This allows the use of the `invert_colors` field during init.

## v0.4 -> 0.5

### Users

* use `Builder` to construct the `Display` and set any options directly on construction

#### v0.4

```rust
let display = Display::st7789(di, rst, DisplayOptions::default());
display.init(&mut delay);
```

#### v0.5

```rust
let display = Builder::st7789(di) // known model or with_model(model)
    .with_display_size(240, 240) // set any options on the builder before init
    .init(&mut delay, Some(rst)); // optional reset pin
```

### Model writers and specific variants

`Model::new` was reverted and is no longer necessary. Models now don't own the `ModelOptions` which has been moved off to the `Display` directly. `Model::init` has changed to include `madctl` parameter which is now provided by the `Display` and should be used as-is unless overrides are required.
`Model::default_options` was added to facilitate "generic variant" construction.

Helper constructors have been moved from `Display` to `Builder` with similar implementations as before.
`DisplayOptions` and `ModelOptions` values are now a function of the `Builder` and do not necessitate a constructor helper anymore. e.g. `Display::st7789_240x240(...)` becomes `Builder::st7789(...).with_display_size(240, 240)` controlled by the user.
Any variants can still set all of the options for a variant via a builder shortcut, such as `Builder::st7789_pico1`.

## v0.3 -> v0.4

### Users

* `Display` helper constructors now take `DisplayOptions` argument instead of `init`

#### v0.3

```rust
let display = Display::st7789(di, rst);
display.init(&mut delay, DisplayOptions::default());
```

#### v0.4 

```rust
let display = Display::st7789(di, rst, DisplayOptions::default());
display.init(&mut delay);
```

### Model writers and specific variants

`Model` now requires that the `Model::new` constructor takes `ModelOptions` which is an artefact of `DisplayOptions` in combination with display sizing and windowing settings. This is used by the "helper constructors" to provide pre-made `Model` variants to users.

Most display `Model`s require just one constructor but some like the `ST7789` have a lot of variants that have different display, frameber sizes or even windowing clipping offsets. These can now be provided easily by creating a helper constructor that provides the dimensions information to create `ModelOptions`.

For users that need to use a variant of a `Model` that does not yet have a constructor helper, this can be done manually provided you know what your display dimensions and offsets are.