use crate::options::TearingEffect;

use super::DcsCommand;

/// Set Tearing Effect
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct SetTearingEffect(TearingEffect);

impl SetTearingEffect {
    /// Construct a new SetTearingEffect DCS with the given value
    pub fn new(tearing_effect: TearingEffect) -> Self {
        SetTearingEffect(tearing_effect)
    }
}

impl DcsCommand for SetTearingEffect {
    fn instruction(&self) -> u8 {
        match self.0 {
            TearingEffect::Off => 0x34,
            TearingEffect::Vertical => 0x35,
            TearingEffect::HorizontalAndVertical => 0x35,
        }
    }

    fn fill_params_buf(&self, buffer: &mut [u8]) -> usize {
        match self.0 {
            TearingEffect::Off => 0,
            TearingEffect::Vertical => {
                buffer[0] = 0x0;
                1
            }
            TearingEffect::HorizontalAndVertical => {
                buffer[0] = 0x1;
                1
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn set_tearing_effect_both_fills_param_properly() {
        let ste = SetTearingEffect(TearingEffect::HorizontalAndVertical);

        let mut buffer = [0u8; 1];
        assert_eq!(ste.instruction(), 0x35);
        assert_eq!(ste.fill_params_buf(&mut buffer), 1);
        assert_eq!(buffer, [0x1]);
    }

    #[test]
    fn set_tearing_effect_off_fills_param_properly() {
        let ste = SetTearingEffect(TearingEffect::Off);

        let mut buffer = [0u8; 0];
        assert_eq!(ste.instruction(), 0x34);
        assert_eq!(ste.fill_params_buf(&mut buffer), 0);
    }
}
