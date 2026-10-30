//! Development-related functionality.

// TODO(tarcieri): move all development-related macros into this module

/// Implement projective arithmetic tests.
#[macro_export]
macro_rules! impl_projective_arithmetic_tests {
    (
        $affine:tt,
        $projective:tt,
        $scalar:ty,
        $add_vectors:expr,
        $mul_vectors:expr
    ) => {
        /// Assert that the provided projective point matches the given test vector.
        // TODO(tarcieri): use coordinate APIs. See zkcrypto/group#30
        macro_rules! assert_point_eq {
            ($actual:expr, $expected:expr) => {
                let (expected_x, expected_y) = $expected;

                let point = $actual.to_affine().to_encoded_point(false);
                let (actual_x, actual_y) = match point.coordinates() {
                    sec1::Coordinates::Uncompressed { x, y } => (x, y),
                    _ => unreachable!(),
                };

                assert_eq!(&expected_x, actual_x.as_slice());
                assert_eq!(&expected_y, actual_y.as_slice());
            };
        }

        #[test]
        fn affine_to_projective() {
            let basepoint_affine = $affine::GENERATOR;
            let basepoint_projective = $projective::GENERATOR;

            assert_eq!($projective::from(basepoint_affine), basepoint_projective,);
            assert_eq!(basepoint_projective.to_affine(), basepoint_affine);
            assert!(!bool::from(basepoint_projective.to_affine().is_identity()));

            assert!(bool::from($projective::IDENTITY.to_affine().is_identity()));
        }

        #[test]
        fn projective_identity_addition() {
            let identity = $projective::IDENTITY;
            let generator = $projective::GENERATOR;

            assert_eq!(identity + &generator, generator);
            assert_eq!(generator + &identity, generator);
        }

        #[test]
        fn projective_mixed_addition() {
            let identity = $projective::IDENTITY;
            let basepoint_affine = $affine::GENERATOR;
            let basepoint_projective = $projective::GENERATOR;

            assert_eq!(identity + &basepoint_affine, basepoint_projective);
            assert_eq!(
                basepoint_projective + &basepoint_affine,
                basepoint_projective + &basepoint_projective
            );
        }

        #[test]
        fn test_vector_repeated_add() {
            let generator = $projective::GENERATOR;
            let mut p = generator;

            for i in 0..$add_vectors.len() {
                assert_point_eq!(p, $add_vectors[i]);
                p += &generator;
            }
        }

        #[test]
        fn test_vector_repeated_add_mixed() {
            let generator = $affine::GENERATOR;
            let mut p = $projective::GENERATOR;

            for i in 0..$add_vectors.len() {
                assert_point_eq!(p, $add_vectors[i]);
                p += &generator;
            }
        }

        #[test]
        fn test_vector_add_mixed_identity() {
            let generator = $projective::GENERATOR;
            let p0 = generator + $projective::IDENTITY;
            let p1 = generator + $affine::IDENTITY;
            assert_eq!(p0, p1);
        }

        #[test]
        fn test_vector_double_generator() {
            let generator = $projective::GENERATOR;
            let mut p = generator;

            for i in 0..2 {
                assert_point_eq!(p, $add_vectors[i]);
                p = p.double();
            }
        }

        #[test]
        fn projective_add_vs_double() {
            let generator = $projective::GENERATOR;
            assert_eq!(generator + &generator, generator.double());
        }

        #[test]
        fn projective_add_and_sub() {
            let basepoint_affine = $affine::GENERATOR;
            let basepoint_projective = $projective::GENERATOR;

            assert_eq!(
                (basepoint_projective + &basepoint_projective) - &basepoint_projective,
                basepoint_projective
            );
            assert_eq!(
                (basepoint_projective + &basepoint_affine) - &basepoint_affine,
                basepoint_projective
            );
        }

        #[test]
        fn projective_double_and_sub() {
            let generator = $projective::GENERATOR;
            assert_eq!(generator.double() - &generator, generator);
        }

        #[test]
        fn test_vector_scalar_mult() {
            let generator = $projective::GENERATOR;

            for (k, coords) in $add_vectors
                .iter()
                .enumerate()
                .map(|(k, coords)| (<$scalar>::from(k as u64 + 1), *coords))
                .chain($mul_vectors.iter().cloned().map(|(k, x, y)| {
                    (
                        <$scalar>::from_repr(
                            $crate::generic_array::GenericArray::clone_from_slice(&k),
                        )
                        .unwrap(),
                        (x, y),
                    )
                }))
            {
                let p = generator * &k;
                assert_point_eq!(p, coords);
            }
        }
    };
}
