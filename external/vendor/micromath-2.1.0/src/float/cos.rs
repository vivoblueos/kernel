//! Cosine function implemented using a parabolic approximation.
//!
//! Note that while this method is inspired by a [Taylor series] approximation,
//! it provides both better performance and accuracy.
//!
//! Most of the other trigonometric functions in this crate are implemented in
//! terms of this approximation.
//!
//! Method described: <https://stackoverflow.com/posts/28050328/revisions>
//!
//! Originally based on this approximation by Nick Capen:
//!
//! <https://web.archive.org/web/20180105200343if_/http://forum.devmaster.net/t/fast-and-accurate-sine-cosine/9648>
//!
//! Post quoted below for posterity as the original site is down:
//!
//! > In some situations you need a good approximation of sine and cosine that
//! > runs at very high performance. One example is to implement dynamic
//! > subdivision of round surfaces, comparable to those in Quake 3. Or to
//! > implement wave motion, in case there are no vertex shaders 2.0 available.
//! >
//! > The standard C `sinf()` and `cosf()` functions are terribly slow and offer
//! > much more precision than what we actually need. What we really want is an
//! > approximation that offers the best compromise between precision and
//! > performance. The most well known approximation method is to use a
//! > [Taylor series] about 0 (also known as a Maclaurin series), which for
//! > sine becomes:
//! >
//! > ```text
//! > x - 1/6 x^3 + 1/120 x^5 - 1/5040 x^7 + ...
//! > ```
//! >
//! > When we plot this we get: taylor.gif. The green line is the real sine,
//! > the red line is the first four terms of the Taylor series. This seems
//! > like an acceptable approximation, but lets have a closer look:
//! > taylor_zoom.gif. It behaves very nicely up till `pi/2`, but after that it
//! > quickly deviates. At pi, it evaluates to -0.075 instead of 0. Using this
//! > for wave simulation will result in jerky motion which is unacceptable.
//! >
//! > We could add another term, which in fact reduces the error significantly,
//! > but this makes the formula pretty lengthy. We already need 7
//! > multiplications and 3 additions for the 4-term version. The Taylor series
//! > just can't give us the precision and performance we're looking for.
//! >
//! > We did however note that we need `sin(pi) = 0`. And there's another thing
//! > we can see from taylor_zoom.gif: this looks very much like a parabola!
//! > So let's try to find the formula of a parabola that matches it as closely
//! > as possible. The generic formula for a parabola is `A + B x + C x²`. So
//! > this gives us three degrees of freedom. Obvious choices are that we want
//! > `sin(0) = 0`, `sin(pi/2) = 1` and `sin(pi) = 0`. This gives us the following
//! > three equations:
//! >
//! > ```text
//! > A + B 0 + C 0² = 0
//! > A + B pi/2 + C (pi/2)² = 1
//! > A + B pi + C pi² = 0
//! > ```
//! >
//! > Which has as solution `A = 0, B = 4/pi, C = -4/pi²`. So our parabola
//! > approximation becomes `4/pi x - 4/pi² x²`. Plotting this we get:
//! > parabola.gif. This looks worse than the 4-term Taylor series, right?
//! > Wrong! The maximum absolute error is 0.056. Furthermore, this
//! > approximation will give us smooth wave motion, and can be calculated
//! > in only 3 multiplications and 1 addition!
//! >
//! > Unfortunately it's not very practical yet. This is what we get in the
//! > `[-pi, pi]` range: negative.gif. It's quite obvious we want at least a
//! > full period. But it's also clear that it's just another parabola,
//! > mirrored around the origin. The formula for it is `4/pi x + 4/pi² x²`.
//! > So the straightforward (pseudo-C) solution is:
//! >
//! > ```text
//! > if(x > 0)
//! > {
//! >     y = 4/pi x - 4/pi² x²;
//! > }
//! > else
//! > {
//! >     y = 4/pi x + 4/pi² x²;
//! > }
//! > ```
//! >
//! > Adding a branch is not a good idea though. It makes the code
//! > significantly slower. But look at how similar the two parts really are.
//! > A subtraction becomes an addition depending on the sign of x. In a naive
//! > first attempt to eliminate the branch we can 'extract' the sign of x
//! > using `x / abs(x)`. The division is very expensive but look at the resulting
//! > formula: `4/pi x - x / abs(x) 4/pi² x²`. By inverting the division we can
//! > simplify this to a very nice and clean `4/pi x - 4/pi² x abs(x)`. So for
//! > just one extra operation we get both halves of our sine approximation!
//! > Here's the graph of this formula confirming the result: abs.gif.
//! >
//! > Now let's look at cosine. Basic trigonometry tells us that
//! > `cos(x) = sin(pi/2 + x)`. Is that all, add pi/2 to x? No, we actually get
//! > the unwanted part of the parabola again: shift_sine.gif. What we need to
//! > do is 'wrap around' when x > pi/2. This can be done by subtracting 2 pi.
//! > So the code becomes:
//! >
//! > ```text
//! > x += pi/2;
//! >
//! > if(x > pi)   // Original x > pi/2
//! > {
//! >     x -= 2 * pi;   // Wrap: cos(x) = cos(x - 2 pi)
//! > }
//! >
//! > y = sin(x);
//! > ```
//! >
//! > Yet another branch. To eliminate it, we can use binary logic, like this:
//! >
//! > ```text
//! > x -= (x > pi) & (2 * pi);
//! > ```
//! >
//! > Note that this isn't valid C code at all. But it should clarify how this
//! > can work. When x > pi is false the & operation zeroes the right hand part
//! > so the subtraction does nothing, which is perfectly equivalent. I'll
//! > leave it as an excercise to the reader to create working C code for this
//! > (or just read on). Clearly the cosine requires a few more operations than
//! > the sine but there doesn't seem to be any other way and it's still
//! > extremely fast.
//! >
//! > Now, a maximum error of 0.056 is nice but clearly the 4-term Taylor series
//! > still has a smaller error on average. Recall what our sine looked like:
//! > abs.gif. So isn't there anything we can do to further increase precision
//! > at minimal cost? Of course the current version is already applicable for
//! > many situations where something that looks like a sine is just as good as
//! > the real sine. But for other situations that's just not good enough.
//! >
//! > Looking at the graphs you'll notice that our approximation always
//! > overestimates the real sine, except at 0, pi/2 and pi. So what we need is
//! > to 'scale it down' without touching these important points. The solution
//! > is to use the squared parabola, which looks like this: squared.gif. Note
//! > how it preserves those important points but it's always lower than the
//! > real sine. So we can use a weighted average of the two to get a better
//! > approximation:
//! >
//! > ```text
//! > Q (4/pi x - 4/pi² x²) + P (4/pi x - 4/pi² x²)²
//! > ```
//! >
//! > With `Q + P = 1`. You can use exact minimization of either the absolute
//! > or relative error but I'll save you the math. The optimal weights are
//! > `Q = 0.775`, `P = 0.225` for the absolute error and `Q = 0.782`,
//! > `P = 0.218` for the relative error. I will use the former. The resulting
//! > graph is: average.gif. Where did the red line go? It's almost entirely
//! > covered by the green line, which instantly shows how good this
//! > approximation really is. The maximum error is about 0.001, a 50x
//! > improvement! The formula looks lengthy but the part between parenthesis
//! > is the same value from the parabola, which needs to be computed only
//! > once. In fact only 2 extra multiplications and 2 additions are required
//! > to achieve this precision boost.
//! >
//! > It shouldn't come as a big surprise that to make it work for negative x
//! > as well we need a second abs() operation. The final C code for the sine
//! > becomes:
//! >
//! > ```text
//! > float sin(float x)
//! > {
//! >     const float B = 4/pi;
//! >     const float C = -4/(pi*pi);
//! >
//! >     float y = B * x + C * x * abs(x);
//! >
//! >     #ifdef EXTRA_PRECISION
//! >     //  const float Q = 0.775;
//! >         const float P = 0.225;
//! >
//! >         y = P * (y * abs(y) - y) + y;   // Q * y + P * y * abs(y)
//! >     #endif
//! > }
//! > ```
//! >
//! > So we need merely 5 multiplications and 3 additions; still faster than
//! > the 4-term Taylor if we neglect the abs(), and much more precise! The
//! > cosine version just needs the extra shift and wrap operations on x.
//! >
//! > Last but not least, I wouldn't be Nick if I didn't include the SIMD
//! > optimized assembly version. It allows to perform the wrap operation very
//! > efficiently so I'll give you the cosine:
//! >
//! > ```asm
//! > // cos(x) = sin(x + pi/2)
//! > addps xmm0, PI_2
//! > movaps xmm1, xmm0
//! > cmpnltps xmm1, PI
//! > andps xmm1, PIx2
//! > subps xmm0, xmm1
//! >
//! > // Parabola
//! > movaps xmm1, xmm0
//! > andps xmm1, abs
//! > mulps xmm1, xmm0
//! > mulps xmm0, B
//! > mulps xmm1, C
//! > addps xmm0, xmm1
//! >
//! > // Extra precision
//! > movaps xmm1, xmm0
//! > andps xmm1, abs
//! > mulps xmm1, xmm0
//! > subps xmm1, xmm0
//! > mulps xmm1, P
//! > addps xmm0, xmm1
//! > ```
//! >
//! > This code computes four cosines in parallel, resulting in a peak
//! > performance of about 9 clock cycles per cosine for most CPU architectures.
//! > Sines take only 6 clock cycles ideally. The lower precision version can
//! > even run at 3 clock cycles per sine... And lets not forget that all input
//! > between -pi and pi is valid and the formula is exact at -pi, -pi/2, 0,
//! > pi/2 and pi.
//! >
//! > So, the conclusion is don't ever again use a Taylor series to approximate
//! > a sine or cosine! To add a useful discussion to this article, I'd love to
//! > hear if anyone knows good approximations for other transcendental functions
//! > like the exponential, logarithm and power functions.

use super::F32;
use core::f32::consts::FRAC_1_PI;

impl F32 {
    /// Approximates `cos(x)` in radians with a maximum error of `0.002`.
    pub fn cos(self) -> Self {
        let mut x = self;
        x *= FRAC_1_PI / 2.0;
        x -= 0.25 + (x + 0.25).floor().0;
        x *= 16.0 * (x.abs() - 0.5);
        x += 0.225 * x * (x.abs() - 1.0);
        x
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::F32;

    /// Maximum error in radians
    pub(crate) const MAX_ERROR: f32 = 0.002;

    /// Cosine test vectors - `(input, output)`
    const TEST_VECTORS: &[(f32, f32)] = &[
        (0.000, 1.000),
        (0.140, 0.990),
        (0.279, 0.961),
        (0.419, 0.914),
        (0.559, 0.848),
        (0.698, 0.766),
        (0.838, 0.669),
        (0.977, 0.559),
        (1.117, 0.438),
        (1.257, 0.309),
        (1.396, 0.174),
        (1.536, 0.035),
        (1.676, -0.105),
        (1.815, -0.242),
        (1.955, -0.375),
        (2.094, -0.500),
        (2.234, -0.616),
        (2.374, -0.719),
        (2.513, -0.809),
        (2.653, -0.883),
        (2.793, -0.940),
        (2.932, -0.978),
        (3.072, -0.998),
        (3.211, -0.998),
        (3.351, -0.978),
        (3.491, -0.940),
        (3.630, -0.883),
        (3.770, -0.809),
        (3.910, -0.719),
        (4.049, -0.616),
        (4.189, -0.500),
        (4.328, -0.375),
        (4.468, -0.242),
        (4.608, -0.105),
        (4.747, 0.035),
        (4.887, 0.174),
        (5.027, 0.309),
        (5.166, 0.438),
        (5.306, 0.559),
        (5.445, 0.669),
        (5.585, 0.766),
        (5.725, 0.848),
        (5.864, 0.914),
        (6.004, 0.961),
        (6.144, 0.990),
        (6.283, 1.000),
    ];

    #[test]
    fn sanity_check() {
        for &(x, expected) in TEST_VECTORS {
            let cos_x = F32(x).cos();
            let delta = (cos_x - expected).abs();

            assert!(
                delta <= MAX_ERROR,
                "delta {} too large: {} vs {}",
                delta,
                cos_x,
                expected
            );
        }
    }
}
