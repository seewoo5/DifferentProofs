import Verso
import VersoManual
import VersoBlueprint
import DifferentProofsBlueprint.ProofColor
import DifferentProofs.IntegerRectangle.Basic
import DifferentProofs.IntegerRectangle.Checkerboard
import DifferentProofs.IntegerRectangle.ComplexIntegral
import DifferentProofs.IntegerRectangle.Defs
import DifferentProofs.IntegerRectangle.RealIntegral

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option linter.style.longLine false

#doc (Manual) "Tiling a Rectangle" =>

:::group "grp:int-rect"
Wagon's theorem on tiling a rectangle by rectangles with an integer side.
:::

:::definition "def:int-rect" (parent := "grp:int-rect") (lean := "IntegerRectangle.IntegerRectangleTheorem")
Stan Wagon's theorem (*Fourteen Proofs of a Result About Tiling a Rectangle*, Amer. Math. Monthly
$`94` (1987) 601–617) states: whenever a rectangle is tiled by finitely many rectangles, each of
which has at least one integer side, then the tiled rectangle has at least one integer side. Here a
*tiling* is a covering by axis-parallel rectangles with pairwise-disjoint interiors.
:::

The three analytic proofs below share one mechanism. To a rectangle $`[a,b] \times [c,d]` attach the
number $`\int\!\!\int g(x)\,h(y)\,dx\,dy`, which by Fubini factors as
$`\bigl(\int_a^b g\bigr)\bigl(\int_c^d h\bigr)`. This functional is additive over a tiling because
the tiles are pairwise almost-disjoint (their overlaps lie in null boundaries), so it is captured by
one lemma.

:::lemma_ "lem:int-rect-engine" (parent := "grp:int-rect") (lean := "IntegerRectangle.IsTiling.prod_integral_dichotomy")
Let $`T` tile $`R` and let $`g, h` be integrable one-variable functions. If for every tile either its
width-integral of $`g` or its height-integral of $`h` vanishes, then the same dichotomy holds for the
ambient rectangle: either $`\int g` over the width of $`R` vanishes, or $`\int h` over its height does.
:::

:::proof "lem:int-rect-engine"
By Fubini the plane integral of $`g(x)h(y)` over any rectangle factors as the product of the two
coordinate integrals. Additivity of the plane integral over the tiling — valid since distinct tiles
meet only in their measure-zero boundaries — writes $`\int\!\!\int_R g\,h` as the sum over tiles of
$`\int\!\!\int_{T_i} g\,h`. Each summand is a product with a vanishing factor, so it is $`0`; hence
$`\bigl(\int_R g\bigr)\bigl(\int_R h\bigr) = 0`, and a product of reals (or complex numbers) vanishes
only if a factor does.
:::

First proof: a complex double integral, de Bruijn's original method.

:::theorem "thm:int-rect-complex" (parent := "grp:int-rect") (lean := "IntegerRectangle.ComplexIntegral.IntegerRectangleTheorem_ComplexIntegral") (proofColor := "#fbcfe8")
A rectangle tiled by rectangles each with an integer side has an integer side.
:::

:::proof "thm:int-rect-complex"
Take $`g(x) = h(x) = e^{2\pi i x}`. The one-dimensional integral
$`\int_a^b e^{2\pi i x}\,dx = (e^{2\pi i b} - e^{2\pi i a})/(2\pi i)` vanishes if and only if $`e^{2\pi i(b-a)} = 1`,
i.e. $`b - a \in \mathbb{Z}`. So a tile's coordinate integral vanishes exactly when that side is an
integer; the hypothesis gives the per-tile dichotomy, the engine {uses "lem:int-rect-engine"}[]
transports it to $`R`, and the same criterion reads off an integer side. The complex exponential is
what makes the criterion an exact "integer side" statement, with no reflected solutions.
:::

Second proof: a real double integral (Wagon's specialization of the first).

:::theorem "thm:int-rect-real" (parent := "grp:int-rect") (lean := "IntegerRectangle.RealIntegral.IntegerRectangleTheorem_RealIntegral") (proofColor := "#fbcfe8")
A rectangle tiled by rectangles each with an integer side has an integer side.
:::

:::proof "thm:int-rect-real"
Use the real integrand $`\sin(2\pi(x - R_x))\sin(2\pi(y - R_y))`, where $`(R_x, R_y)` is the corner of
$`R`; shifting the integrand by the corner replaces Wagon's "place $`R` in standard position". The
factor integral is $`\int_a^b \sin(2\pi(x-s))\,dx = (\cos 2\pi(a-s) - \cos 2\pi(b-s))/(2\pi)`. It
vanishes whenever $`b - a \in \mathbb{Z}` (used for the tiles, where the shift is irrelevant); and at
the corner, where the lower limit equals the shift, it reduces to $`(1 - \cos 2\pi(b-s))/(2\pi)`,
which vanishes if and only if $`b - s \in \mathbb{Z}`. The engine {uses "lem:int-rect-engine"}[] then
forces an integer side of $`R`.
:::

Third proof: a checkerboard colouring (Rochberg–Stein), the discretization of the second.

:::theorem "thm:int-rect-checker" (parent := "grp:int-rect") (lean := "IntegerRectangle.Checkerboard.IntegerRectangleTheorem_Checkerboard") (proofColor := "#fbcfe8")
A rectangle tiled by rectangles each with an integer side has an integer side.
:::

:::proof "thm:int-rect-checker"
Colour the plane in a $`\tfrac12 \times \tfrac12` checkerboard with a corner at $`R`'s corner;
"equal black and white" over a region means $`\int\!\!\int (-1)^{\lfloor 2x\rfloor}(-1)^{\lfloor 2y\rfloor} = 0`.
The one-dimensional factor $`(-1)^{\lfloor 2(x-s)\rfloor}` is the $`\pm 1` square wave of period $`1`;
its integral over any integer-length interval is $`0`, so every tile with an integer side is balanced.
By the engine {uses "lem:int-rect-engine"}[] so is $`R`. But over $`[s, b]` the square wave integrates
to the triangle wave $`\min(r, 1-r)`, with $`r` the fractional part of $`b - s`, which is nonzero
unless $`b - s \in \mathbb{Z}`; hence $`R` has an integer side.
:::
