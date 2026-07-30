import Verso
import VersoManual
import VersoBlueprint
import DifferentProofsBlueprint.ProofColor
import DifferentProofs.IntegerRectangle.Basic
import DifferentProofs.IntegerRectangle.Checkerboard
import DifferentProofs.IntegerRectangle.ComplexIntegral
import DifferentProofs.IntegerRectangle.Defs
import DifferentProofs.IntegerRectangle.RealIntegral
import DifferentProofs.IntegerRectangle.StepFunction
import DifferentProofs.IntegerRectangle.SweepLine

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

The first three proofs below are analytic and share one mechanism. To a rectangle $`[a,b] \times [c,d]` attach the
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

Twelfth proof: a sweep line (Bachman–Yannakakis). This one does not use the analytic engine above.
Instead of an integral it propagates a conserved quantity upward through the tiling, and the only
geometry it needs is what a horizontal cut of a tiling looks like — the slice lemma below.

:::lemma_ "lem:int-rect-slice" (parent := "grp:int-rect") (lean := "IntegerRectangle.SweepLine.widthSum_slice")
Let $`T` tile $`R` and let $`t` be a height between the bottom and the top of $`R` avoiding every
horizontal tile edge. Then the widths of the tiles crossed by the line $`y = t` add up to the width
of $`R`.
:::

:::proof "lem:int-rect-slice"
Because $`t` avoids the horizontal edges, a tile met by the line at all is crossed through its
interior, and its trace on the line is the closed interval spanned by its width. The traces cover
the full cross-section of $`R` at height $`t` because the tiles cover $`R`, and two distinct traces
meet in a null set: an interior point of both traces would be an interior point of both tiles.
Additivity of one-dimensional Lebesgue measure over this almost-disjoint cover gives the claim.
:::

:::lemma_ "lem:int-rect-conservation" (parent := "grp:int-rect") (lean := "IntegerRectangle.SweepLine.gain_eq_loss")
At every height $`c` strictly between the bottom and the top of $`R`, the tiles whose bottom edge
lies at $`c` (the tiles *born* at $`c`) have the same total width as the tiles whose top edge lies
at $`c` (the tiles *dying* at $`c`).
:::

:::proof "lem:int-rect-conservation"
The finitely many horizontal tile edges leave a punctured neighbourhood of $`c` edge-free, so the
slice lemma {uses "lem:int-rect-slice"}[] applies at heights just below and just above $`c`, and
both slices total the width of $`R`. The slice below consists of the tiles strictly straddling $`c`
together with those dying at $`c`; the slice above, of the same straddling tiles together with those
born at $`c`. Subtracting the common straddling part equates the gain with the loss.
:::

:::lemma_ "lem:int-rect-jump" (parent := "grp:int-rect") (lean := "IntegerRectangle.SweepLine.exists_int_jump")
Call a height *integral* if it lies an integer distance above the base of $`R`, and suppose every
tile has an integer side. For a height $`c` below the top of $`R`, let the *gain* $`G(c)` be the
total width of the tiles born at $`c` whose top edge is non-integral, and the *loss* $`L(c)` the
total width of the tiles dying at $`c` whose top edge is non-integral. Then
$`G(c) - L(c) \in \mathbb{Z}`.
:::

:::proof "lem:int-rect-jump"
A tile with exactly one of its two horizontal edges at integral height has non-integer height,
hence integer width by the hypothesis, and any sum of such widths is an integer. If $`c` is
integral then $`L(c) = 0` outright — a tile dying at $`c` has its top edge at the integral height
$`c`, so it is not counted — while every tile counted by $`G(c)` has integral bottom and
non-integral top, so $`G(c)` is an integer. If $`c` is not integral (in particular $`c` is strictly
above the base), then *every* tile dying at $`c` has non-integral top, so $`L(c)` is the full dying
width, which by conservation {uses "lem:int-rect-conservation"}[] equals the full born width; hence
$`G(c) - L(c)` is minus the width born at $`c` with integral top, and each such tile has
non-integral bottom and integral top — integer width again.
:::

:::theorem "thm:int-rect-sweep" (parent := "grp:int-rect") (lean := "IntegerRectangle.SweepLine.IntegerRectangleTheorem_SweepLine") (proofColor := "#fbcfe8")
A rectangle tiled by rectangles each with an integer side has an integer side.
:::

:::proof "thm:int-rect-sweep"
Suppose the height of $`R` is not an integer, and sweep a horizontal line up through the tiling. At
height $`t` let $`f(t)` be the total width of the tiles the line meets — each tile taken with its
bottom edge removed — whose top edge is at non-integral height above the base of $`R`. Below $`R`
no tile has been entered, so $`f = 0`. At the top of $`R` exactly the tiles touching the top edge
are counted — their top edge is at the height of $`R`, which is non-integral — and by the slice
lemma {uses "lem:int-rect-slice"}[] applied just below the top these tiles span the full width, so
$`f` ends at the width of $`R`. Between horizontal tile edges $`f` is constant, and crossing a
height $`c` changes it by the gain minus the loss at $`c`, which is an integer
{uses "lem:int-rect-jump"}[]. Rather than sorting the finitely many tile edges, this is packaged as
local constancy of $`t \mapsto \{f(t)\}` and settled by connectedness of $`\mathbb{R}`: the
fractional part of the width of $`R` equals the fractional part of $`f` below $`R`, namely $`0`.
(The jump lemma stops below the top of $`R` — conservation genuinely fails there, that failure
being the theorem — so $`f` is frozen at the top before taking fractional parts.)
:::

Thirteenth proof: step functions (Hochster–Maté). Like the first three this attaches a number to
each rectangle and rides on additivity over the tiling, but the number comes from a *step function*
instead of an integral. Correspondingly the mechanism is not almost-everywhere disjointness of the
tiles but the exact partition of a tiling into half-open cells, which makes every plane measure —
not just Lebesgue measure — additive over a tiling.

:::lemma_ "lem:int-rect-step-engine" (parent := "grp:int-rect") (lean := "IntegerRectangle.StepFunction.dichotomy")
Let $`f` and $`g` be Stieltjes functions, that is, monotone and right-continuous, and write
$`\Delta_a^b = (f - g)(b) - (f - g)(a)` for the increment of $`f - g` across $`(a, b]`. If $`T` tiles
$`R` and every tile has vanishing increment across its width or across its height, then the same
dichotomy holds for $`R`.
:::

:::proof "lem:int-rect-step-engine"
A Stieltjes function $`f` induces a measure with $`\mu_f(a, b] = f(b) - f(a)`, finite on every
interval, so the increment $`\Delta_a^b` is the signed mass $`\mu_f(a, b] - \mu_g(a, b]`. Multiplying
the increment across the width by the increment across the height and expanding the two differences
writes the product as a combination of the four product measures $`\mu_f \otimes \mu_f`,
$`\mu_f \otimes \mu_g`, $`\mu_g \otimes \mu_f`, $`\mu_g \otimes \mu_g`, each evaluated on the
half-open cell $`(x_0, x_1] \times (y_0, y_1]` of the rectangle. Since the half-open cells of a
tiling partition the half-open cell of the tiled rectangle exactly, every plane measure is additive
over a tiling, so the product of the two increments is too. Each tile contributes a product with a
vanishing factor, hence the product for $`R` vanishes, and a product of reals vanishes only if a
factor does.
:::

:::theorem "thm:int-rect-step" (parent := "grp:int-rect") (lean := "IntegerRectangle.StepFunction.IntegerRectangleTheorem_StepFunction") (proofColor := "#fbcfe8")
A rectangle tiled by rectangles each with an integer side has an integer side.
:::

:::proof "thm:int-rect-step"
Take $`f(x) = x` and $`g(x) = \lfloor x \rfloor`; both are monotone and right-continuous, and their
measures are Lebesgue measure and the counting measure of the integers. Their difference is the
sawtooth $`\{x\} = x - \lfloor x\rfloor`, so the increment across $`(a, b]` is $`\{b\} - \{a\}`,
which vanishes if and only if $`b - a \in \mathbb{Z}`. A tile with an integer side therefore
satisfies the hypothesis of the engine {uses "lem:int-rect-step-engine"}[], which returns a
vanishing increment for $`R` in one of the two directions — an integer side. The sawtooth criterion
is an exact "integer difference" statement, so unlike the checkerboard proof, whose triangle wave is
symmetric about the half-integers, this argument needs no standard-position hypothesis.
:::
