import Verso
import VersoManual
import VersoBlueprint
import DifferentProofsBlueprint.ProofColor
import DifferentProofs.IntegerRectangle.Basic
import DifferentProofs.IntegerRectangle.Checkerboard
import DifferentProofs.IntegerRectangle.ComplexIntegral
import DifferentProofs.IntegerRectangle.Defs
import DifferentProofs.IntegerRectangle.Primes
import DifferentProofs.IntegerRectangle.RealIntegral
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

Sixth proof: prime numbers (Robinson). Wagon scales the tiling by a prime $`p` and rounds all tile
corners to integers, which requires verifying that the rounded rectangles tile again. Instead we
count lattice points: rounding is hidden inside a floor, and the re-tiling is replaced by the fact
that the *half-open* cells of a tiling — each tile minus its left and bottom edges — genuinely
partition the half-open cell of $`R`, with no null sets involved.

:::lemma_ "lem:int-rect-partition" (parent := "grp:int-rect") (lean := "IntegerRectangle.IsTiling.iUnion_toSetIoc")
The half-open cells of the tiles of a tiling are pairwise disjoint and their union is the half-open
cell of the tiled rectangle.
:::

:::proof "lem:int-rect-partition"
Disjointness: a point common to two half-open cells moves down-and-left — to the midpoint between
the higher of the two lower-left corners and the point itself — into the interiors of both tiles,
contradicting interior-disjointness. Covering: a point of the ambient half-open cell is approached
from below-left; every such nudge stays in $`R`, hence in some tile, and since there are finitely
many tiles one tile contains nudges arbitrarily close in. That tile is closed, so it contains the
point, and the nudges witness the two strict inequalities of its half-open cell.
:::

:::lemma_ "lem:int-rect-count" (parent := "grp:int-rect") (lean := "IntegerRectangle.Primes.card_latticePoints_eq_sum")
For $`p > 0`, the number of points of the lattice $`\tfrac1p\mathbb{Z} \times \tfrac1p\mathbb{Z}`
in the half-open cell of $`R` is the sum of the numbers of such points in the half-open cells of
the tiles. Moreover the count for a rectangle $`[x_0,x_1] \times [y_0,y_1]` is the product
$`(\lfloor p x_1 \rfloor - \lfloor p x_0 \rfloor)(\lfloor p y_1 \rfloor - \lfloor p y_0 \rfloor)`.
:::

:::proof "lem:int-rect-count"
A lattice point $`(a/p, b/p)` lies in the half-open cell iff $`\lfloor p x_0\rfloor < a \le
\lfloor p x_1\rfloor` and likewise for $`b`, which gives the product formula; additivity is then
exactly the exact-partition property {uses "lem:int-rect-partition"}[] of the half-open cells, read
through this membership description.
:::

:::lemma_ "lem:int-rect-near" (parent := "grp:int-rect") (lean := "IntegerRectangle.Primes.exists_side_near_int")
If every tile has an integer side, then for every prime $`p` the width or the height of $`R` is
within $`1/p` of an integer.
:::

:::proof "lem:int-rect-near"
A tile side of integer length $`n` contributes the floor-difference factor
$`\lfloor p x_0 + pn\rfloor - \lfloor p x_0\rfloor = pn`, so every tile's lattice count is
divisible by $`p`, and by additivity {uses "lem:int-rect-count"}[] so is the count of $`R`, a
product of two floor differences. Primality forces $`p` to divide one factor, say
$`\lfloor p x_1\rfloor - \lfloor p x_0\rfloor = pm`; then $`p(x_1 - x_0) - pm` is a difference of
two floor remainders, each in $`[0,1)`, so $`|`width$` - m| < 1/p`.
:::

:::theorem "thm:int-rect-primes" (parent := "grp:int-rect") (lean := "IntegerRectangle.Primes.IntegerRectangleTheorem_Primes") (proofColor := "#fbcfe8")
A rectangle tiled by rectangles each with an integer side has an integer side.
:::

:::proof "thm:int-rect-primes"
Suppose neither side of $`R` is an integer. Each of the width and the height then keeps some fixed
positive distance from every integer — at least the smaller of its fractional part and one minus
it. Choosing a prime $`p` larger than the reciprocals of both distances (there are infinitely many
primes), no side of $`R` can be within $`1/p` of an integer, contradicting the claim
{uses "lem:int-rect-near"}[] for this $`p`.
:::
