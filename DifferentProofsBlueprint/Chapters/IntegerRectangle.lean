import Verso
import VersoManual
import VersoBlueprint
import DifferentProofsBlueprint.ProofColor
import DifferentProofs.IntegerRectangle.Basic
import DifferentProofs.IntegerRectangle.BipartiteGraph
import DifferentProofs.IntegerRectangle.Checkerboard
import DifferentProofs.IntegerRectangle.ComplexIntegral
import DifferentProofs.IntegerRectangle.CornerCount
import DifferentProofs.IntegerRectangle.CountingSquares
import DifferentProofs.IntegerRectangle.Defs
import DifferentProofs.IntegerRectangle.EulerianPath
import DifferentProofs.IntegerRectangle.GridRefinement
import DifferentProofs.IntegerRectangle.Polynomials
import DifferentProofs.IntegerRectangle.Primes
import DifferentProofs.IntegerRectangle.RealIntegral
import DifferentProofs.IntegerRectangle.ReducibleLink
import DifferentProofs.IntegerRectangle.Staircase
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

Fourth proof: counting squares (Ruzsa, Gilbert). Wagon translates every grid line of the tiling
that lies off the lattice through the corner of $`R` onto the nearest half-integer line, leaving
lattice lines fixed; the tiling becomes a tiling of a translated rectangle all of whose
coordinates sit on the half-unit grid, so every rectangle in it is a union of
$`\tfrac12 \times \tfrac12` squares — the checkerboard cells of the third proof — and the argument
is a parity count of those squares. As with the polynomial proof below, the fg-area supplies the
count without the auxiliary tiling having to be built.

:::lemma_ "lem:int-rect-cell-parity" (parent := "grp:int-rect") (lean := "IntegerRectangle.CountingSquares.even_cellIndex_iff")
Measure a coordinate $`x` from a base point $`a` by the integer
$`c(x) = \lfloor x - a \rfloor + \lceil x - a \rceil`, twice the translated coordinate of $`x` on
the half-unit grid based at $`a`. Then $`c(x)` is even exactly when $`x - a` is an integer.
:::

:::proof "lem:int-rect-cell-parity"
Floor and ceiling agree at the integers and differ by one everywhere else, so $`c(x)` is
$`2\lfloor x - a\rfloor` in the first case and $`2\lfloor x - a\rfloor + 1` in the second.
:::

:::lemma_ "lem:int-rect-cellcount" (parent := "grp:int-rect") (lean := "IntegerRectangle.CountingSquares.sum_cellCount")
The number of half-unit squares covered by the translation of a rectangle — the product of the
increments of the two grid coordinates across it — is additive over a tiling.
:::

:::proof "lem:int-rect-cellcount"
That number is by definition the fg-area of the pair of grid coordinate functions, so this is
fg-area additivity {uses "lem:int-rect-fgarea"}[], read back in the integers. It is what Wagon gets
from the auxiliary tiling, here without having to check that the translated tiles tile the
translated rectangle.
:::

:::theorem "thm:int-rect-counting" (parent := "grp:int-rect") (lean := "IntegerRectangle.CountingSquares.IntegerRectangleTheorem_CountingSquares") (proofColor := "#fbcfe8")
A rectangle tiled by rectangles each with an integer side has an integer side.
:::

:::proof "thm:int-rect-counting"
Base the half-unit grid at the lower-left corner of $`R`. The endpoints of a side of integer
length $`n` are $`n` apart, so the translation moves them equally and the increment of the grid
coordinate across that side is $`2n`: every tile covers an even number of squares, and hence
{uses "lem:int-rect-cellcount"}[] so does $`R`. The corner of $`R` has grid coordinate $`0`, so
that count is the product of the grid coordinates of the far edges of $`R`, and one of the two
factors is even — which says {uses "lem:int-rect-cell-parity"}[] that the corresponding side of
$`R` has integer length. (Wagon phrases the last step as a contradiction: a translated rectangle
with no integer side has both sides equal to half an odd integer, hence an odd number of squares.)
:::

Fifth proof: polynomials (Douady). Through the lower-left corner of $`R`, fix the two coordinate
lattices and introduce a parameter $`t`. Move a vertical grid line by $`t` when its x-coordinate is
off the x-lattice, and move a horizontal grid line by $`t` when its y-coordinate is off the
y-lattice; leave lattice lines fixed. The perturbed areas become honest polynomials in $`t`; the
fg-area formalizes them without separately constructing the auxiliary tiling.

:::theorem "thm:int-rect-polynomials" (parent := "grp:int-rect") (lean := "IntegerRectangle.Polynomials.IntegerRectangleTheorem_Polynomials") (proofColor := "#fbcfe8")
A rectangle tiled by rectangles each with an integer side has an integer side.
:::

:::proof "thm:int-rect-polynomials"
Let $`\varepsilon_x(u)` be $`0` when $`u - R_x \in \mathbb{Z}` and $`1` otherwise, and similarly
define $`\varepsilon_y`; perturb the coordinates by $`\varphi_t(u) = u + t\varepsilon_x(u)` and
$`\psi_t(v) = v + t\varepsilon_y(v)`. The perturbed area of a rectangle $`S` is then the value at
$`t` of the polynomial $`P_S = (\Delta\varepsilon_x X + w)(\Delta\varepsilon_y X + h)`, with
$`w, h` the sides of $`S` and $`\Delta\varepsilon` the indicator increments across them; its
quadratic coefficient is the fg-area of the indicator pair. If a tile has an integer side, the two
endpoints of that side have the same indicator, the corresponding factor is constant, and the
quadratic coefficient vanishes: the tile's perturbed area is linear or constant in $`t`, as in
Wagon's text. Additivity of the fg-area {uses "lem:int-rect-fgarea"}[] equates $`\sum_i P_{T_i}`
with $`P_R` at every real $`t` — Wagon needs $`t` small so that the moved segments still bound a
tiling, the algebraic identity does not — hence $`\sum_i P_{T_i} = P_R` as polynomials. If neither
side of $`R` is an integer, each lower endpoint has indicator $`0` and each upper endpoint $`1`,
so the quadratic coefficient of $`P_R` is $`1`; comparing $`X^2`-coefficients yields $`0 = 1`, a
contradiction. (A polynomial-free variant of the same computation: each tile's term is affine in
$`t`, so the second finite difference $`F(2) - 2F(1) + F(0)` of the identity vanishes tile by
tile, while it equals $`2` on $`(w + t)(h + t)`.)
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

Seventh proof: an Eulerian path (Paterson). Let $`\Gamma` be the graph whose vertices are the
corners of the tiles, two of them joined whenever they are the two ends of a horizontal side of a
tile of integer width, or of a vertical side of a tile of integer height. A tile having a vertex as
a corner contributes exactly one edge there, so the degree of a vertex is the number of tiles
having it as a corner: $`2` or $`4` away from the corners of $`R`, while a corner of $`R` lies on
exactly one tile and has degree $`1`. A walk that starts at a corner of $`R` and repeats no edge
can therefore not stop before it reaches another corner of $`R`. Every edge of $`\Gamma` is a
segment of integer length parallel to an axis, so the two corners differ by a vector with integer
entries, and that is an integer side of $`R`.

Of the degrees only the parity is ever used. Wagon reads it off the local picture — a point other
than a corner of $`R` is a corner of $`2` or $`4` tiles — which is a statement about how tiles fit
together around a point. It follows instead from the fg-area additivity of the thirteenth proof
below, with no local analysis at all, in the form of the corner parity lemma; that lemma and the
double count following it are shared with the eighth proof. Corners are counted with multiplicity,
so degenerate tiles need no separate treatment.

:::lemma_ "lem:int-rect-corner-parity" (parent := "grp:int-rect") (lean := "IntegerRectangle.IsTiling.sum_cornerCount_mod_two")
Let $`T` tile $`R`. At every point of the plane, the tiles have in total a number of corners
congruent modulo $`2` to the number of corners of $`R` there. (Each rectangle has four corners,
counted with multiplicity.)
:::

:::proof "lem:int-rect-corner-parity"
Fix a point $`(u, v)` and take for $`f` and $`g` the indicator functions of $`\{u\}` and
$`\{v\}`. The fg-area of a rectangle is then
$`(\mathbb{1}[x_1 = u] - \mathbb{1}[x_0 = u])(\mathbb{1}[y_1 = v] - \mathbb{1}[y_0 = v])`, the
number of corners at $`(u, v)` with the left and bottom edges counted negatively. Being an fg-area
it is additive over the tiling {uses "lem:int-rect-fgarea"}[], and modulo $`2` subtraction and
addition agree, so each signed count may be replaced by the corner count.
:::

:::lemma_ "lem:int-rect-double-count" (parent := "grp:int-rect") (lean := "IntegerRectangle.IsTiling.even_sum_cornerCount")
Let $`T` tile $`R` and let $`Z` be a finite set of points of the plane in which every tile has an
even number of corners. Then $`R` has an even number of corners in $`Z`.
:::

:::proof "lem:int-rect-double-count"
Count the incidences between the points of $`Z` and the tiles having them as a corner. Tile by
tile the total is even by hypothesis. Counting the same incidences point by point instead, and
replacing each point's count by the corresponding count for $`R`
{uses "lem:int-rect-corner-parity"}[], leaves the parity unchanged, so the number of corners of
$`R` in $`Z` is even too.
:::

:::lemma_ "lem:int-rect-euler-walk" (parent := "grp:int-rect") (lean := "IntegerRectangle.EulerianPath.exists_reachable_corner")
Let $`T` tile $`R`, every tile having an integer side. Then some walk in $`\Gamma` leads from the
lower-left corner of $`R` to another corner of $`R`.
:::

:::proof "lem:int-rect-euler-walk"
Take for $`Z` the connected component of the lower-left corner of $`R`, that is, the vertices a
walk starting there reaches. An edge of $`\Gamma` has both of its ends in $`Z` or neither, and the
sides that a tile with an integer side contributes to $`\Gamma` pair up its four corners; so every
tile has an even number of corners in $`Z`, and by the double count
{uses "lem:int-rect-double-count"}[] so has $`R`. The lower-left corner of $`R` is one of them,
hence not the only one.
:::

:::theorem "thm:int-rect-euler" (parent := "grp:int-rect") (lean := "IntegerRectangle.EulerianPath.IntegerRectangleTheorem_EulerianPath") (proofColor := "#fbcfe8")
A rectangle tiled by rectangles each with an integer side has an integer side.
:::

:::proof "thm:int-rect-euler"
An edge of $`\Gamma` is a side of a tile, parallel to an axis and of integer length, so it leaves
the pair of fractional parts of a point unchanged, and hence so does a walk. The walk to a second
corner of $`R` {uses "lem:int-rect-euler-walk"}[] therefore preserves the fractional part of the
abscissa or of the ordinate — of both, if it ends at the opposite corner — which says that the
width or the height of $`R` is an integer.
:::

Eighth proof: a bipartite graph, Wagon's variation on the preceding proof. Place $`R` in standard
position and join each point of the lattice $`\mathbb{Z} \times \mathbb{Z}` to the tiles having it
as a corner; then count the edges of that graph in the two possible ways. It is the same count as
before, taken over a lattice grid instead of a connected component of $`\Gamma`. The lattice used
below is the one through the lower-left corner of $`R`, which replaces the standard position, and
rather than the tile corners the count runs over all lattice points of $`R`, which changes nothing
since a non-corner contributes $`0` on both sides.

:::lemma_ "lem:int-rect-bipartite-count" (parent := "grp:int-rect") (lean := "IntegerRectangle.BipartiteGraph.even_sum_cornerCount")
Let $`T` tile $`R`, and let $`X` and $`Y` be finite sets of abscissae and of ordinates such that
every tile has both or neither of its vertical edges over $`X`, or both or neither of its
horizontal edges over $`Y`. Then $`R` has an even number of corners on the grid $`X \times Y`.
:::

:::proof "lem:int-rect-bipartite-count"
The number of corners a rectangle has on the grid is the number of its vertical edges over $`X`
times the number of its horizontal edges over $`Y`, so by hypothesis every tile has an even number
of them, and the double count {uses "lem:int-rect-double-count"}[] applies.
:::

:::theorem "thm:int-rect-bipartite" (parent := "grp:int-rect") (lean := "IntegerRectangle.BipartiteGraph.IntegerRectangleTheorem_BipartiteGraph") (proofColor := "#fbcfe8")
A rectangle tiled by rectangles each with an integer side has an integer side.
:::

:::proof "thm:int-rect-bipartite"
Take for $`X` and $`Y` the points of the lattices through the left and bottom edges of $`R` that
lie inside $`R`. A tile of integer width has its two vertical edges an integer apart, so both or
neither lie on the lattice, and likewise in the other direction; the hypothesis of the count
{uses "lem:int-rect-bipartite-count"}[] therefore holds, and $`R` has evenly many corners on the
grid. Its lower-left corner is one of them. If neither side of $`R` were an integer, its right
edge would miss $`X` and its top edge would miss $`Y`, leaving that corner as the only one — an
odd number.
:::

Ninth proof: induction (Raphael Robinson). Call a tile an *H-tile* if it is designated by its
integer width and a *V-tile* if it is designated by its integer height. Cutting every tile into
unit pieces along its designated side normalizes the tiling: every H-tile is then exactly one unit
wide and every V-tile exactly one unit tall. The induction runs on the number of H-tiles. Robinson
grows a vertical strip of width $`1` from an H-tile, expanding it one unit at a time through the
V-tiles above it until an H-tile blocks the way, then stepping onto that H-tile and carrying on;
and likewise downwards. The resulting staircase runs from the bottom edge of $`R` to its top edge,
and deleting it and sliding everything on its right one unit leftwards tiles a rectangle one unit
narrower with fewer H-tiles.

:::lemma_ "lem:int-rect-normalize" (parent := "grp:int-rect") (lean := "IntegerRectangle.IsTiling.normalized")
Every tiling by tiles with an integer side refines to a normalized one, in which every tile is one
unit wide or one unit tall.
:::

:::proof "lem:int-rect-normalize"
Discard the degenerate tiles and cut each remaining tile into unit pieces along a side of integer
length, of which it has at least one, and which is at least one unit long since the tile is
nondegenerate. The half-open cells of the pieces of a tile partition its own, so the cells of all
the pieces still partition those of $`R`.
:::

:::lemma_ "lem:int-rect-column" (parent := "grp:int-rect") (lean := "IntegerRectangle.Staircase.exists_column")
In a normalized tiling the strip of width $`1` carried by an H-tile runs upwards through whole
V-tiles until it reaches the top of $`R` or an H-tile starts across it.
:::

:::proof "lem:int-rect-column"
Induct on the number of unit levels the strip has risen. Nothing crosses the top edge of the
H-tile inside the strip, since the only tile below that edge there is the H-tile itself. If
nothing crosses the height reached so far and no H-tile starts there, then the tile above each
point of that height starts exactly there, hence is a V-tile and is one unit tall; it therefore
spans the whole level, nothing crosses the next height, and the strip is still inside $`R`. Each
level raises the strip by a unit, so it cannot rise forever.
:::

:::lemma_ "lem:int-rect-staircase" (parent := "grp:int-rect") (lean := "IntegerRectangle.Staircase.exists_strip")
A normalized tiling with an H-tile has a staircase strip of width $`1` running from the bottom
edge of $`R` to its top edge and containing an H-tile. Every tile lies to the left of the strip at
each of its heights, or to its right, or inside it, and none lies to the left at one height and to
the right at another.
:::

:::proof "lem:int-rect-staircase"
Walk down from the given H-tile: while the column below the current H-tile is blocked, step onto
the H-tile blocking it, which lies strictly lower, so the walk stops at an H-tile whose column
reaches the bottom of $`R`. From there build the staircase upwards {uses "lem:int-rect-column"}[]
column by column, each step raising the top edge to a strictly higher one of the finitely many
heights carrying a horizontal edge of the tiling. A tile meeting a column lies inside it, so it
meets no other column, and the strip has a single abscissa along it; and consecutive columns
overlap horizontally, since the H-tile carrying the upper column crosses the lower one. A tile to
the left of the staircase at one height and to its right at another would have to fit in the gap
between two consecutive columns, and there is no gap.
:::

:::lemma_ "lem:int-rect-cut" (parent := "grp:int-rect") (lean := "IntegerRectangle.Staircase.isTiling_cut")
Cutting a normalized tiling along its staircase strip and sliding everything on the right of the
strip one unit leftwards tiles the rectangle one unit narrower.
:::

:::proof "lem:int-rect-cut"
Each tile is cut at a single abscissa: its right edge if it lies left of the strip, its left edge
less one if it lies right of the strip, and the left edge of the strip if it lies inside it — and
since the staircase is a wall {uses "lem:int-rect-staircase"}[] the same alternative holds at all
of that tile's heights. A point of the shrunken rectangle left of the strip comes from the point
itself and one to its right from its translate one unit rightwards, so the half-open cells of the
pieces partition those of the shrunken rectangle.
:::

:::theorem "thm:int-rect-induction" (parent := "grp:int-rect") (lean := "IntegerRectangle.Staircase.IntegerRectangleTheorem_Staircase") (proofColor := "#fbcfe8")
A rectangle tiled by rectangles each with an integer side has an integer side.
:::

:::proof "thm:int-rect-induction"
Normalize the tiling {uses "lem:int-rect-normalize"}[] and induct on the number of its H-tiles.
With no H-tile every tile has integer height, hence so does $`R`. Otherwise grow the staircase
from an H-tile {uses "lem:int-rect-staircase"}[]. If $`R` is narrower than two units then the
H-tile leaves no room beside it and $`R` is exactly one unit wide. Otherwise cut the staircase out
{uses "lem:int-rect-cut"}[]: heights never change, so V-tiles stay V-tiles, and an H-tile is
carried over whole or swallowed by the strip, so the new tiling is normalized and has fewer
H-tiles — the one the staircase was grown from is gone. Its rectangle is one unit narrower and
just as tall, so an integer side of it is an integer side of $`R`.
:::

Tenth proof: induction on reducible links (Richard Bishop and Wagon), Wagon's variation on
Robinson's induction. Call a tile an *H-tile* if it is designated by its integer width and a
*V-tile* if it is designated by its integer height. A *V-link* is a maximal stretch of a vertical
line of the tiling that no tile crosses and that no horizontal segment cuts, and an *H-link* is
its horizontal counterpart — so the H-links are the V-links of the transposed tiling. A link is
*reducible* if it is a V-link with only H-tiles along one of its sides, or an H-link with only
V-tiles along one of its sides. The proof is an induction on the number of tiles: a reducible link
always exists, and reducing it loses a tile.

:::lemma_ "lem:int-rect-link-side" (parent := "grp:int-rect") (lean := "IntegerRectangle.ReducibleLink.Link.exists_left")
At every height of a V-link there is a tile whose right edge lies on the link, and it sticks out
past neither end of the link.
:::

:::proof "lem:int-rect-link-side"
Approach the point of the link at that height from below left; the tile whose half-open cell
contains it has the line on or to the right of its own right edge. It cannot reach past the line,
for a tile crossing the line would block a height interior to the link, and it cannot reach past
either end of the link, because whatever blocks that end — a tile crossing the line, or a
horizontal edge arriving at the line from both sides — would share a point with it.
:::

:::lemma_ "lem:int-rect-link-push" (parent := "grp:int-rect") (lean := "IntegerRectangle.ReducibleLink.isTiling_push")
Let $`T` tile $`R`, let a V-link of the tiling be given, and let $`w > 0` be at most the width of
every tile abutting the link on its right. Pushing every tile on the left of the link $`w` units
rightwards, and paring every tile on its right back by $`w`, again tiles $`R`.
:::

:::proof "lem:int-rect-link-push"
The tiles on either side of the link cut it into consecutive pieces
{uses "lem:int-rect-link-side"}[], so the strip of width $`w` that the tiles on the left sweep out
is exactly the strip that the tiles on the right vacate; no other tile can reach into it, and the
half-open cells of the new family therefore still partition those of $`R`.
:::

:::lemma_ "lem:int-rect-link-exists" (parent := "grp:int-rect") (lean := "IntegerRectangle.ReducibleLink.exists_reducible")
In a tiling with at least one H-tile and at least one V-tile, some link is reducible.
:::

:::proof "lem:int-rect-link-exists"
Suppose not. Then from any H-tile one can step to an H-tile directly above or below across an
H-link, so the H-tiles reach every height of $`R`; and from any V-tile one can step to a V-tile
across a V-link on either side, so the V-tiles reach from the left edge of $`R` to its right edge.
Follow the V-tiles rightwards, carrying the assertion that every H-tile overlapping the current
V-tile in height lies to the right of it. It holds at the left edge, where there is no room on the
left. It survives a step: an H-tile lying on the left of the V-link just crossed can be walked up
and down along H-links to the height of the previous V-tile, staying on the left throughout, since
a V-link blocks every H-link it meets and the H-tiles bordering an H-link do not reach past its
ends — contradicting the assertion for the previous V-tile. But at the right edge of $`R` the
assertion is absurd, since the H-tiles reach that height too.
:::

:::theorem "thm:int-rect-links" (parent := "grp:int-rect") (lean := "IntegerRectangle.ReducibleLink.IntegerRectangleTheorem_ReducibleLink") (proofColor := "#fbcfe8")
A rectangle tiled by rectangles each with an integer side has an integer side.
:::

:::proof "thm:int-rect-links"
Induct on the number of tiles. Degenerate tiles have empty half-open cells and may be discarded.
If every tile has integer width the fg-area for the fractional part horizontally and the identity
vertically vanishes on every tile, hence on $`R`, so $`R` has integer width; likewise if every
tile has integer height. Otherwise some link is reducible {uses "lem:int-rect-link-exists"}[], say
a V-link with only H-tiles on its right; take for $`w` the width of the narrowest of them and push
{uses "lem:int-rect-link-push"}[]. Heights never change, so V-tiles stay V-tiles, and widths change
by the integer $`w`, so H-tiles stay H-tiles; but the narrowest tile on the right is squeezed to
nothing, so the new tiling of $`R` has fewer tiles and the induction hypothesis applies. The three
other ways a link can be reducible are this one read in the mirror image of the tiling, in its
transpose, and in the mirror image of its transpose.
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
instead of an integral, and the additivity is combinatorial rather than measure-theoretic: it holds
for the fg-area built from an arbitrary function, with no regularity at all.

:::lemma_ "lem:int-rect-fgarea" (parent := "grp:int-rect") (lean := "IntegerRectangle.IsTiling.sum_fgArea")
For functions $`f, g : \mathbb{R} \to \mathbb{R}` define the *fg-area* of a rectangle
$`[x_0, x_1] \times [y_0, y_1]` as $`(f(x_1) - f(x_0)) \cdot (g(y_1) - g(y_0))`. If $`T` tiles $`R`
then the fg-areas of the tiles sum to the fg-area of $`R`, for arbitrary $`f` and $`g`.
:::

:::proof "lem:int-rect-fgarea"
The tile edges form a graph; extending its edges across $`R` cuts $`R` into a grid, whose vertical
lines carry the finitely many x-coordinates of vertical tile edges and whose horizontal lines carry
the y-coordinates of horizontal ones. No grid coordinate lies strictly inside an open grid cell, so
a tile covering the centre of a cell has all four edges clear of it and contains the whole cell; by
disjointness of interiors this tile is unique. Conversely the cells assigned to a tile fill out a
full product subdivision of it, because the tile's own edges are grid lines. Summing fg-areas of
cells therefore counts every cell exactly once, tile by tile; over a product subdivision the sum
telescopes in both coordinates to the tile's fg-area, and over the whole grid it telescopes to the
fg-area of $`R`.
:::

:::lemma_ "lem:int-rect-step-engine" (parent := "grp:int-rect") (lean := "IntegerRectangle.StepFunction.dichotomy")
Let $`f, g : \mathbb{R} \to \mathbb{R}` be arbitrary. If $`T` tiles $`R` and every tile has a
vanishing increment of $`f` across its width or of $`g` across its height, then the same dichotomy
holds for $`R`.
:::

:::proof "lem:int-rect-step-engine"
The fg-area of every tile is a product with a vanishing factor, so by additivity of the fg-area
{uses "lem:int-rect-fgarea"}[] the fg-area of $`R` vanishes, and a product of reals vanishes only if
a factor does.
:::

:::theorem "thm:int-rect-step" (parent := "grp:int-rect") (lean := "IntegerRectangle.StepFunction.IntegerRectangleTheorem_StepFunction") (proofColor := "#fbcfe8")
A rectangle tiled by rectangles each with an integer side has an integer side.
:::

:::proof "thm:int-rect-step"
Take $`f = g = \{\cdot\}`, the sawtooth $`\{x\} = x - \lfloor x\rfloor` — the identity minus a
step function. Its increment $`\{b\} - \{a\}` vanishes if and only if $`b - a \in \mathbb{Z}`, so a
tile with an integer side satisfies the hypothesis of the engine
{uses "lem:int-rect-step-engine"}[], which returns a vanishing sawtooth increment for $`R` in one
of the two directions — an integer side. The criterion is an exact "integer difference" statement,
so unlike the checkerboard proof, whose triangle wave is symmetric about the half-integers, this
argument needs no standard-position hypothesis. (The sawtooth increment is also the signed mass of
$`(a, b]` under Lebesgue measure minus the counting measure of the integers, giving an alternative
measure-theoretic route to the additivity.)
:::
