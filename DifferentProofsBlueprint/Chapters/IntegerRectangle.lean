import Verso
import VersoManual
import VersoBlueprint
import DifferentProofsBlueprint.ProofColor
import DifferentProofs.IntegerRectangle.Tiling.Basic
import DifferentProofs.IntegerRectangle.BipartiteGraph
import DifferentProofs.IntegerRectangle.Checkerboard
import DifferentProofs.IntegerRectangle.ComplexIntegral
import DifferentProofs.IntegerRectangle.Tiling.CornerCount
import DifferentProofs.IntegerRectangle.Tiling.Image
import DifferentProofs.IntegerRectangle.CountingSquares
import DifferentProofs.IntegerRectangle.CutSet
import DifferentProofs.IntegerRectangle.Defs
import DifferentProofs.IntegerRectangle.EulerianPath
import DifferentProofs.IntegerRectangle.Tiling.Slice
import DifferentProofs.IntegerRectangle.Polynomials
import DifferentProofs.IntegerRectangle.Primes
import DifferentProofs.IntegerRectangle.RealIntegral
import DifferentProofs.IntegerRectangle.Sperner
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

:::definition "def:int-rect" (parent := "grp:int-rect") (lean := "IntegerRectangleTheorem")
Stan Wagon's theorem (*Fourteen Proofs of a Result About Tiling a Rectangle*, Amer. Math. Monthly
$`94` (1987) 601–617) states: whenever a rectangle is tiled by finitely many rectangles, each of
which has at least one integer side, then the tiled rectangle has at least one integer side. Here a
*tiling* is a covering by axis-parallel rectangles of positive width and height with
pairwise-disjoint interiors.
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

:::theorem "thm:int-rect-complex" (parent := "grp:int-rect") (lean := "IntegerRectangleTheorem_ComplexIntegral") (proofColor := "#fbcfe8")
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

:::theorem "thm:int-rect-real" (parent := "grp:int-rect") (lean := "IntegerRectangleTheorem_RealIntegral") (proofColor := "#fbcfe8")
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

:::theorem "thm:int-rect-checker" (parent := "grp:int-rect") (lean := "IntegerRectangleTheorem_Checkerboard") (proofColor := "#fbcfe8")
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

Wagon's fourth, fifth and sixth proofs each build an auxiliary tiling by moving the lines of the
given one without changing their order, and compare a count or an area over the two tilings. They
rest on three facts about tilings.

:::lemma_ "lem:int-rect-partition" (parent := "grp:int-rect") (lean := "IntegerRectangle.IsTiling.iUnion_toSetIoc")
The half-open cells of the tiles of a tiling — each tile with its left and bottom edges removed —
are pairwise disjoint, and their union is the half-open cell of the tiled rectangle.
:::

:::proof "lem:int-rect-partition"
Disjointness: a point common to two half-open cells moves down-and-left — to the midpoint between
the higher of the two lower-left corners and the point itself — into the interiors of both tiles,
contradicting interior-disjointness. Covering: a point of the ambient half-open cell is approached
from below-left; every such nudge stays in $`R`, hence in some tile, and since there are finitely
many tiles one tile contains nudges arbitrarily close in. That tile is closed, so it contains the
point, and the nudges witness the two strict inequalities of its half-open cell.
:::

:::lemma_ "lem:int-rect-area" (parent := "grp:int-rect") (lean := "IntegerRectangle.IsTiling.sum_area")
The areas of the tiles of a tiling add up to the area of the tiled rectangle.
:::

:::proof "lem:int-rect-area"
The area of a rectangle is the Lebesgue measure of its half-open cell, and the half-open cells of
the tiles partition that of the tiled rectangle {uses "lem:int-rect-partition"}[].
:::

:::lemma_ "lem:int-rect-move-lines" (parent := "grp:int-rect") (lean := "IntegerRectangle.IsTiling.image")
Let $`T` tile $`R`, and move every vertical line $`x = a` of the tiling to $`x = \varphi(a)` and
every horizontal line $`y = b` to $`y = \psi(b)`, by maps $`\varphi` and $`\psi` keeping the order
of the abscissae of the vertical lines and of the ordinates of the horizontal ones. If $`R` does
not collapse, the moved tiles that do not collapse to segments tile the moved $`R`.
:::

:::proof "lem:int-rect-move-lines"
By half-open cells {uses "lem:int-rect-partition"}[]. Pull a point $`z` back to the point whose
abscissa is the leftmost vertical line of the tiling whose image is not to the left of $`z`, or a
point beyond the tiling if there is none, and whose ordinate is the lowest horizontal line whose
image is not below $`z`. Since the moves keep the order of the lines, this point lies in the
half-open cell of a tile, or of $`R`, exactly when $`z` lies in that of its image. So the
half-open cells of the moved tiles are pairwise disjoint and cover the half-open cell of the moved
$`R`, because those of the tiling are and do; a tile collapsed to a segment has an empty half-open
cell and is discarded.
:::

Fourth proof: counting squares (Ruzsa, Gilbert). Place $`R` in standard position and translate
every vertical line of the tiling with a noninteger abscissa $`a` to the half-integer line
$`x = \lfloor a\rfloor + \tfrac12`, and likewise the horizontal lines, the integral lines staying
put. Here the lattice is based at the lower-left corner of $`R`, which replaces the standard
position. The translated tiles tile a translated rectangle all of whose coordinates lie on the
half-unit grid, so every rectangle in it is a union of $`\tfrac12 \times \tfrac12` squares — the
checkerboard cells of the third proof — and the argument is a parity count of those squares.

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
The translated tiles contain, in all, as many half-unit squares as the translated rectangle, and a
translated rectangle contains as many squares as the product of the increments of the two grid
coordinates across it.
:::

:::proof "lem:int-rect-cellcount"
The translation keeps the order of the lines, so the translated tiles tile the translated
rectangle {uses "lem:int-rect-move-lines"}[]. Count the squares by their upper right corners: a
square lies in a rectangle whose edges are grid lines exactly when its upper right corner lies in
the half-open cell of the rectangle, so every square of the translated rectangle lies in exactly
one translated tile {uses "lem:int-rect-partition"}[], and a rectangle whose edges are the grid
lines $`c_0 \le c_1` and $`d_0 \le d_1` half-steps from the corner of $`R` contains
$`(c_1 - c_0)(d_1 - d_0)` squares.
:::

:::theorem "thm:int-rect-counting" (parent := "grp:int-rect") (lean := "IntegerRectangleTheorem_CountingSquares") (proofColor := "#fbcfe8")
A rectangle tiled by rectangles each with an integer side has an integer side.
:::

:::proof "thm:int-rect-counting"
The endpoints of a side of integer length $`n` are $`n` apart, so the translation moves them
equally and the increment of the grid coordinate across that side is $`2n`: every translated tile
contains an even number of squares, and hence {uses "lem:int-rect-cellcount"}[] so does the
translated rectangle. The corner of $`R` has grid coordinate $`0`, so that count is the product of
the grid coordinates of the far edges of $`R`, and one of the two factors is even — which says
{uses "lem:int-rect-cell-parity"}[] that the corresponding side of $`R` has integer length.
(Wagon phrases the last step as a contradiction: a translated rectangle with no integer side has
both sides equal to half an odd integer, hence an odd number of squares.)
:::

Fifth proof: polynomials (Douady). With the lattices again based at the lower-left corner of $`R`
and a parameter $`t`, move a vertical line of the tiling by $`t` when its abscissa is off the
lattice and a horizontal line by $`t` when its ordinate is, leaving the lattice lines fixed. For
$`t` smaller than the least gap between the lines of the tiling the moved lines keep their order,
and the areas of the moved rectangles are polynomials in $`t`.

:::lemma_ "lem:int-rect-poly-sum" (parent := "grp:int-rect") (lean := "IntegerRectangle.Polynomials.sum_areaPoly")
As a polynomial in $`t`, the area of the moved $`R` is the sum of the areas of the moved tiles.
:::

:::proof "lem:int-rect-poly-sum"
For $`t` in an interval $`[0, \delta)` the moved lines keep their order, so the moved tiles tile
the moved rectangle {uses "lem:int-rect-move-lines"}[] and the area of the moved rectangle is the
sum of theirs {uses "lem:int-rect-area"}[]. The two polynomials therefore agree at infinitely many
points, so they are equal.
:::

:::theorem "thm:int-rect-polynomials" (parent := "grp:int-rect") (lean := "IntegerRectangleTheorem_Polynomials") (proofColor := "#fbcfe8")
A rectangle tiled by rectangles each with an integer side has an integer side.
:::

:::proof "thm:int-rect-polynomials"
Let $`\varepsilon_x(u)` be $`0` when $`u - R_x \in \mathbb{Z}` and $`1` otherwise, and similarly
define $`\varepsilon_y`, so that the lines move by $`\varphi_t(u) = u + t\varepsilon_x(u)` and
$`\psi_t(v) = v + t\varepsilon_y(v)`. The area of a moved rectangle $`S` is the value at $`t` of
the polynomial $`P_S = (\Delta\varepsilon_x X + w)(\Delta\varepsilon_y X + h)`, with $`w, h` the
sides of $`S` and $`\Delta\varepsilon` the indicator increments across them. If a tile has an
integer side, the two endpoints of that side have the same indicator, the corresponding factor is
constant, and the quadratic coefficient vanishes: the area of the moved tile is linear or constant
in $`t`, and hence {uses "lem:int-rect-poly-sum"}[] so is the area of the moved $`R`. If neither
side of $`R` is an integer, each lower endpoint has indicator $`0` and each upper endpoint $`1`, so
the moved $`R` is $`(w + t) \times (h + t)` and its area has quadratic coefficient $`1`, a
contradiction.
:::

Sixth proof: prime numbers (Robinson). For a prime $`p`, scale the tiling by $`p` and replace every
tile corner $`(x, y)` of the scaled tiling by $`(\lfloor x\rfloor, \lfloor y\rfloor)`. This moves
the vertical line $`x = a` to $`x = \lfloor pa\rfloor` and the horizontal line $`y = b` to
$`y = \lfloor pb\rfloor`, keeping their order, so the rounded tiles tile the rounded rectangle, an
integer-sided rectangle tiled by integer-sided rectangles; a tile narrower or lower than $`1/p` may
collapse to a segment and drop out.

:::lemma_ "lem:int-rect-round" (parent := "grp:int-rect") (lean := "IntegerRectangle.Primes.dvd_area_round")
If every tile has an integer side and the rounded rectangle does not collapse, its area is a
multiple of $`p`.
:::

:::proof "lem:int-rect-round"
A tile side of integer length $`n` rounds to one of length
$`\lfloor p x_0 + pn\rfloor - \lfloor p x_0\rfloor = pn`, so the area of every rounded tile is a
multiple of $`p`, and the area of the rounded rectangle is the sum of these areas
{uses "lem:int-rect-move-lines"}[] {uses "lem:int-rect-area"}[].
:::

:::lemma_ "lem:int-rect-near" (parent := "grp:int-rect") (lean := "IntegerRectangle.Primes.exists_side_near_int")
If every tile has an integer side, then for every prime $`p` the width or the height of $`R` is
within $`1/p` of an integer.
:::

:::proof "lem:int-rect-near"
The sides of the rounded rectangle are integers that differ from those of the scaled-up rectangle
by less than $`1`. If one of them is $`0`, the corresponding side of $`R` is shorter than $`1/p`.
Otherwise the area of the rounded rectangle is a multiple of $`p` {uses "lem:int-rect-round"}[],
and $`p` being prime, so is one of its sides, say
$`\lfloor p x_1\rfloor - \lfloor p x_0\rfloor = pm`; then $`p(x_1 - x_0) - pm` is a difference of
two floor remainders, each in $`[0,1)`, so $`|`width$` - m| < 1/p`.
:::

:::theorem "thm:int-rect-primes" (parent := "grp:int-rect") (lean := "IntegerRectangleTheorem_Primes") (proofColor := "#fbcfe8")
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

The formalization builds $`\Gamma` as a multigraph through its half-edges, or darts, a dart being a
tile together with one of its four corners. Each tile contributes its two horizontal sides if its
width is an integer and its two vertical sides otherwise, and the two darts of such a side are its
two ends. Two tiles of the same integer width stacked on each other share a side, which is then a
double edge of $`\Gamma`. The degree of a vertex is the number of darts at it, which is the number
of tiles having it as a corner.

Of the degrees only the parity is ever used, and Wagon reads it off the local picture of how the
tiles fit together around a point, which the eighth proof shares. Nor is the walk built step by
step: what makes it reach a second corner of $`R` is the handshake lemma, which stands in for it
here since mathlib's multigraphs have no walks yet.

:::lemma_ "lem:int-rect-local-picture" (parent := "grp:int-rect") (lean := "IntegerRectangle.IsTiling.sum_cornerCount_eq")
Let $`T` tile $`R`. At a corner of $`R` the tiles have exactly one corner in all, and at any other
point of the plane none, two or four. (Each rectangle has four corners, counted with
multiplicity.)
:::

:::proof "lem:int-rect-local-picture"
Look at the four quadrants at the point. A tile containing the point fills one of them if the
point is a corner of the tile, two if the point lies inside one of its edges, and four if it lies
inside the tile. Each quadrant inside $`R` is filled by exactly one tile, so the numbers of
quadrants the tiles fill add up to the number of quadrants inside $`R`: four at a point inside
$`R`, two at a point inside one of its edges, one at a corner, and none outside $`R`. The tiles
having the point as a corner fill one quadrant each and the other tiles an even number, so the
former are at most as many as the quadrants inside $`R`, and as many up to an even number.
:::

:::lemma_ "lem:handshake" (parent := "grp:int-rect") (lean := "HalfEdgePairing.exists_ne_reflTransGen_of_odd")
In a finite multigraph, a vertex of odd degree is joined by a walk to another vertex of odd
degree.
:::

:::proof "lem:handshake"
The vertices that walks from it reach form a union of connected components, so every edge at one
of them has both of its ends among them, and their degrees add up to twice the number of these
edges. That sum is even, so besides the degree of the starting vertex another of its terms is odd.
:::

:::lemma_ "lem:int-rect-euler-walk" (parent := "grp:int-rect") (lean := "IntegerRectangle.EulerianPath.exists_reachable_corner")
Let $`T` tile $`R`. Then some walk in $`\Gamma` leads from the lower-left corner of $`R` to another
corner of $`R`.
:::

:::proof "lem:int-rect-euler-walk"
The degree of a vertex is the number of tiles having it as a corner, so by the local picture
{uses "lem:int-rect-local-picture"}[] the vertices of odd degree are the corners of $`R`. The
lower-left corner is one of them, and by the handshake lemma {uses "lem:handshake"}[] a walk leads
from it to another vertex of odd degree, which is another corner of $`R`.
:::

:::theorem "thm:int-rect-euler" (parent := "grp:int-rect") (lean := "IntegerRectangleTheorem_EulerianPath") (proofColor := "#fbcfe8")
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
position, let $`S` be the set of corners of tiles having both coordinates integers, and form the
bipartite graph on $`S` and the set of tiles that joins each point of $`S` to all the tiles of which
it is a corner. Its edges are counted in the two possible ways. The formalization builds this
graph as a mathlib multigraph whose edges are the incidences of the tiles with their corners, and
cuts $`S` out by the lattice through the lower-left corner of $`R`, which replaces the standard
position.

:::lemma_ "lem:graph-bipartite-count" (parent := "grp:int-rect") (lean := "Graph.IsBipartiteWith.sum_ncard_incidenceSet_eq")
In a bipartite multigraph with finitely many edges, the numbers of edges at the vertices of one
part add up to the same total as the numbers of edges at the vertices of the other part.
:::

:::proof "lem:graph-bipartite-count"
Every edge has exactly one end in each part, so either sum counts every edge exactly once.
:::

:::lemma_ "lem:int-rect-bipartite-tile" (parent := "grp:int-rect") (lean := "IntegerRectangle.BipartiteGraph.even_ncard_incidenceSet_inr")
A tile with an integer side has $`0`, $`2` or $`4` corners in $`S`, so evenly many edges.
:::

:::proof "lem:int-rect-bipartite-tile"
The two ends of a side of integer length are both on the lattice or neither is, so the corners of
the tile on the lattice come in pairs, the two ends of the same side.
:::

:::lemma_ "lem:int-rect-bipartite-odd" (parent := "grp:int-rect") (lean := "IntegerRectangle.BipartiteGraph.exists_odd")
Let $`T` tile $`R` by tiles with an integer side. Then some point of $`S` other than the
lower-left corner of $`R` lies on an odd number of tiles.
:::

:::proof "lem:int-rect-bipartite-odd"
Counted from the side of the tiles, the edges of the graph are evenly many
{uses "lem:int-rect-bipartite-tile"}[], so by the count from the other side
{uses "lem:graph-bipartite-count"}[] the numbers of tiles the points of $`S` lie on have an even
sum. The lower-left corner of $`R` lies on exactly one tile {uses "lem:int-rect-local-picture"}[],
so it is in $`S`, and the numbers for the other points of $`S` have an odd sum.
:::

:::theorem "thm:int-rect-bipartite" (parent := "grp:int-rect") (lean := "IntegerRectangleTheorem_BipartiteGraph") (proofColor := "#fbcfe8")
A rectangle tiled by rectangles each with an integer side has an integer side.
:::

:::proof "thm:int-rect-bipartite"
Take a point of $`S` other than the lower-left corner of $`R` lying on an odd number of tiles
{uses "lem:int-rect-bipartite-odd"}[]. A point that is not a corner of $`R` lies on none, two or
four tiles {uses "lem:int-rect-local-picture"}[], so this one is another corner of $`R`, and being
on the lattice through the lower-left corner it is an integer width or height away from it.
:::

The two inductive proofs that follow treat as immediate the case of a tiling all of whose tiles
have integer width, or all of whose tiles have integer height. It is settled by slicing the tiling
along a line, the geometric ingredient of the twelfth proof below.

:::lemma_ "lem:int-rect-slice" (parent := "grp:int-rect") (lean := "IntegerRectangle.widthSum_slice")
Let $`T` tile $`R` and let $`t` be a height between the bottom and the top of $`R` avoiding every
horizontal tile edge. Then the widths of the tiles crossed by the line $`y = t` add up to the width
of $`R`.
:::

:::proof "lem:int-rect-slice"
Length along the line $`y = t` is a measure on the plane, so it adds up over the half-open cells of
the tiles, which partition that of $`R` {uses "lem:int-rect-partition"}[]. Because $`t` avoids the
horizontal edges, the line meets the half-open cell of a tile, in an interval as long as the tile
is wide, exactly when it crosses the tile; and it meets the half-open cell of $`R` in an interval
of the full width, since it is not the bottom edge of $`R`: the tile containing the point of the
left edge of $`R` at height $`t` reaches below it.
:::

:::lemma_ "lem:int-rect-all-h" (parent := "grp:int-rect") (lean := "IntegerRectangle.intWidth_of_forall, IntegerRectangle.intHeight_of_forall")
If every tile of a tiling of $`R` has integer width, then so has $`R`; and likewise for heights.
:::

:::proof "lem:int-rect-all-h"
A horizontal line through $`R` avoiding the finitely many heights of horizontal tile edges crosses
tiles whose widths add up to the width of $`R` {uses "lem:int-rect-slice"}[], and these widths are
integers. For heights, transpose the tiling.
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
Cut each tile into unit pieces along a side of integer length, of which it has at least one, and
which is at least one unit long since the tile has positive width and height. The half-open cells of
the pieces of a tile partition its own, so the cells of all the pieces still partition those of
$`R`.
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
since the staircase is a wall {uses "lem:int-rect-staircase"}[] the same alternative holds at all of
that tile's heights. A point of the shrunken rectangle left of the strip comes from the point itself
and one to its right from its translate one unit rightwards, so the half-open cells of the pieces
partition those of the shrunken rectangle. Pieces of zero width have empty cells and are discarded;
a tile inside the strip leaves only such pieces.
:::

:::theorem "thm:int-rect-induction" (parent := "grp:int-rect") (lean := "IntegerRectangleTheorem_Staircase") (proofColor := "#fbcfe8")
A rectangle tiled by rectangles each with an integer side has an integer side.
:::

:::proof "thm:int-rect-induction"
Normalize the tiling {uses "lem:int-rect-normalize"}[] and induct on the number of its H-tiles.
With no H-tile every tile has integer height, hence so does $`R`
{uses "lem:int-rect-all-h"}[]. Otherwise grow the staircase
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
rightwards, and paring every tile on its right back by $`w`, again tiles $`R`, once the tiles
squeezed to zero width are discarded.
:::

:::proof "lem:int-rect-link-push"
The tiles on either side of the link cut it into consecutive pieces
{uses "lem:int-rect-link-side"}[], so the strip of width $`w` that the tiles on the left sweep out
is exactly the strip that the tiles on the right vacate; no other tile can reach into it, and the
half-open cells of the new family therefore still partition those of $`R`. A tile squeezed to zero
width has an empty cell, so discarding it changes nothing.
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

:::theorem "thm:int-rect-links" (parent := "grp:int-rect") (lean := "IntegerRectangleTheorem_ReducibleLink") (proofColor := "#fbcfe8")
A rectangle tiled by rectangles each with an integer side has an integer side.
:::

:::proof "thm:int-rect-links"
Induct on the number of tiles. If every tile has integer width then so has $`R`, and if every tile
has integer height then so has $`R` {uses "lem:int-rect-all-h"}[]. Otherwise some link is reducible
{uses "lem:int-rect-link-exists"}[], say a V-link with only H-tiles on its right; take for $`w` the
width of the narrowest of them and push {uses "lem:int-rect-link-push"}[]. Heights never change, so
V-tiles stay V-tiles, and widths change by the integer $`w`, so H-tiles stay H-tiles; but the
narrowest tile on the right is squeezed to nothing, so the new tiling of $`R` has fewer tiles and
the induction hypothesis applies. The three other ways a link can be reducible are this one read in
the mirror image of the tiling, in its transpose, and in the mirror image of its transpose.
:::

Eleventh proof: a minimal cut-set (Paul Seymour, Bell Communications Research). Form a graph
$`\Gamma`: its vertices are the horizontal segments of the tiling, and its edges are the tiles —
each tile joins the segment carrying its bottom edge to the segment carrying its top edge — plus
one exterior edge running around the outside of $`R` from its bottom edge to its top edge.
Drawing each edge up the vertical bisector of its tile embeds $`\Gamma` in the plane, and the
faces of the embedding are the V-links of the tenth proof together with the two outer faces on
either side of the exterior edge. Call a tile a V-tile when its height is an integer, an H-tile
(of integer width) otherwise, and let $`S` collect the H-tile edges together with the exterior
edge. If deleting $`S` leaves the bottom of $`R` connected to its top, a path of V-tiles climbs
from bottom to top and the height of $`R` is an integer. Otherwise Seymour passes to a minimal
$`S' \subseteq S` cutting the bottom off from the top and invokes a well-known theorem for planar
graphs: the duals of its edges form a cycle in the dual graph $`\Gamma^*`. The cycle must use the
dual of the exterior edge — that edge alone joins bottom to top — and deleting it leaves a dual
path from the left outer face to the right one whose steps cross H-tiles, so the width of $`R` is
an integer.

The formalization builds the embedding as the rotation system the drawing determines: the darts
are the two ends of each edge, and the rotation turns each dart counterclockwise round its
segment. A rotation system is planar when it is connected and its Euler characteristic is two,
and the well-known theorem is proved for planar rotation systems in general.

:::theorem "thm:planar-bond-cycle" (parent := "grp:int-rect") (lean := "CombinatorialMap.IsPlanar.isCycle_of_isBond")
In a planar combinatorial map, the edges of a bond of the graph, a minimal nonempty edge cut, form
a cycle of the dual graph.
:::

:::proof "thm:planar-bond-cycle"
Over $`\mathbb{Z}/2`, the edge cuts of the graph form the image of its coboundary, and the edge
sets meeting every face evenly form the kernel of the boundary of the dual graph. The image lies
in the kernel, since walking round a face crosses an edge cut an even number of times, and the
two have dimensions $`\#V - 1` and $`\#E - \#F + 1`, which Euler's formula makes equal. So a bond
is a minimal nonempty edge set meeting every face evenly. Such a set is a cycle: the rest of it
joins the two ends of any of its edges, by the handshake lemma {uses "lem:handshake"}[], since
those two ends are the only faces it meets an odd number of times, and a shortest such path closes
up with the edge to a cycle which, being even, is all of it.
:::

:::lemma_ "lem:int-rect-cut-vertices" (parent := "grp:int-rect") (lean := "IntegerRectangle.CutSet.sameCycle_of_vert_eq")
The vertices of the rotation system are the horizontal segments: the darts at a segment form one
orbit of the rotation.
:::

:::proof "lem:int-rect-cut-vertices"
Along the tiles below a segment the rotation passes from each tile to the next one on the right
for as long as the segment goes on, then round the right end of the segment to the tiles above
it, along which it moves left, and round the left end back below.
:::

:::lemma_ "lem:int-rect-cut-faces" (parent := "grp:int-rect") (lean := "IntegerRectangle.CutSet.sameCycle_of_faceOf_eq")
The faces of the rotation system are the V-links and the two outer faces.
:::

:::proof "lem:int-rect-cut-faces"
Following a dart to the other end of its edge and turning there stays on the V-link carrying the
corresponding vertical edge of the tile, because the corners the rotation turns round inside a
V-link are not blocked. Round a V-link the face permutation climbs its left side tile by tile
{uses "lem:int-rect-link-side"}[], crosses its top end to the right side, and descends that side;
round the outer faces it runs along the left and right edges of $`R` and the exterior edge.
:::

:::lemma_ "lem:int-rect-cut-planar" (parent := "grp:int-rect") (lean := "IntegerRectangle.CutSet.seymourMap_isPlanar")
The embedding of Seymour's graph is planar.
:::

:::proof "lem:int-rect-cut-planar"
The graph is connected, every segment being joined to the bottom of $`R` through the tiles
below it. An edge set meeting every face evenly is an edge cut: colour each segment by the parity
of the tiles of the set stacked under it. The colour does not depend on where along the segment it
is read, because the tiles a moving column gains and loses abut V-links lying wholly below the
segment, each met evenly {uses "lem:int-rect-cut-faces"}[]; crossing a tile changes the colour
exactly when the tile is in the set, and crossing the exterior edge exactly when it is, by the
parity at the left outer face. So the cut space of the graph and the cycle space of the dual
coincide, and comparing their dimensions is Euler's formula.
:::

:::lemma_ "lem:int-rect-cut-steps" (parent := "grp:int-rect") (lean := "IntegerRectangle.CutSet.int_sub_y₀_of_reflTransGen")
With $`S` deleted, every vertex reached from the bottom of $`R` sits an integer distance above
it.
:::

:::proof "lem:int-rect-cut-steps"
Each step of the path crosses a V-tile, up or down, changing the height by an integer.
:::

:::lemma_ "lem:int-rect-cut-path" (parent := "grp:int-rect") (lean := "IntegerRectangle.CutSet.intWidth_of_not_reflTransGen")
If deleting $`S` cuts the bottom of $`R` off from its top, the width of $`R` is an integer.
:::

:::proof "lem:int-rect-cut-path"
A minimal $`S' \subseteq S` cutting the bottom off from the top is a bond of $`\Gamma`, so by
planarity {uses "lem:int-rect-cut-planar"}[] and planar duality {uses "thm:planar-bond-cycle"}[]
its edges form a cycle of $`\Gamma^*`, whose vertices are the V-links and the outer faces
{uses "lem:int-rect-cut-faces"}[]. The cycle passes through the dual of the exterior edge, which
moves the abscissa from one side of $`R` to the other. Every other step crosses an H-tile and
moves the abscissa by its integer width, and round the cycle the abscissa comes back, so the
width of $`R` is an integer.
:::

:::theorem "thm:int-rect-cut" (parent := "grp:int-rect") (lean := "IntegerRectangleTheorem_CutSet") (proofColor := "#fbcfe8")
A rectangle tiled by rectangles each with an integer side has an integer side.
:::

:::proof "thm:int-rect-cut"
Form Seymour's graph {uses "lem:int-rect-cut-vertices"}[] and delete $`S`. If the top of $`R` is
still reachable from the bottom, the height of $`R` is an integer {uses "lem:int-rect-cut-steps"}[];
otherwise the width is {uses "lem:int-rect-cut-path"}[].
:::

Twelfth proof: a sweep line (Bachman–Yannakakis). This one does not use the analytic engine above.
Instead of an integral it propagates a conserved quantity upward through the tiling, and the only
geometry it needs is what a horizontal cut of a tiling looks like — the slice lemma of the ninth
and tenth proofs.

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

:::theorem "thm:int-rect-sweep" (parent := "grp:int-rect") (lean := "IntegerRectangleTheorem_SweepLine") (proofColor := "#fbcfe8")
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

Thirteenth proof: step functions (Hochster–Máté). Take the bottom and left edges of $`R` for the
axes, which replaces the standard position, and let $`\Gamma` be the graph whose vertices are the
points of the x-axis at which some tile has a vertical edge and the points of the y-axis at which
some tile has a horizontal edge; two vertices on the x-axis are joined when an H-tile spans the
interval between them, and two on the y-axis when a V-tile does. Number the connected components
of $`\Gamma` by distinct numbers in an arbitrary way, and let $`f` be the step function whose value
on the interval between consecutive vertices $`x_i < x_{i+1}` of the x-axis is the number of the
component of $`x_{i+1}` less that of $`x_i`, and $`g` its counterpart on the y-axis. The
formalization builds $`\Gamma` as a mathlib simple graph.

:::lemma_ "lem:int-rect-grid" (parent := "grp:int-rect") (lean := "IntegerRectangle.Grid.cellTile_eq_iff")
Extend the edges of the tiles of a tiling across $`R` to a grid. Every open grid cell lies in exactly
one tile, and the cells in a tile form the product of two intervals of grid indices.
:::

:::proof "lem:int-rect-grid"
No grid coordinate lies strictly inside an open grid cell, so a tile covering the centre of a cell
has all four edges clear of it and contains the whole cell; by disjointness of interiors this tile
is unique. Conversely the cells assigned to a tile fill out a full product subdivision of it,
because the tile's own edges are grid lines.
:::

:::lemma_ "lem:int-rect-fgarea" (parent := "grp:int-rect") (lean := "IntegerRectangle.StepFunction.sum_fgArea")
For functions $`F, G : \mathbb{R} \to \mathbb{R}` define the *fg-area* of a rectangle
$`[x_0, x_1] \times [y_0, y_1]` as $`(F(x_1) - F(x_0)) \cdot (G(y_1) - G(y_0))`. If $`T` tiles $`R`
then the fg-areas of the tiles sum to the fg-area of $`R`, for arbitrary $`F` and $`G`.
:::

:::proof "lem:int-rect-fgarea"
Refine the tiling into its grid {uses "lem:int-rect-grid"}[]. Summing the fg-areas of the grid
cells counts every cell exactly once, tile by tile; over the cells of a tile, a product of index
intervals, the sum telescopes in both coordinates to the fg-area of the tile, and over the whole
grid to the fg-area of $`R`.
:::

:::lemma_ "lem:int-rect-step-reach" (parent := "grp:int-rect") (lean := "IntegerRectangle.StepFunction.reachable")
The lower-left corner of $`R` lies in the same component of $`\Gamma` as its lower-right corner or
as its upper-left corner.
:::

:::proof "lem:int-rect-step-reach"
Let $`F` give each vertex of the x-axis the number of its component, and $`G` likewise on the
y-axis, so that the value of $`f` on the interval between two consecutive vertices is the increment
of $`F` across it, and the value of $`f(x) g(y)` on a grid rectangle is its fg-area for $`F` and
$`G`. Over the grid rectangles in a tile these values add up to the fg-area of the tile, which
vanishes: the width of an H-tile spans an edge of $`\Gamma`, whose ends are in the same component,
and so does the height of a V-tile. By the grid refinement {uses "lem:int-rect-fgarea"}[] the
fg-area of $`R`, the product of the increments of $`F` across its width and of $`G` across its
height, vanishes too, and the numbers of distinct components being distinct, the corner of $`R` is
in the same component as one of the other two.
:::

:::theorem "thm:int-rect-step" (parent := "grp:int-rect") (lean := "IntegerRectangleTheorem_StepFunction") (proofColor := "#fbcfe8")
A rectangle tiled by rectangles each with an integer side has an integer side.
:::

:::proof "thm:int-rect-step"
Every edge of $`\Gamma` spans a side of a tile of integer length, so two vertices in the same
component are an integer apart, and by {uses "lem:int-rect-step-reach"}[] the width or the height
of $`R` is an integer.
:::

Fourteenth proof: Sperner's lemma (Schmerl). Cut every tile in two along a diagonal and label each
vertex of the resulting figure by which of its coordinates are integers; a variation of Sperner's
lemma then makes the number of triangles carrying all three labels odd, and no tile with an
integer side has such a triangle. Following Mead, whose lemma this is, an edge is called
*complete* when its endpoints carry the first two labels, and a triangle is complete when its
vertices carry all three. The labelling is based at the corner of $`R` rather than at the origin,
so the tiling is never translated.

:::lemma_ "lem:int-rect-sperner-local" (parent := "grp:int-rect") (lean := "IntegerRectangle.Sperner.completeEdge_sum_eq_one_iff")
Label points $`A`, $`B` or $`C`, and call an edge *complete* when its endpoints are labelled $`A`
and $`B`. Counting modulo $`2`, the three sides of a triangle carry an odd number of complete
edges exactly when its three vertices carry three different labels.
:::

:::proof "lem:int-rect-sperner-local"
A finite check of the $`27` labellings of an ordered triple.
:::

:::lemma_ "lem:sperner-1d" (parent := "grp:int-rect") (lean := "IntegerRectangle.Sperner.odd_card_completeEdges_iff")
Sperner's lemma in dimension one: a two-colouring of the points subdividing a segment has an odd
number of complete edges exactly when the two ends of the segment are coloured differently.
:::

:::proof "lem:sperner-1d"
Modulo $`2` the colour increments along the segment telescope, so their sum is the sum of the two
ends; and an increment is $`1` exactly on a complete edge, so that sum counts the complete edges.
The telescoped identity is the form the application below uses.
:::

:::lemma_ "lem:int-rect-sperner-side" (parent := "grp:int-rect") (lean := "IntegerRectangle.Sperner.sum_segComplete")
Label $`(x, y)` by $`A` if $`x` differs from the abscissa of the corner of $`R` by an integer, by
$`B` if it does not but $`y` differs from the ordinate by an integer, and by $`C` otherwise. Then
the complete edges among the grid segments composing a horizontal side sum, modulo $`2`, to the
indicator of the side's own two endpoints.
:::

:::proof "lem:int-rect-sperner-side"
This is the point of the geometric labelling, and what lets the argument run on a figure that is
not a triangulation in the usual sense: a corner of one tile may lie inside an edge of another, so
a side of a triangle carries however many vertices its neighbours put there, and its number of
complete edges is not determined by its endpoints. Its parity is. Along a horizontal segment the
ordinate is constant, so at an integer height the labels are $`A` and $`B` according to the
integrality of the abscissa, and at any other height they are $`A` and $`C` and no edge is
complete; in the first case a complete edge records a change in the integrality of the abscissa,
and a sequence has an odd number of changes exactly when its two ends differ
{uses "lem:sperner-1d"}[]. Along a vertical segment the abscissa is constant, so either every
point is labelled $`A` or none is, and no edge is ever complete.
:::

:::lemma_ "lem:int-rect-sperner-tile" (parent := "grp:int-rect") (lean := "IntegerRectangle.Sperner.not_isCompleteTriangle")
Neither of the two triangles of a tile with an integer side is complete.
:::

:::proof "lem:int-rect-sperner-tile"
If the width of the tile is an integer, its left and right edges have abscissae differing by an
integer, so the two ends of each of its horizontal sides carry the same label; if the height is an
integer, the two ends of each of its vertical sides do. Either way each of the two triangles has
two vertices with a common label, hence not three different ones.
:::

:::lemma_ "lem:int-rect-sperner-count" (parent := "grp:int-rect") (lean := "IntegerRectangle.Sperner.sum_tile_edges")
Summed over all the triangles, the number of complete edges on their sides equals, modulo $`2`,
the number along the bottom and top edges of $`R`.
:::

:::proof "lem:int-rect-sperner-count"
The diagonal of a tile is a side of both of its triangles, so it is counted twice and cancels, and
its vertical sides carry no complete edge {uses "lem:int-rect-sperner-side"}[]; what is left of a
tile is the complete edges on its bottom and top edges. Refine the tiling to its grid: every open
grid cell lies in a unique tile {uses "lem:int-rect-grid"}[], so along a fixed column of cells a
horizontal grid segment strictly inside $`R` either has the same tile above and below it, and is
interior to that tile and counted by neither of its triangles, or has different tiles, and is then
the top edge of the lower and the bottom edge of the upper and counted exactly twice. Everything
in the interior of the column therefore cancels, leaving the segment at the bottom of the column
and the one at the top; summing over the columns leaves the bottom and top edges of $`R`.
:::

:::lemma_ "lem:int-rect-sperner-odd" (parent := "grp:int-rect") (lean := "IntegerRectangle.Sperner.odd_card_completeTriangles")
*The variation of Sperner's lemma, as Wagon uses it.* If neither side of $`R` is an integer,
the number of complete triangles is odd.
:::

:::proof "lem:int-rect-sperner-odd"
Each triangle carries an odd number of complete edges exactly when it is itself complete
{uses "lem:int-rect-sperner-local"}[], so modulo $`2` the number of complete triangles is the
total number of complete edges over all the triangles, which is the number along the bottom and
top edges of $`R` {uses "lem:int-rect-sperner-count"}[]. The top edge is at a height differing
from the bottom by the height of $`R`, not an integer, so it carries none. The bottom edge runs
at an integer height from the corner of $`R`, labelled $`A`, to its lower-right corner, labelled
$`B` because the width of $`R` is not an integer — so it carries a single one
{uses "lem:int-rect-sperner-side"}[]. The total is therefore odd.
:::

:::theorem "thm:int-rect-sperner" (parent := "grp:int-rect") (lean := "IntegerRectangleTheorem_Sperner") (proofColor := "#fbcfe8")
A rectangle tiled by rectangles each with an integer side has an integer side.
:::

:::proof "thm:int-rect-sperner"
Suppose neither side of $`R` is an integer. Then the number of complete triangles is odd
{uses "lem:int-rect-sperner-odd"}[], and in particular there is one. But every tile has an integer
side, so neither of its triangles is complete {uses "lem:int-rect-sperner-tile"}[] — a
contradiction.
:::
