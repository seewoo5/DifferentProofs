import Verso
import VersoManual
import VersoBlueprint
import DifferentProofsBlueprint.ProofColor
import DifferentProofs.SumOfTwoSquares.Basic
import DifferentProofs.SumOfTwoSquares.Defs
import DifferentProofs.SumOfTwoSquares.Jacobi
import DifferentProofs.SumOfTwoSquares.QuadraticReciprocity
import DifferentProofs.SumOfTwoSquares.Wilson
import DifferentProofs.SumOfTwoSquares.Zagier

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option linter.style.longLine false

#doc (Manual) "Sum of Two Squares" =>

:::group "grp:sos"
Fermat's theorem on sums of two squares.
:::

:::definition "def:sos" (parent := "grp:sos") (lean := "FermatSumOfTwoSquares")
Fermat's theorem on sums of two squares (Fermat's Christmas theorem) states that every prime
$`p` with $`p \equiv 1 \pmod 4` can be written as $`p = a^2 + b^2` with $`a, b \in \mathbb{N}`.
:::

Two of the proofs below reduce the theorem to the same elementary descent: once $`-1` is known
to be a square modulo $`p`, a pigeonhole argument recovers the two squares. They differ only in
how they exhibit a square root of $`-1`.

:::lemma_ "lem:sos-thue" (parent := "grp:sos") (lean := "sq_add_sq_of_isSquare_neg_one")
Thue's descent: if $`-1` is a square modulo a prime $`p`, then $`p = a^2 + b^2` for some
natural numbers $`a, b`.
:::

:::proof "lem:sos-thue"
Fix $`u` with $`u^2 \equiv -1 \pmod p` and set $`r = \lfloor \sqrt p \rfloor`. The
$`(r+1)^2 > p` pairs $`(s, t)` with $`0 \le s, t \le r` cannot map injectively into
$`\mathbb{Z}/p\mathbb{Z}` under $`(s, t) \mapsto s - u t`, so two distinct pairs collide. Their
difference $`(a, b)` satisfies $`a \equiv u b \pmod p` with $`|a|, |b| \le r` and
$`(a, b) \ne (0, 0)`. Then $`a^2 + b^2 \equiv u^2 b^2 + b^2 \equiv 0 \pmod p`, while
$`0 < a^2 + b^2 \le 2 r^2 < 2 p`, forcing $`a^2 + b^2 = p`.
:::

First proof: quadratic reciprocity.

:::theorem "thm:sos-qr" (parent := "grp:sos") (lean := "FermatSumOfTwoSquares_QuadraticReciprocity") (proofColor := "#fde68a")
Every prime $`p \equiv 1 \pmod 4` is a sum of two squares.
:::

:::proof "thm:sos-qr"
The first supplement to quadratic reciprocity — equivalently Euler's criterion for the quartic
character $`\chi_4` — says that $`-1` is a square modulo an odd prime $`p` iff
$`p \not\equiv 3 \pmod 4`. This holds for $`p \equiv 1 \pmod 4`, so the descent
{uses "lem:sos-thue"}[] gives $`p = a^2 + b^2`.
:::

Second proof: Wilson's theorem.

:::theorem "thm:sos-wilson" (parent := "grp:sos") (lean := "FermatSumOfTwoSquares_Wilson") (proofColor := "#fde68a")
Every prime $`p \equiv 1 \pmod 4` is a sum of two squares.
:::

:::proof "thm:sos-wilson"
Wilson's theorem gives $`(p-1)! \equiv -1 \pmod p`. Pairing each $`k` with $`p - k` rewrites
$`(p-1)! \equiv (-1)^{(p-1)/2}\bigl(((p-1)/2)!\bigr)^2 \pmod p`. Since $`p \equiv 1 \pmod 4`, the
exponent $`(p-1)/2` is even, so $`\bigl(((p-1)/2)!\bigr)^2 \equiv -1 \pmod p` exhibits $`-1` as a
square, and the descent {uses "lem:sos-thue"}[] gives $`p = a^2 + b^2`.
:::

Third proof: Zagier's "one-sentence" involution proof.

:::theorem "thm:sos-zagier" (parent := "grp:sos") (lean := "SumOfTwoSquares.Zagier.FermatSumOfTwoSquares_Zagier") (proofColor := "#fde68a")
Every prime $`p \equiv 1 \pmod 4` is a sum of two squares.
:::

:::proof "thm:sos-zagier"
Consider the finite set $`S = \{(x, y, z) \mid x, y, z > 0,\ x^2 + 4yz = p\}`. The windmill
involution sends $`(x, y, z)` to $`(x + 2z,\ z,\ y - x - z)` when $`x < y - z`, to
$`(2y - x,\ y,\ x - y + z)` when $`y - z < x < 2y`, and to $`(x - 2y,\ x - y + z,\ y)` when
$`x > 2y`; on $`S` the boundary cases $`x = y - z` and $`x = 2y` are impossible because $`p` is
prime. It has exactly one fixed point (namely $`(1, 1, (p-1)/4)`), so $`|S|` is odd. Therefore the
simple involution $`(x, y, z) \mapsto (x, z, y)` must also have a fixed point $`(x, y, y)`, giving
$`x^2 + 4y^2 = p`, i.e. $`p = x^2 + (2y)^2`.
:::

Fourth proof: Alpoge's proof via Jacobi sums.

:::theorem "thm:sos-jacobi" (parent := "grp:sos") (lean := "SumOfTwoSquares.Jacobi.FermatSumOfTwoSquares_Jacobi") (proofColor := "#fde68a")
Every prime $`p \equiv 1 \pmod 4` is a sum of two squares.
:::

:::proof "thm:sos-jacobi"
Let $`\chi_4` be a multiplicative character of $`\mathbb{Z}/p\mathbb{Z}` of order $`4` (it exists
because $`4 \mid p - 1`), taking values in the fourth roots of unity $`\mu_4 \subseteq \mathbb{C}`.
The Jacobi sum $`J = \sum_x \chi_4(x)\,\chi_4(1 - x)` then lies in $`\mathbb{Z}[i]`. Because
$`\chi_4` and $`\chi_4^2` are nontrivial, $`J \cdot \overline{J} = p`; writing $`J = a + b i`
with $`a, b \in \mathbb{Z}` gives $`a^2 + b^2 = p`.
:::
