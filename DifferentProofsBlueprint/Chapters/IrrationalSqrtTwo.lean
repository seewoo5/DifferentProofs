import Verso
import VersoManual
import VersoBlueprint
import DifferentProofsBlueprint.ProofColor
import DifferentProofs.IrrationalSqrtTwo.Basic
import DifferentProofs.IrrationalSqrtTwo.CongruentNumber
import DifferentProofs.IrrationalSqrtTwo.Defs
import DifferentProofs.IrrationalSqrtTwo.Descent
import DifferentProofs.IrrationalSqrtTwo.FermatLastTheorem
import DifferentProofs.IrrationalSqrtTwo.Valuation

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option linter.style.longLine false

#doc (Manual) "Irrationality of √2" =>

:::group "grp:sqrt-two"
Irrationality of square root of 2.
:::

:::definition "def:sqrt-two" (parent := "grp:sqrt-two") (lean := "IrrationalSqrtTwo")
The real number $`\sqrt{2}` is irrational: it is not the image of any rational
number under the canonical embedding $`\mathbb{Q} \hookrightarrow \mathbb{R}`.
:::

:::definition "def:sqrt-two-nat" (parent := "grp:sqrt-two") (lean := "IrrationalSqrtTwoNat")
The natural-number form says that the equation $`p^2 = 2q^2` has no solution in
natural numbers with $`q \neq 0`.
:::

:::theorem "thm:sqrt-two-nat-impl-sqrt-two" (parent := "grp:sqrt-two") (lean := "IrrationalSqrtTwoNat_impl_IrrationalSqrtTwo")
The natural-number statement {uses "def:sqrt-two-nat"}[] implies the real
statement {uses "def:sqrt-two"}[].
:::

:::proof "thm:sqrt-two-nat-impl-sqrt-two"
If $`\sqrt{2}` were the image of a rational $`r`, squaring gives $`r^2 = 2` in
$`\mathbb{Q}`. Writing $`r` as the quotient of its numerator and denominator
and clearing denominators yields $`\mathrm{num}(r)^2 = 2\,\mathrm{den}(r)^2`,
so taking absolute values gives a natural-number solution of $`p^2 = 2q^2`
with $`q = \mathrm{den}(r) \neq 0`.
:::

First proof is by infinite descent.

:::theorem "thm:sqrt-two-descent" (parent := "grp:sqrt-two") (lean := "IrrationalSqrtTwo_Descent") (proofColor := "#bae6fd")
$`\sqrt{2}` is irrational.
:::

:::proof "thm:sqrt-two-descent"
Use {uses "thm:sqrt-two-nat-impl-sqrt-two"}[] to reduce to the natural-number form.
Suppose $`p^2 = 2q^2` with $`q > 0`. Then $`2 \mid p^2`, so $`2 \mid p` since
$`2` is prime; write $`p = 2r`. Substituting gives $`q^2 = 2r^2`, a new
solution whose first component $`q` is strictly smaller than $`p`. By strong
induction no solution with $`q \neq 0` exists.
:::

Second proof is by $`2`-adic valuation.

:::theorem "thm:sqrt-two-valuation" (parent := "grp:sqrt-two") (lean := "IrrationalSqrtTwo_Valuation") (proofColor := "#bae6fd")
$`\sqrt{2}` is irrational.
:::

:::proof "thm:sqrt-two-valuation"
Use {uses "thm:sqrt-two-nat-impl-sqrt-two"}[] to reduce to the natural-number form.
Apply the exponent of $`2` in the prime factorization to both sides of
$`p^2 = 2q^2`. The left side has even $`2`-adic valuation $`2v_2(p)`, while
the right side has odd valuation $`1 + 2v_2(q)`, a contradiction.
:::

Third proof is by Fermat's Last Theorem for exponent $`3`.

:::theorem "thm:sqrt-two-flt" (parent := "grp:sqrt-two") (lean := "IrrationalSqrtTwo_FermatLastTheorem") (proofColor := "#bae6fd")
$`\sqrt{2}` is irrational.
:::

:::proof "thm:sqrt-two-flt"
This proof establishes the irrationality of $`\sqrt{2}` {uses "def:sqrt-two"}[]
directly, without the natural-number reduction.
One has the identity $`(18+17\sqrt{2})^3 + (18-17\sqrt{2})^3 = 42^3`, due to
Jarvis and Meekin. If $`\sqrt{2}` were a rational $`r`, then $`18+17r`,
$`18-17r`, and $`42` would be nonzero rationals (nonzero because
$`(\pm 18/17)^2 \neq 2`) solving $`x^3 + y^3 = z^3`, contradicting Fermat's
Last Theorem for exponent $`3`. See
[this Math StackExchange answer](https://math.stackexchange.com/a/4438248).
:::

Fourth proof is by Fermat's theorem that $`1` is not a congruent number.

:::definition "def:congruent-number" (parent := "grp:sqrt-two") (lean := "IsCongruentNumber")
A positive rational number $`n` is a *congruent number* if it is the area of a right triangle
with rational sides: there are rational numbers $`a, b, c > 0` with $`a^2 + b^2 = c^2` and
$`\frac{1}{2}ab = n`.
:::

:::theorem "thm:one-not-congruent" (parent := "grp:sqrt-two") (lean := "not_isCongruentNumber_one")
Fermat's theorem: $`1` is not a congruent number {uses "def:congruent-number"}[].
:::

:::proof "thm:one-not-congruent"
This is Theorem 2.1 of Keith Conrad's notes
[The congruent number problem](https://kconrad.math.uconn.edu/blurbs/ugradnumthy/congnumber.pdf),
proved by Fermat's method of descent. Write the sides of a rational right triangle with area
$`1` as $`a/d`, $`b/d`, $`c/d` with positive integers $`a, b, c, d`, so that $`a^2 + b^2 = c^2`
and $`ab = 2d^2`. The greatest common divisor $`g` of $`a` and $`b` satisfies $`g^2 \mid c^2` and
$`g^2 \mid 2d^2`, hence $`g \mid c` and $`g \mid d`, and dividing by $`g` gives a solution with
$`a` and $`b` coprime.
Then exactly one of $`a` and $`b` is even, say $`a`, and $`a = 2k^2`, $`b = \ell^2` with
$`\ell` odd, so $`c` is odd too. The coprime integers $`(c+b)/2` and $`(c-b)/2` multiply to
$`k^4`, so they are $`r^4` and $`s^4`, and $`\ell^2 = r^4 - s^4 = (r^2+s^2)(r^2-s^2)` with
coprime factors. Hence $`r^2 + s^2 = t^2` and $`r^2 - s^2 = u^2` with $`t` and $`u` odd and
coprime, and $`u^2 \equiv 1 \pmod{4}` forces $`r` to be odd and $`s` to be even. Now
$`a' = (t+u)/2`, $`b' = (t-u)/2`, $`c' = r`, $`d' = s/2` is another solution with $`a'` and
$`b'` coprime, and $`c' = r \le r^4 < r^4 + s^4 = c`. By descent there is no solution.
:::

:::theorem "thm:sqrt-two-congruent-number" (parent := "grp:sqrt-two") (lean := "IrrationalSqrtTwo_CongruentNumber") (proofColor := "#bae6fd")
$`\sqrt{2}` is irrational.
:::

:::proof "thm:sqrt-two-congruent-number"
This proof establishes the irrationality of $`\sqrt{2}` {uses "def:sqrt-two"}[]
directly, without the natural-number reduction.
If $`\sqrt{2}` were rational, then $`\sqrt{2}`, $`\sqrt{2}` and $`2` would be the sides of a
rational right triangle with area $`1`, contradicting {uses "thm:one-not-congruent"}[]. This is
the remark after Theorem 2.1 in Conrad's notes; see also
[this Math StackExchange answer](https://math.stackexchange.com/a/1332960).
:::
