import Verso
import VersoManual
import VersoBlueprint
import DifferentProofs.IrrationalSqrtTwo.Basic
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

:::theorem "thm:sqrt-two-descent" (parent := "grp:sqrt-two") (lean := "IrrationalSqrtTwo_Descent")
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

:::theorem "thm:sqrt-two-valuation" (parent := "grp:sqrt-two") (lean := "IrrationalSqrtTwo_Valuation")
$`\sqrt{2}` is irrational.
:::

:::proof "thm:sqrt-two-valuation"
Use {uses "thm:sqrt-two-nat-impl-sqrt-two"}[] to reduce to the natural-number form.
Apply the exponent of $`2` in the prime factorization to both sides of
$`p^2 = 2q^2`. The left side has even $`2`-adic valuation $`2v_2(p)`, while
the right side has odd valuation $`1 + 2v_2(q)`, a contradiction.
:::

Third proof is by Fermat's Last Theorem for exponent $`3`.

:::theorem "thm:sqrt-two-flt" (parent := "grp:sqrt-two") (lean := "IrrationalSqrtTwo_FermatLastTheorem")
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
