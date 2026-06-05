import Verso
import VersoManual
import VersoBlueprint
import DifferentProofs.FermatLittleTheorem.Alkauskas
import DifferentProofs.FermatLittleTheorem.Basic
import DifferentProofs.FermatLittleTheorem.Binomial
import DifferentProofs.FermatLittleTheorem.Defs
import DifferentProofs.FermatLittleTheorem.Dynamical
import DifferentProofs.FermatLittleTheorem.Lagrange

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option linter.style.longLine false

#doc (Manual) "Fermat's Little Theorem" =>

:::group "grp:flt"
Statements and proofs of Fermat's Little Theorem.
:::

:::definition "def:flt" (parent := "grp:flt") (lean := "FermatLittleTheorem")
Fermat's Little Theorem, in integer form, says that for any prime $`p` and
integer $`a`, one has $`a^p \equiv a \pmod p`.
:::

:::definition "def:flt-nat" (parent := "grp:flt") (lean := "FermatLittleTheoremNat")
The natural-number form says that for any prime $`p` and natural number $`a`,
one has $`a^p \equiv a \pmod p`.
:::

:::theorem "thm:flt-nat-impl-flt" (parent := "grp:flt") (lean := "FermatLittleTheoremNat_impl_FermatLittleTheorem")
The natural-number statement {uses "def:flt-nat"}[] implies the integer
statement {uses "def:flt"}[].
:::

:::proof "thm:flt-nat-impl-flt"
Work in $`\mathbb{Z}/p\mathbb{Z}`. Every element is represented by the natural
number `((a : ZMod p).val)`, so the natural-number congruence transfers back
through the canonical map.
:::

:::theorem "thm:flt-binomial" (parent := "grp:flt") (lean := "FermatLittleTheorem_Binomial")
For any prime $`p` and integer $`a`, one has $`a^p \equiv a \pmod p`.
This proof uses the binomial theorem.
:::

:::proof "thm:flt-binomial"
In characteristic $`p`, Freshman's dream gives
$`(x + 1)^p = x^p + 1`. Applying this in `ZMod p` and inducting over natural
representatives proves the congruence.
:::

:::theorem "thm:flt-lagrange" (parent := "grp:flt") (lean := "FermatLittleTheorem_Lagrange")
For any prime $`p` and integer $`a`, one has $`a^p \equiv a \pmod p`.
This proof uses Lagrange's theorem.
:::

:::proof "thm:flt-lagrange"
If $`a` is zero modulo $`p`, the claim is immediate. Otherwise `a` is a unit in
$`\mathbb{Z}/p\mathbb{Z}`; by Lagrange's theorem its order divides
$`p - 1`, so $`a^{p-1} = 1`, and multiplying by $`a` gives the result.
:::

:::lemma_ "lem:flt-alkauskas-expansion" (parent := "grp:flt")
Let $`g \in \mathbb{Z}[[x]]` be an integer power series of the form
$`g(x) = 1 - x - d x^2 + \sum_{k \ge 3} b_k x^k`. For every $`N`, there is a
sequence of integers $`(a_n)_{n \ge 1}` with $`a_1 = 1` such that $`g` agrees
with $`\prod_{n=1}^{N}(1 - a_n x^n)` in all coefficients of degree at most
$`N`.
:::

:::proof "lem:flt-alkauskas-expansion"
Choose the factors inductively. Multiplying by
$`1 - a_{N+1}x^{N+1}` leaves all lower coefficients fixed, and the integer
$`a_{N+1}` can be chosen to match the coefficient of $`x^{N+1}`.
:::

:::theorem "thm:flt-alkauskas" (parent := "grp:flt") (lean := "FermatLittleTheorem.Alkauskas.FermatLittleTheorem_Alkauskas")
For any prime $`p` and integer $`a`, one has $`a^p \equiv a \pmod p`.
This proof uses Alkauskas' product expansion and depends on
{uses "lem:flt-alkauskas-expansion"}[] and {uses "thm:flt-nat-impl-flt"}[].
:::

:::proof "thm:flt-alkauskas"
Apply the integer formal product expansion to
$`\frac{1-(d+1)x}{1-dx}`. Comparing the coefficient of $`x^p` in the negated
logarithmic derivative gives $`p \mid (d+1)^p - d^p - 1`. Telescoping these
congruences over $`d` proves the natural-number form, then the reduction gives
the integer form.
:::

:::definition "def:T" (parent := "grp:flt") (lean := "T")
For a natural number $`n`, define $`T_n : [0,1] \to [0,1]` by
$`T_n(x) = \{nx\}` for $`0 \le x < 1` and $`T_n(1) = 1`.
:::

:::lemma_ "lem:T-comp-eq-mul" (parent := "grp:flt") (lean := "T_comp_eq_mul")
For natural numbers $`m` and $`n`, the maps satisfy
$`T_m \circ T_n = T_{mn}`. This is a consequence of {uses "def:T"}[].
:::

:::proof "lem:T-comp-eq-mul"
Away from $`1`, write fractional parts as subtraction of floors:
$`\{m\{nx\}\} = \{mnx\}` because the difference is an integer.
The endpoint $`1` is fixed by definition.
:::

:::lemma_ "lem:T-num-fp-eq" (parent := "grp:flt") (lean := "T_num_fp_eq")
For any $`n \ge 2`, the map $`T_n` has exactly $`n` fixed points.
This counts the fixed points of {uses "def:T"}[].
:::

:::proof "lem:T-num-fp-eq"
For $`x < 1`, the equation $`T_n(x)=x` is equivalent to
$`(n-1)x \in \mathbb{Z}`, giving the points $`j/(n-1)` for
$`0 \le j \le n-2`. Together with the endpoint $`1`, these are exactly
$`n` fixed points.
:::

:::theorem "thm:flt-dynamical" (parent := "grp:flt") (lean := "FermatLittleTheorem_Dynamical")
For any prime $`p` and integer $`a`, one has $`a^p \equiv a \pmod p`.
The proof uses {uses "lem:T-comp-eq-mul"}[], {uses "lem:T-num-fp-eq"}[], and
the reduction {uses "thm:flt-nat-impl-flt"}[].
:::

:::proof "thm:flt-dynamical"
It suffices to prove the natural-number form. For $`a \ge 2`, consider the
fixed points of $`T_{a^p}` that are not fixed by $`T_a`. Their cardinality is
$`a^p-a`, and the action of $`T_a` partitions this set into orbits of size
$`p`, so $`p` divides $`a^p-a`.
:::
