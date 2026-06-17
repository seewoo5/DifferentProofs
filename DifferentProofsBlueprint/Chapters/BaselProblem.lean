import Verso
import VersoManual
import VersoBlueprint
import DifferentProofs.BaselProblem.Defs
import DifferentProofs.BaselProblem.Parseval
import DifferentProofs.BaselProblem.Cauchy

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option linter.style.longLine false

#doc (Manual) "Basel problem" =>

:::group "grp:basel"
Statements and proofs of the Basel problem, the evaluation of the sum of the
reciprocals of the squares.
:::

:::definition "def:basel" (parent := "grp:basel") (lean := "BaselProblem")
The Basel problem asserts the value of the convergent series
$`\sum_{n \geq 1} \frac{1}{n^2} = \frac{\pi^2}{6}`. The summand at $`n = 0` is
$`1 / 0 = 0` by convention, so the natural-number sum agrees with the series
over positive integers.
:::

:::theorem "thm:basel-parseval" (parent := "grp:basel") (lean := "BaselProblem.BaselProblem_Parseval")
The sum $`\sum_{n \geq 1} \frac{1}{n^2}` equals $`\frac{\pi^2}{6}`. This proof
uses Parseval's identity for the Fourier series of the function $`x \mapsto x`
and proves {uses "def:basel"}[].
:::

:::proof "thm:basel-parseval"
Let $`f(x) = x` on the interval $`(-\pi, \pi]`, viewed as a square-integrable
function on the circle $`\mathbb{R} / 2\pi\mathbb{Z}`. Integration by parts gives
its Fourier coefficients $`c_n`; for $`n \neq 0` the boundary term contributes
$`c_n = \frac{(-1)^n}{2\pi i n} \cdot 2\pi`, whose squared modulus is
$`\lvert c_n \rvert^2 = 1/n^2`, while $`c_0 = 0` because $`f` is odd. Hence the
identity $`\lvert c_0 \rvert^2 = 1/0^2 = 0` makes $`\lvert c_n\rvert^2 = 1/n^2`
hold for every integer $`n`.
Parseval's identity states
$`\sum_{n \in \mathbb{Z}} \lvert c_n \rvert^2
  = \frac{1}{2\pi} \int_{-\pi}^{\pi} \lvert f(x) \rvert^2 \, dx`.
The right-hand side is $`\frac{1}{2\pi} \int_{-\pi}^{\pi} x^2 \, dx
  = \frac{1}{2\pi} \cdot \frac{2\pi^3}{3} = \frac{\pi^2}{3}`. The left-hand side
is $`\sum_{n \in \mathbb{Z}} \frac{1}{n^2}
  = 2 \sum_{n \geq 1} \frac{1}{n^2}` because the summand is even and the
$`n = 0` term vanishes. Equating the two sides gives
$`2 \sum_{n \geq 1} \frac{1}{n^2} = \frac{\pi^2}{3}`, hence
$`\sum_{n \geq 1} \frac{1}{n^2} = \frac{\pi^2}{6}`.
:::

The remaining entries record the main steps of Cauchy's proof.

:::lemma_ "lem:de-moivre" (parent := "grp:basel") (lean := "BaselProblem.Cauchy.sin_two_mul_add_one")
For all $`\theta \in \mathbb{R}` and $`n \in \mathbb{N}`,
$`\sin((2n+1)\theta) = \sum_{j=0}^{n} (-1)^j \binom{2n+1}{2j+1}
  \cos^{2(n-j)}\theta \, \sin^{2j+1}\theta`.
:::

:::proof "lem:de-moivre"
Since $`\cos\theta + i\sin\theta = e^{i\theta}`, we have
$`\sin((2n+1)\theta) = \operatorname{Im}\big((\cos\theta + i\sin\theta)^{2n+1}\big)`.
Expanding the power by the binomial theorem and taking the imaginary part keeps
exactly the terms with an odd power of $`i\sin\theta`; reindexing those terms by
$`j` gives the stated sum.
:::

:::definition "def:cot-poly" (parent := "grp:basel") (lean := "BaselProblem.Cauchy.cotPoly")
For $`n \in \mathbb{N}`, let
$`P_n(t) = \sum_{j=0}^{n} (-1)^j \binom{2n+1}{2j+1} t^{n-j}`. This polynomial has
degree $`n`, leading coefficient $`2n+1`, and coefficient of $`t^{n-1}` equal to
$`-\binom{2n+1}{3}`.
:::

:::lemma_ "lem:cot-poly-eval" (parent := "grp:basel") (lean := "BaselProblem.Cauchy.cotPoly_eval")
If $`\sin\theta \neq 0` then
$`P_n(\cot^2\theta)\,\sin^{2n+1}\theta = \sin((2n+1)\theta)`.
:::

:::proof "lem:cot-poly-eval"
Divide the De Moivre expansion {uses "lem:de-moivre"}[] by $`\sin^{2n+1}\theta`.
Each summand becomes
$`(-1)^j \binom{2n+1}{2j+1} \cos^{2(n-j)}\theta / \sin^{2(n-j)}\theta
  = (-1)^j \binom{2n+1}{2j+1} (\cot^2\theta)^{n-j}`,
and the sum of these is exactly $`P_n(\cot^2\theta)` {uses "def:cot-poly"}[].
:::

:::lemma_ "lem:cot-sq-sum" (parent := "grp:basel") (lean := "BaselProblem.Cauchy.cotSq_sum")
For $`n \geq 1`,
$`\sum_{k=1}^{n} \cot^2\!\left(\frac{k\pi}{2n+1}\right) = \frac{n(2n-1)}{3}`.
:::

:::proof "lem:cot-sq-sum"
For $`k = 1, \dots, n` the angle $`\theta_k = \frac{k\pi}{2n+1}` lies in
$`(0, \pi/2)` and satisfies $`\sin((2n+1)\theta_k) = \sin(k\pi) = 0` while
$`\sin\theta_k \neq 0`, so {uses "lem:cot-poly-eval"}[] shows each
$`\cot^2\theta_k` is a root of $`P_n`. The $`n` values $`\cot^2\theta_k` are
distinct, hence are exactly the roots of the degree-$`n` polynomial $`P_n`. By
Vieta's formula their sum is the negative ratio of the two leading coefficients,
$`\binom{2n+1}{3} / (2n+1) = \frac{n(2n-1)}{3}`.
:::

:::lemma_ "lem:cot-sq-lt-inv-sq" (parent := "grp:basel") (lean := "BaselProblem.Cauchy.cotSq_lt_inv_sq")
For $`0 < x < \pi/2`, $`\cot^2 x < \frac{1}{x^2}`.
:::

:::proof "lem:cot-sq-lt-inv-sq"
From $`x < \tan x` on $`(0, \pi/2)` we get $`\cot x < \frac{1}{x}`; both sides
are positive, so squaring preserves the inequality.
:::

:::lemma_ "lem:inv-sq-lt-csc-sq" (parent := "grp:basel") (lean := "BaselProblem.Cauchy.inv_sq_lt_one_add_cotSq")
For $`0 < x < \pi/2`, $`\frac{1}{x^2} < 1 + \cot^2 x`.
:::

:::proof "lem:inv-sq-lt-csc-sq"
From $`0 < \sin x < x` we get
$`\frac{1}{x^2} < \frac{1}{\sin^2 x} = 1 + \cot^2 x`.
:::

:::theorem "thm:basel-cauchy" (parent := "grp:basel") (lean := "BaselProblem.Cauchy.BaselProblem_Cauchy")
The sum $`\sum_{n \geq 1} \frac{1}{n^2}` equals $`\frac{\pi^2}{6}`. This is
Cauchy's elementary proof by a cotangent squeeze, using no analytic machinery
beyond limits, and proves {uses "def:basel"}[].
:::

:::proof "thm:basel-cauchy"
Apply the squeeze $`\cot^2 x < \frac{1}{x^2} < 1 + \cot^2 x`
({uses "lem:cot-sq-lt-inv-sq"}[] and {uses "lem:inv-sq-lt-csc-sq"}[]) at the
$`n` angles $`\theta_k = \frac{k\pi}{2n+1}` and sum over $`k`. Using
$`\sum_{k=1}^n \frac{1}{\theta_k^2} = \frac{(2n+1)^2}{\pi^2}
  \sum_{k=1}^n \frac{1}{k^2}` together with Cauchy's identity
{uses "lem:cot-sq-sum"}[] gives
$`\frac{n(2n-1)}{3} < \frac{(2n+1)^2}{\pi^2} \sum_{k=1}^n \frac{1}{k^2}
  < \frac{n(2n-1)}{3} + n`.
Multiplying through by $`\frac{\pi^2}{(2n+1)^2}` sandwiches the partial sum
$`\sum_{k=1}^n \frac{1}{k^2}` between two sequences both tending to
$`\frac{\pi^2}{6}`, so by the squeeze theorem the series converges to
$`\frac{\pi^2}{6}`.
:::
