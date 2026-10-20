import Verso
import VersoManual
import VersoBlueprint
import DifferentProofsBlueprint.ProofColor
import DifferentProofs.BaselProblem.Defs
import DifferentProofs.BaselProblem.Parseval
import DifferentProofs.BaselProblem.Cauchy
import DifferentProofs.BaselProblem.Ramanujan
import DifferentProofs.BaselProblem.RamanujanUnnormalized

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option linter.style.longLine false

#doc (Manual) "Basel problem" =>

:::group "grp:basel"
Basel problem.
:::

:::definition "def:basel" (parent := "grp:basel") (lean := "BaselProblem")
The Basel problem asserts the value of the convergent series
$`\sum_{n \geq 1} \frac{1}{n^2} = \frac{\pi^2}{6}`. The summand at $`n = 0` is
$`1 / 0 = 0` by convention.
:::

First proof uses Parseval's identity, applied to the function $`f(x) = x` on $`(-\pi, \pi]`.

:::theorem "thm:basel-parseval" (parent := "grp:basel") (lean := "BaselProblem_Parseval") (proofColor := "#fbcfe8")
$`\sum_{n \geq 1} \frac{1}{n^2} = \frac{\pi^2}{6}`.
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
$`\sum_{n \geq 1} \frac{1}{n^2} = \frac{\pi^2}{6}`, the value asserted by the
Basel problem {uses "def:basel"}[].
:::

Second proof uses Cauchy's method of bounding the partial sums by evaluating a certain
trigonometric polynomial at the angles $`\frac{k\pi}{2n+1}` for $`k = 1, \dots, n`.

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

:::theorem "thm:basel-cauchy" (parent := "grp:basel") (lean := "BaselProblem_Cauchy") (proofColor := "#fbcfe8")
$`\sum_{n \geq 1} \frac{1}{n^2} = \frac{\pi^2}{6}`.
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
$`\frac{\pi^2}{6}`, the value asserted by the Basel problem {uses "def:basel"}[].
:::

The third and fourth proofs follow Seewoo Lee's note *New(?) proof of Bassel problem*. Normalize
the Eisenstein series of weights $`2` and $`4` to have constant term $`1`. Ramanujan's identity for
the derivative of $`E_2`, compared at the coefficients of $`q` and $`q^2`, then determines the
normalizing constant of $`E_2`, which is $`-4\pi^2/\zeta(2)`.

:::definition "def:basel-alpha" (parent := "grp:basel") (lean := "BaselProblem.α")
For $`k \geq 2` let $`\alpha_k = \frac{(2\pi i)^k}{\zeta(k)\,(k-1)!}`. In particular
$`\alpha_2 = -\frac{4\pi^2}{\zeta(2)}`, so the Basel problem is the statement $`\alpha_2 = -24`.
:::

:::lemma_ "lem:basel-E2-expansion" (parent := "grp:basel") (lean := "BaselProblem.hasSum_E2")
With $`q = e^{2\pi i z}`, the normalized Eisenstein series $`E_2 = G_2 / (2\zeta(2))` has the
$`q`-expansion $`E_2 = 1 + \alpha_2 \sum_{n \geq 1} \sigma_1(n) q^n`.
:::

:::proof "lem:basel-E2-expansion"
Lipschitz's formula, which follows from Euler's partial fraction expansion of $`\pi \cot \pi z`,
gives $`G_2 = 2\zeta(2) + 2(2\pi i)^2 \sum_{n \geq 1} \sigma_1(n) q^n` with $`\zeta(2)` left
unevaluated {uses "def:basel-alpha"}[]; divide by $`2\zeta(2)`.
:::

:::lemma_ "lem:basel-E4-expansion" (parent := "grp:basel") (lean := "BaselProblem.hasSum_E₄")
The normalized Eisenstein series of weight $`4` has the $`q`-expansion
$`E_4 = 1 + \alpha_4 \sum_{n \geq 1} \sigma_3(n) q^n`.
:::

:::proof "lem:basel-E4-expansion"
This is the $`q`-expansion of $`E_4 = G_4 / (2\zeta(4))`, again with $`\zeta(4)` left unevaluated
{uses "def:basel-alpha"}[].
:::

:::lemma_ "lem:basel-D-expansion" (parent := "grp:basel") (lean := "Derivative.hasSum_normalizedDerivOfComplex_of_hasSum")
If $`f = \sum_{m \geq 0} c_m q^m` on the upper half-plane, then $`D f = \sum_{m \geq 0} m\,c_m q^m`,
where $`D = \frac{1}{2\pi i} \frac{d}{dz} = q \frac{d}{dq}`.
:::

:::proof "lem:basel-D-expansion"
A power series can be differentiated term by term inside its disc of convergence, and
$`D q^m = m q^m`.
:::

:::lemma_ "lem:basel-coeff-relations" (parent := "grp:basel") (lean := "BaselProblem.coeff_relations")
If $`D E_2 = \kappa (E_2^2 - E_4)` for a constant $`\kappa`, then
$`\alpha_2 = \kappa (2\alpha_2 - \alpha_4)` and
$`6\alpha_2 = \kappa (6\alpha_2 + \alpha_2^2 - 9\alpha_4)`.
:::

:::proof "lem:basel-coeff-relations"
By {uses "lem:basel-E2-expansion"}[], {uses "lem:basel-E4-expansion"}[] and
{uses "lem:basel-D-expansion"}[], the coefficients of $`q` and $`q^2` are $`\alpha_2` and
$`6\alpha_2` in $`D E_2`, $`2\alpha_2` and $`6\alpha_2 + \alpha_2^2` in $`E_2^2`, and $`\alpha_4` and
$`9\alpha_4` in $`E_4`, since $`\sigma_1(2) = 3` and $`\sigma_3(2) = 9`. A convergent $`q`-series
determines its coefficients, so they agree on both sides.
:::

:::lemma_ "lem:basel-alpha-two" (parent := "grp:basel") (lean := "BaselProblem.baselProblem_of_α_two")
If $`\alpha_2 = -24`, then $`\sum_{n \geq 1} \frac{1}{n^2} = \frac{\pi^2}{6}`.
:::

:::proof "lem:basel-alpha-two"
$`\alpha_2 = -\frac{4\pi^2}{\zeta(2)} = -24` says $`\zeta(2) = \frac{\pi^2}{6}`
{uses "def:basel-alpha"}[], and $`\zeta(2) = \sum_{n \geq 1} \frac{1}{n^2}` {uses "def:basel"}[].
:::

:::theorem "thm:basel-ramanujan" (parent := "grp:basel") (lean := "BaselProblem_Ramanujan") (proofColor := "#fbcfe8")
$`\sum_{n \geq 1} \frac{1}{n^2} = \frac{\pi^2}{6}`.
:::

:::proof "thm:basel-ramanujan"
Take Ramanujan's identity $`D E_2 = \frac{E_2^2 - E_4}{12}` from mathlib. By
{uses "lem:basel-coeff-relations"}[] with $`\kappa = \frac{1}{12}`,
$`12\alpha_2 = 2\alpha_2 - \alpha_4` and $`72\alpha_2 = 6\alpha_2 + \alpha_2^2 - 9\alpha_4`, so
$`\alpha_4 = -10\alpha_2` and $`\alpha_2 (\alpha_2 + 24) = 0`. As $`\alpha_2 \neq 0`,
$`\alpha_2 = -24` {uses "lem:basel-alpha-two"}[]. This proof is not independent of mathlib's
evaluation of $`\zeta(2)`: mathlib proves Ramanujan's identity using $`\zeta(2) = \frac{\pi^2}{6}`,
and the identity with the constant $`\frac{1}{12}` is in fact equivalent to it, by the computation
just made.
:::

The fourth proof removes this circularity. Without the value of $`\zeta(2)`, the argument by
modularity gives Ramanujan's identity with $`\frac{1}{12}` replaced by
$`\kappa = \frac{\zeta(2)}{2\pi^2}`. Its one input from the theory of modular forms, that cusp forms
of weight $`4` vanish, rests on the transformation of the Dedekind eta function, which is proved
here from the pentagonal number theorem and Poisson summation.

:::lemma_ "lem:basel-eta-pentagonal" (parent := "grp:basel") (lean := "BaselProblem.RamanujanUnnormalized.hasSum_eta")
For $`\operatorname{Im} z > 0`,
$`\eta(z) = q^{1/24} \prod_{n \geq 1} (1 - q^n) = \sum_{k \in \mathbb{Z}} (-1)^k e^{\pi i z (6k - 1)^2 / 12}`.
:::

:::proof "lem:basel-eta-pentagonal"
This is Euler's pentagonal number theorem
$`\prod_{n \geq 1} (1 - q^n) = \sum_{k \in \mathbb{Z}} (-1)^k q^{k (3k - 1) / 2}`, together with
$`\frac{1}{24} + \frac{k (3k - 1)}{2} = \frac{(6k - 1)^2}{24}`.
:::

:::lemma_ "lem:basel-eta-poisson" (parent := "grp:basel") (lean := "BaselProblem.RamanujanUnnormalized.eta_eq_tsum")
For $`\operatorname{Im} z > 0`,
$`\eta(z) = (-3iz)^{-1/2} \sum_{n \in \mathbb{Z}} e^{-\pi i (2n - 1) / 6}\, e^{\pi i (-1/z) (2n - 1)^2 / 12}`.
:::

:::proof "lem:basel-eta-poisson"
Write the series of {uses "lem:basel-eta-pentagonal"}[] as
$`e^{\pi i z / 12} \sum_k e^{-\pi a k^2 + 2\pi b k}` with $`a = -3iz` and $`b = \frac{i (1 - z)}{2}`,
and apply Poisson summation to this Gaussian:
$`\sum_k e^{-\pi a k^2 + 2\pi b k} = a^{-1/2} \sum_n e^{-\pi (n + ib)^2 / a}`. Expanding the square,
the factor $`e^{\pi i z / 12}` cancels.
:::

:::lemma_ "lem:basel-eta-twisted" (parent := "grp:basel") (lean := "BaselProblem.RamanujanUnnormalized.tsum_twisted")
For $`\operatorname{Im} w > 0`,
$`\sum_{n \in \mathbb{Z}} e^{-\pi i (2n - 1) / 6}\, e^{\pi i w (2n - 1)^2 / 12} = \sqrt{3}\,\eta(w)`.
:::

:::proof "lem:basel-eta-twisted"
Split $`n` modulo $`3`. The classes $`n = 3j` and $`n = 3j + 1` contribute $`e^{\pi i / 6}` and
$`e^{-\pi i / 6}` times the series of {uses "lem:basel-eta-pentagonal"}[] (the second after
$`j \mapsto -j`), and these factors add up to $`2 \cos \frac{\pi}{6} = \sqrt{3}`. The class
$`n = 3j + 2` contributes a series that changes sign under $`j \mapsto -1 - j`, so it vanishes.
:::

:::lemma_ "lem:basel-eta-transformation" (parent := "grp:basel") (lean := "BaselProblem.RamanujanUnnormalized.eta_neg_one_div_pow")
For $`\operatorname{Im} z > 0`, $`\eta(-1/z)^{24} = z^{12}\,\eta(z)^{24}`. Hence
$`\Delta = \eta^{24}` is a cusp form of weight $`12` for $`\mathrm{SL}_2(\mathbb{Z})`.
:::

:::proof "lem:basel-eta-transformation"
By {uses "lem:basel-eta-poisson"}[] and {uses "lem:basel-eta-twisted"}[] at $`w = -1/z`,
$`\eta(z) = \sqrt{3}\,(-3iz)^{-1/2}\,\eta(-1/z)`. The $`24`th power removes the square root:
$`\eta(z)^{24} = 3^{12} (-3iz)^{-12} \eta(-1/z)^{24} = z^{-12} \eta(-1/z)^{24}`. Invariance under
$`z \mapsto z + 1` and vanishing at $`i\infty` are visible from the product.
:::

:::lemma_ "lem:basel-cusp-forms-vanish" (parent := "grp:basel") (lean := "BaselProblem.RamanujanUnnormalized.cuspForm_eq_zero")
A cusp form of weight $`k < 12` for $`\mathrm{SL}_2(\mathbb{Z})` is zero.
:::

:::proof "lem:basel-cusp-forms-vanish"
$`\Delta` vanishes nowhere on the upper half-plane and has a simple zero at the cusp, so dividing a
cusp form of weight $`k` by $`\Delta` {uses "lem:basel-eta-transformation"}[] gives a modular form
of weight $`k - 12 < 0`, which is zero.
:::

:::lemma_ "lem:basel-slash-invariant" (parent := "grp:basel") (lean := "BaselProblem.RamanujanUnnormalized.slash_invariant")
With $`\kappa = \frac{\zeta(2)}{2\pi^2}`, the function $`D E_2 - \kappa E_2^2` transforms like a
modular form of weight $`4` under $`\mathrm{SL}_2(\mathbb{Z})`.
:::

:::proof "lem:basel-slash-invariant"
For $`\gamma \in \mathrm{SL}_2(\mathbb{Z})` with bottom row $`(c, d)`, the transformation law of
$`G_2` gives $`(cz + d)^{-2} E_2(\gamma z) = E_2(z) - \frac{2\pi i c}{2\zeta(2) (cz + d)}`.
Differentiating, the defects of $`D E_2` and of $`\kappa E_2^2` cancel exactly when
$`\kappa \cdot \frac{(2\pi i)^2}{2\zeta(2)} = -1`, that is, when
$`\kappa = \frac{\zeta(2)}{2\pi^2}`.
:::

:::lemma_ "lem:basel-ramanujan-unnormalized" (parent := "grp:basel") (lean := "BaselProblem.RamanujanUnnormalized.normalizedDerivOfComplex_E2")
$`D E_2 = \frac{\zeta(2)}{2\pi^2} (E_2^2 - E_4)`.
:::

:::proof "lem:basel-ramanujan-unnormalized"
By {uses "lem:basel-slash-invariant"}[], $`D E_2 - \kappa (E_2^2 - E_4)` is modular of weight $`4`.
It is holomorphic, and it tends to $`0 - \kappa (1 - 1) = 0` at $`i\infty` by
{uses "lem:basel-E2-expansion"}[] and {uses "lem:basel-E4-expansion"}[]. So it is a cusp form of
weight $`4`, and it is zero by {uses "lem:basel-cusp-forms-vanish"}[].
:::

:::theorem "thm:basel-ramanujan-unnormalized" (parent := "grp:basel") (lean := "BaselProblem_RamanujanUnnormalized") (proofColor := "#fbcfe8")
$`\sum_{n \geq 1} \frac{1}{n^2} = \frac{\pi^2}{6}`.
:::

:::proof "thm:basel-ramanujan-unnormalized"
By {uses "lem:basel-ramanujan-unnormalized"}[] and {uses "lem:basel-coeff-relations"}[] with
$`\kappa = \frac{\zeta(2)}{2\pi^2}`, $`\alpha_2 = \kappa (2\alpha_2 - \alpha_4)` and
$`6\alpha_2 = \kappa (6\alpha_2 + \alpha_2^2 - 9\alpha_4)`, which are the note's equations with
$`\frac{1}{12}` replaced by $`\kappa`. Since $`\kappa \alpha_2 = -2`, multiplying both by
$`\alpha_2` and eliminating $`\alpha_4` gives $`\alpha_2 (\alpha_2 + 24) = 0`, so
$`\alpha_2 = -24` {uses "lem:basel-alpha-two"}[].
:::
