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

:::theorem "thm:basel-cauchy" (parent := "grp:basel") (lean := "BaselProblem.Cauchy.BaselProblem_Cauchy")
The sum $`\sum_{n \geq 1} \frac{1}{n^2}` equals $`\frac{\pi^2}{6}`. This is
Cauchy's elementary proof by a cotangent squeeze, using no analytic machinery
beyond limits, and proves {uses "def:basel"}[].
:::

:::proof "thm:basel-cauchy"
For $`0 < x < \pi/2` one has $`\sin x < x < \tan x`, hence the squeeze
$`\cot^2 x < \frac{1}{x^2} < \csc^2 x = 1 + \cot^2 x`. De Moivre's formula
expands $`\sin((2n+1)\theta)` as $`\sin^{2n+1}\theta` times a degree-$`n`
polynomial $`P` in $`\cot^2\theta`, whose $`n` roots are
$`\cot^2\!\left(\frac{k\pi}{2n+1}\right)` for $`k = 1, \dots, n`. Reading off the
two leading coefficients of $`P` and applying Vieta's formula gives
$`\sum_{k=1}^{n} \cot^2\!\left(\frac{k\pi}{2n+1}\right) = \frac{n(2n-1)}{3}`.

Summing the squeeze inequality over the $`n` angles $`\frac{k\pi}{2n+1}` and
using $`\sum_{k=1}^n \frac{1}{\theta_k^2} = \frac{(2n+1)^2}{\pi^2}
  \sum_{k=1}^n \frac{1}{k^2}` yields
$`\frac{n(2n-1)}{3} < \frac{(2n+1)^2}{\pi^2} \sum_{k=1}^n \frac{1}{k^2}
  < \frac{n(2n-1)}{3} + n`.
Multiplying through by $`\frac{\pi^2}{(2n+1)^2}` sandwiches the partial sum
$`\sum_{k=1}^n \frac{1}{k^2}` between two sequences both tending to
$`\frac{\pi^2}{6}`, so by the squeeze theorem the series converges to
$`\frac{\pi^2}{6}`.
:::
