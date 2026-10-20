module

public import DifferentProofs.BaselProblem.Eisenstein
public import Mathlib.NumberTheory.ModularForms.RamanujanFormula

/-!
# The Basel problem via Ramanujan's identity for `E₂`

This is the proof in Seewoo Lee's note *New(?) proof of Bassel problem*
(https://seewoo5.github.io/jekyll/update/2023/12/04/zeta-eisenstein.html). Normalize the
Eisenstein series so that their constant terms are `1`:
$$ E_k = 1 + \alpha_k \sum_{n \ge 1} \sigma_{k-1}(n) q^n,
  \qquad \alpha_k = \frac{(2\pi i)^k}{\zeta(k) (k-1)!}, $$
so that the Basel problem is the evaluation `α₂ = -24`. Ramanujan's identity
$$ D E_2 = \frac{E_2^2 - E_4}{12}, \qquad D = \frac{1}{2\pi i} \frac{d}{dz} = q \frac{d}{dq}, $$
compared at the coefficients of `q` and `q²`, gives
$$ \alpha_2 = \frac{2\alpha_2 - \alpha_4}{12}, \qquad
  6\alpha_2 = \frac{6\alpha_2 + \alpha_2^2 - 9\alpha_4}{12}, $$
whence `α₄ = -10 α₂` and `α₂ (α₂ + 24) = 0`. As `α₂ ≠ 0`, `α₂ = -24`, that is, `ζ(2) = π² / 6`.

The `q`-expansions of `E₂` and `E₄` with `ζ(2)` and `ζ(4)` left unevaluated, and the comparison of
coefficients, are in `DifferentProofs.BaselProblem.Eisenstein`. Ramanujan's identity is mathlib's
`Derivative.normalizedDerivOfComplex_E₂`.

## Circularity

Mathlib's proof of `Derivative.normalizedDerivOfComplex_E₂` uses `riemannZeta_two`, that is,
`ζ(2) = π² / 6`: to show that `D E₂ - E₂² / 12` is modular, and, through `E2_mdifferentiable` and
`ModularForm.logDeriv_eta_eq_E2`, to show that `E₂` is holomorphic. Mathlib derives
`riemannZeta_two` from its own solution `hasSum_zeta_two` of the Basel problem. This is not an
accident of mathlib's proof: since `E₂ = G₂ / (2ζ(2))`, the identity with the constant `1 / 12`
already implies `ζ(2) = π² / 6`, by the very computation above.

So, unlike the other proofs in this project, this one is not independent of mathlib's
`hasSum_zeta_two`. It formalizes the coefficient comparison of the note, taking Ramanujan's
identity from mathlib as the note takes it from the literature.
`DifferentProofs.BaselProblem.RamanujanUnnormalized` removes the circularity by proving the
identity in the form `D E₂ = (ζ(2) / (2π²)) (E₂² - E₄)`, which does not presuppose the value
of `ζ(2)`.
-/

@[expose] public section

open Derivative

namespace BaselProblem.Ramanujan

/-- Solving the coefficient relations for Ramanujan's identity `D E₂ = (E₂² - E₄) / 12`:
`α₄ = -10 α₂` and `α₂ (α₂ + 24) = 0`. -/
lemma α_two_eq : α 2 = -24 := by
  grind [coeff_relations normalizedDerivOfComplex_E₂, α_two_ne_zero]

end BaselProblem.Ramanujan

open BaselProblem BaselProblem.Ramanujan in
theorem BaselProblem_Ramanujan : BaselProblem := baselProblem_of_α_two α_two_eq
