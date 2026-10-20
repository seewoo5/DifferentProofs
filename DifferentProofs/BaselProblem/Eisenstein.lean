module

public import DifferentProofs.BaselProblem.Defs
public import DifferentProofsForMathlib.NumberTheory.ModularForms.Derivative
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable

/-!
# The Basel problem from `q`-expansions of Eisenstein series

This is the part shared by `DifferentProofs.BaselProblem.Ramanujan` and
`DifferentProofs.BaselProblem.RamanujanUnnormalized`, the two formalizations of Seewoo Lee's note
*New(?) proof of Bassel problem*
(https://seewoo5.github.io/jekyll/update/2023/12/04/zeta-eisenstein.html).

Normalized to have constant term `1`, the Eisenstein series of weights `2` and `4` are
$$ E_k = 1 + \alpha_k \sum_{n \ge 1} \sigma_{k-1}(n) q^n,
  \qquad \alpha_k = \frac{(2\pi i)^k}{\zeta(k) (k-1)!} $$
(`hasSum_E2`, `hasSum_E₄`), with `ζ(2)` and `ζ(4)` left unevaluated. These come from mathlib's
`EisensteinSeries.G2_eq_tsum_cexp` (as `E2 = G₂ / (2ζ(2))`) and
`EisensteinSeries.q_expansion_riemannZeta`, that is, from Lipschitz's formula, which the note
derives from Euler's partial fraction expansion of the cotangent. The Basel problem is the
evaluation `α₂ = -24` (`baselProblem_of_α_two`).

If `D E₂ = κ (E₂² - E₄)` for a constant `κ`, where `D = (2πi)⁻¹ d/dz = q d/dq`, then comparing the
coefficients of `q` and `q²` gives (`coeff_relations`)
$$ \alpha_2 = \kappa (2\alpha_2 - \alpha_4), \qquad
  6\alpha_2 = \kappa (6\alpha_2 + \alpha_2^2 - 9\alpha_4), $$
using `σ₁(2) = 3` and `σ₃(2) = 9`. The two proofs differ in where this identity comes from.

Nothing here uses the value of any `ζ(2k)`.
-/

@[expose] public section

open UpperHalfPlane hiding I
open Complex EisensteinSeries ModularForm Derivative
open scoped Real Nat ArithmeticFunction.sigma

namespace BaselProblem

local notation "𝕢" => Function.Periodic.qParam 1

/-- The normalizing constant `αₖ = (2πi)ᵏ / (ζ(k) (k - 1)!)`, so that
`Eₖ = 1 + αₖ ∑ σₖ₋₁(n) qⁿ`. The Basel problem is the evaluation `α₂ = -24`. -/
noncomputable def α (k : ℕ) : ℂ := (2 * π * I) ^ k / (riemannZeta k * (k - 1)!)

private lemma qParam_one (τ : ℍ) : 𝕢 τ = cexp (2 * π * I * τ) := by
  simp only [Function.Periodic.qParam, ofReal_one, div_one]

lemma riemannZeta_two_ne_zero : riemannZeta 2 ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re (by norm_num)

lemma α_two : α 2 = -(4 * π ^ 2) / riemannZeta 2 := by
  norm_num [α, mul_pow]

lemma α_two_ne_zero : α 2 ≠ 0 := by
  rw [α_two]
  exact div_ne_zero (by norm_num [Real.pi_ne_zero]) riemannZeta_two_ne_zero

/-- A function equal to `1 + c ∑ σₖ(n) qⁿ` has the `q`-expansion with coefficients `1` and
`c σₖ(m)`. -/
private lemma hasSum_one_add_sigma {f : ℍ → ℂ} {c : ℂ} (k : ℕ) (τ : ℍ)
    (hf : f τ = 1 + c * ∑' n : ℕ, (σ k (n + 1) : ℂ) * 𝕢 τ ^ (n + 1)) :
    HasSum (fun m : ℕ ↦ (if m = 0 then 1 else c * σ k m) • 𝕢 τ ^ m) (f τ) :=
  (hasSum_nat_add_iff' 1).mp <| by
    simpa only [hf, qParam_one, Nat.add_one_ne_zero, ↓reduceIte, smul_eq_mul, mul_assoc,
      Finset.sum_range_one, pow_zero, one_mul, add_sub_cancel_left, Nat.add_one_sub_one] using
      ((summable_nat_add_iff 1).2 (summable_sigma_mul_cexp_pow k.add_one_pos τ)).hasSum.mul_left c

/-- `E₂ = 1 + α₂ ∑ σ₁(n) qⁿ`, read off from the `q`-expansion of `G₂`. -/
lemma hasSum_E2 (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (if m = 0 then 1 else α 2 * σ 1 m) • 𝕢 τ ^ m) (E2 τ) :=
  hasSum_one_add_sigma 1 τ <| by
    rw [E2, Pi.smul_apply, smul_eq_mul, G2_eq_tsum_cexp, qParam_one,
      tsum_pnat_eq_tsum_succ (f := fun n ↦ (σ 1 n : ℂ) * cexp (2 * π * I * τ) ^ n), α_two]
    field [riemannZeta_two_ne_zero]

/-- `E₄ = 1 + α₄ ∑ σ₃(n) qⁿ`. -/
lemma hasSum_E₄ (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (if m = 0 then 1 else α 4 * σ 3 m) • 𝕢 τ ^ m) (E₄ τ) :=
  hasSum_one_add_sigma 3 τ <| by
    simp only [q_expansion_riemannZeta (by norm_num) ⟨2, rfl⟩ τ, zpow_natCast, qParam_one, α,
      tsum_pnat_eq_tsum_succ (f := fun n ↦ (σ 3 n : ℂ) * cexp (2 * π * I * τ) ^ n)]
    ring

/-- **Comparing coefficients.** If `D E₂ = κ (E₂² - E₄)`, then the coefficients of `q` and `q²`
give `α₂ = κ (2α₂ - α₄)` and `6α₂ = κ (6α₂ + α₂² - 9α₄)`. -/
lemma coeff_relations {κ : ℂ} (h : D E2 = κ • (E2 ^ 2 - ⇑E₄)) :
    α 2 = κ * (2 * α 2 - α 4) ∧ 6 * α 2 = κ * (6 * α 2 + α 2 ^ 2 - 9 * α 4) := by
  have hE2 := analyticAt_cuspFunction_zero_of_hasSum_qExpansion one_pos hasSum_E2
  have hE₄ := ModularFormClass.analyticAt_cuspFunction_zero E₄ one_pos one_mem_strictPeriods_SL
  have hsq := cuspFunction_mul hE2.continuousAt hE2.continuousAt ▸ hE2.mul hE2
  have key := qExpansion_coeff_eq_of_hasSum one_pos
    (hasSum_normalizedDerivOfComplex_of_hasSum one_pos hasSum_E2)
  rw [h, sq, qExpansion_smul (cuspFunction_sub hsq.continuousAt hE₄.continuousAt ▸ hsq.sub hE₄),
    qExpansion_sub hsq hE₄, qExpansion_mul hE2 hE2] at key
  have := And.intro (key 1) (key 2)
  norm_num [qExpansion_coeff_eq_of_hasSum one_pos hasSum_E2, PowerSeries.coeff_mul,
    ← ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL hasSum_E₄,
    Finset.Nat.sum_antidiagonal_succ, show σ 1 2 = 3 from rfl, show σ 3 2 = 9 from rfl] at this
  grind

/-- The Basel problem is the evaluation `α₂ = -24`, since `α₂ = (2πi)² / ζ(2) = -4π² / ζ(2)`. -/
lemma baselProblem_of_α_two (h : α 2 = -24) : BaselProblem :=
  Complex.ofReal_injective <| by
    push_cast
    linear_combination (div_eq_iff riemannZeta_two_ne_zero).1 (α_two ▸ h) / 24 -
      zeta_nat_eq_tsum_of_gt_one one_lt_two

end BaselProblem
