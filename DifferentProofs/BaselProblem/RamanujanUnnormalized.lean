module

public import DifferentProofs.BaselProblem.Eisenstein
public import DifferentProofs.BaselProblem.RamanujanUnnormalized.Eta
public import Mathlib.NumberTheory.ModularForms.RamanujanFormula

/-!
# The Basel problem via the unnormalized Ramanujan identity

This is the argument of Seewoo Lee's note *New(?) proof of Bassel problem*
(https://seewoo5.github.io/jekyll/update/2023/12/04/zeta-eisenstein.html), made independent of the
value of `ζ(2)`.

The note compares coefficients in Ramanujan's identity `D E₂ = (E₂² - E₄) / 12`. As
`E₂ = G₂ / (2ζ(2))` is normalized by the unknown `ζ(2)`, the constant `1/12` is not available in
advance: the identity that can be proved without knowing `ζ(2)` is
$$ D E_2 = \kappa\,(E_2^2 - E_4), \qquad \kappa = \frac{\zeta(2)}{2\pi^2} $$
(`normalizedDerivOfComplex_E2`), and `κ = 1/12` is equivalent to the Basel problem. Its proof is
the standard one.
* Mathlib's `EisensteinSeries.E2_slash_action`, `E₂ ∣[2] γ = E₂ - (2ζ(2))⁻¹ D₂(γ)`, together with
  the slash rule for `D`, makes `D E₂ - κ E₂²` invariant in weight `4`, precisely because
  `κ = ζ(2) / (2π²)` (`slash_invariant`).
* `D E₂ - κ (E₂² - E₄)` tends to `0` at `i∞`, so it is a cusp form of weight `4`
  (`ramanujanCuspForm`), and cusp forms of weight `4` vanish (`cuspForm_eq_zero`, proved without
  `ζ(2)` in `DifferentProofs.BaselProblem.RamanujanUnnormalized.Eta`).

Comparing coefficients of `q` and `q²` (`BaselProblem.coeff_relations`) gives
`α₂ = κ (2α₂ - α₄)` and `6α₂ = κ (6α₂ + α₂² - 9α₄)`, the note's two equations with `1/12`
replaced by `κ`. Since `κ α₂ = -2` (`κ_mul_α_two`), they still force `α₂ (α₂ + 24) = 0`, so
`α₂ = -24`, which is the Basel problem.

## Independence from mathlib's `ζ(2) = π² / 6`

Several mathlib results that would be natural inputs here are proved using `ζ(2) = π² / 6`, or
using the evaluation of `ζ(2k)` through Bernoulli numbers, and are avoided: Ramanujan's formula
`Derivative.normalizedDerivOfComplex_E₂`, the holomorphy and boundedness of `E₂`
(`E2_mdifferentiable`, `EisensteinSeries.isBoundedAtImInfty_E2`), the limits
`EisensteinSeries.tendsto_E2_atImInfty` and `EisensteinSeries.tendsto_E_atImInfty`, the
transformations of `η` and `Δ`, and the dimension formula. Their replacements are read off from
the `q`-expansions, in which `ζ(2)` and `ζ(4)` stay unevaluated, and from
`DifferentProofs.BaselProblem.RamanujanUnnormalized.Eta`. The only result used from
`Mathlib.NumberTheory.ModularForms.RamanujanFormula` is `Derivative.normalizedDerivOfComplex_D2`,
a direct computation. A traversal of the dependencies of `BaselProblem_RamanujanUnnormalized`
finds no declaration of `Mathlib.NumberTheory.ZetaValues` or
`Mathlib.NumberTheory.LSeries.HurwitzZetaValues`.
-/

@[expose] public section

open UpperHalfPlane hiding I
open Complex ModularForm SlashInvariantForm EisensteinSeries Derivative Filter
open scoped Real Topology Manifold MatrixGroups

namespace BaselProblem.RamanujanUnnormalized

/-- The constant in the unnormalized Ramanujan identity, `κ = ζ(2) / (2π²)`. -/
noncomputable def κ : ℂ := riemannZeta 2 / (2 * π ^ 2)

lemma mdifferentiable_E2 : MDiff E2 := mdifferentiable_of_hasSum_qExpansion one_pos hasSum_E2

/-- `D E₂ - κ E₂²` is invariant under the weight-`4` slash action of `SL(2, ℤ)`: the defects of
`D E₂` and of `E₂²` cancel exactly because `κ` is `ζ(2) / (2π²)`. -/
lemma slash_invariant (γ : SL(2, ℤ)) :
    (D E2 - κ • E2 ^ 2) ∣[(4 : ℤ)] γ = D E2 - κ • E2 ^ 2 := by
  have hD2 : MDiff (D2 γ) := mdifferentiable_const.div (mdifferentiable_denom _) (denom_ne_zero _)
  have hD := normalizedDerivOfComplex_SL_slash (k := 2) mdifferentiable_E2 (γ := γ)
  rw [E2_slash_action, normalizedDerivOfComplex_sub _ _ mdifferentiable_E2 (hD2.const_smul _),
    normalizedDerivOfComplex_smul _ _ hD2] at hD
  rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, SL_smul_slash, pow_two,
    show (4 : ℤ) = 2 + 2 from rfl, mul_slash_SL2, E2_slash_action, ← sub_eq_add_neg]
  ext z
  have hz := congrFun hD z
  have hζ := riemannZeta_two_ne_zero
  simp only [one_div, mul_inv_rev, normalizedDerivOfComplex_D2, Fin.isValue, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Int.reduceAdd, Int.cast_ofNat, inv_I, neg_mul, mul_neg, D2,
    sub_neg_eq_add, κ, Pi.mul_apply, Pi.add_apply, Pi.neg_apply] at hz ⊢
  field_simp at hz ⊢
  linear_combination (-(π : ℂ)) * hz + ((γ 1 0 : ℤ) ^ 2 * π ^ 2 : ℂ) * I_sq

lemma isBoundedAtImInfty_E2 : IsBoundedAtImInfty E2 :=
  isBoundedAtImInfty_of_hasSum_qExpansion one_pos hasSum_E2

lemma tendsto_E2 : Tendsto E2 atImInfty (𝓝 1) := by
  simpa only [↓reduceIte] using tendsto_atImInfty_of_hasSum_qExpansion one_pos hasSum_E2

/-- `E₄ → 1` at `i∞`. Mathlib's `EisensteinSeries.tendsto_E_atImInfty` is not used: its proof
evaluates the constant term through Bernoulli numbers, i.e. through `riemannZeta_two_mul_nat`. -/
lemma tendsto_E₄ : Tendsto E₄ atImInfty (𝓝 1) := by
  simpa only [↓reduceIte] using tendsto_atImInfty_of_hasSum_qExpansion one_pos hasSum_E₄

/-- The difference of the two sides of the unnormalized Ramanujan identity. -/
noncomputable def ramanujanDefect : ℍ → ℂ := D E2 - κ • (E2 ^ 2 - ⇑E₄)

lemma ramanujanDefect_slash (γ : SL(2, ℤ)) :
    ramanujanDefect ∣[(4 : ℤ)] γ = ramanujanDefect := by
  have h : ramanujanDefect = (D E2 - κ • E2 ^ 2) + κ • ⇑E₄ := by
    ext z
    simp only [ramanujanDefect, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hγ : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  rw [h, SlashAction.add_slash, slash_invariant, SL_smul_slash, ModularForm.SL_slash,
    slash_action_eqn E₄ _ hγ]

/-- `D E₂ - κ (E₂² - E₄)` is a cusp form of weight `4`: it is invariant by `slash_invariant`, and
it vanishes at `i∞` because `D E₂ → 0` while `E₂, E₄ → 1`. -/
noncomputable def ramanujanCuspForm : CuspForm 𝒮ℒ 4 where
  toFun := ramanujanDefect
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact ramanujanDefect_slash A
  holo' := (normalizedDerivOfComplex_mdifferentiable mdifferentiable_E2).sub
    (((mdifferentiable_E2.pow 2).sub E₄.holo').const_smul κ)
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [ramanujanDefect_slash]
    have h := (isZeroAtImInfty_normalizedDerivOfComplex mdifferentiable_E2
      isBoundedAtImInfty_E2).sub (((tendsto_E2.pow 2).sub
        tendsto_E₄).const_smul κ)
    rw [one_pow, sub_self, smul_zero, sub_zero] at h
    exact h

/-- **Ramanujan's identity, unnormalized**: `D E₂ = (ζ(2) / (2π²)) (E₂² - E₄)`. The cusp form
`ramanujanCuspForm` has weight `4 < 12`, so it vanishes. -/
theorem normalizedDerivOfComplex_E2 : D E2 = κ • (E2 ^ 2 - ⇑E₄) := by
  have h : ramanujanDefect = 0 := congrArg (⇑) (cuspForm_eq_zero (by norm_num) ramanujanCuspForm)
  exact sub_eq_zero.mp h

lemma κ_mul_α_two : κ * α 2 = -2 := by
  rw [κ, α_two]
  field_simp [riemannZeta_two_ne_zero]
  norm_num

/-- Solving the coefficient relations for the unnormalized identity, using `κ α₂ = -2`:
`α₂ (α₂ + 24) = 0`. -/
theorem α_two_eq : α 2 = -24 := by
  obtain ⟨h1, h2⟩ := coeff_relations normalizedDerivOfComplex_E2
  have h : α 2 * (α 2 + 24) = 0 := by
    linear_combination 9 * α 2 * h1 - α 2 * h2 + (12 * α 2 - α 2 ^ 2) * κ_mul_α_two
  exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp h).resolve_left α_two_ne_zero)

end BaselProblem.RamanujanUnnormalized

open BaselProblem BaselProblem.RamanujanUnnormalized in
theorem BaselProblem_RamanujanUnnormalized : BaselProblem := baselProblem_of_α_two α_two_eq
