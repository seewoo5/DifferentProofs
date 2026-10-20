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

/-- `E₂` is holomorphic. Mathlib's `E2_mdifferentiable` is not used: its proof identifies `E₂`
with the logarithmic derivative of `η` using `ζ(2) = π² / 6`. -/
private lemma mdifferentiable_E2 : MDiff E2 :=
  mdifferentiable_of_hasSum_qExpansion one_pos hasSum_E2

/-- `D E₂ - κ E₂²` is invariant under the weight-`4` slash action of `SL(2, ℤ)`: the defects of
`D E₂` and of `E₂²` cancel exactly because `κ` is `ζ(2) / (2π²)`. -/
lemma slash_invariant (γ : SL(2, ℤ)) :
    (D E2 - κ • E2 ^ 2) ∣[(4 : ℤ)] γ = D E2 - κ • E2 ^ 2 := by
  have hD2 : MDiff (D2 γ) := mdifferentiable_const.div (mdifferentiable_denom _) (denom_ne_zero _)
  rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, SL_smul_slash, pow_two,
    ← two_add_two_eq_four, mul_slash_SL2,
    eq_add_of_sub_eq (normalizedDerivOfComplex_SL_slash mdifferentiable_E2).symm]
  ext z
  simp only [E2_slash_action, normalizedDerivOfComplex_D2, normalizedDerivOfComplex_smul _ _ hD2,
    normalizedDerivOfComplex_sub _ _ mdifferentiable_E2 (hD2.const_smul _), Pi.add_apply,
    Pi.sub_apply, Pi.neg_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, mul_inv_rev, inv_I, D2, κ]
  linear_combination (norm := field [riemannZeta_two_ne_zero])
    ((γ 1 0 : ℂ) / denom γ z) ^ 2 / (2 * riemannZeta 2) * I_sq

/-- `E₂` is bounded at `i∞`; mathlib's `EisensteinSeries.isBoundedAtImInfty_E2` is not used, as
its proof goes through `E₂ = 1 - 24 ∑ σ₁(n) qⁿ`, that is, through `ζ(2) = π² / 6`. -/
private lemma isBoundedAtImInfty_E2' : IsBoundedAtImInfty E2 :=
  isBoundedAtImInfty_of_hasSum_qExpansion one_pos hasSum_E2

/-- `E₂ → 1` at `i∞`; mathlib's `EisensteinSeries.tendsto_E2_atImInfty` is not used, for the same
reason. -/
private lemma tendsto_E2 : Tendsto E2 atImInfty (𝓝 1) := by
  simpa only [↓reduceIte] using tendsto_atImInfty_of_hasSum_qExpansion one_pos hasSum_E2

/-- `E₄ → 1` at `i∞`. Mathlib's `EisensteinSeries.tendsto_E_atImInfty` is not used: its proof
evaluates the constant term through Bernoulli numbers, i.e. through `riemannZeta_two_mul_nat`. -/
private lemma tendsto_E₄ : Tendsto E₄ atImInfty (𝓝 1) := by
  simpa only [↓reduceIte] using tendsto_atImInfty_of_hasSum_qExpansion one_pos hasSum_E₄

/-- The difference of the two sides of the unnormalized Ramanujan identity. -/
noncomputable def ramanujanDefect : ℍ → ℂ := D E2 - κ • (E2 ^ 2 - ⇑E₄)

lemma ramanujanDefect_slash (γ : SL(2, ℤ)) : ramanujanDefect ∣[(4 : ℤ)] γ = ramanujanDefect := by
  rw [ramanujanDefect, smul_sub, ← sub_add, SlashAction.add_slash, slash_invariant, SL_smul_slash,
    show ⇑E₄ ∣[(4 : ℤ)] γ = E₄ from slash_action_eqn E₄ _ ⟨γ, rfl⟩]

/-- `D E₂ - κ (E₂² - E₄)` is a cusp form of weight `4`: it is invariant by `slash_invariant`, and
it vanishes at `i∞` because `D E₂ → 0` while `E₂, E₄ → 1`. -/
private noncomputable def ramanujanCuspForm : CuspForm 𝒮ℒ 4 where
  toFun := ramanujanDefect
  slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ ramanujanDefect_slash γ
  holo' := (normalizedDerivOfComplex_mdifferentiable mdifferentiable_E2).sub
    (((mdifferentiable_E2.pow 2).sub E₄.holo').const_smul κ)
  zero_at_cusps' hc := (OnePoint.isZeroAt_iff_forall_SL2Z hc).mpr fun γ _ ↦
    (ramanujanDefect_slash γ).symm ▸ Tendsto.mono_right
      ((isZeroAtImInfty_normalizedDerivOfComplex mdifferentiable_E2 isBoundedAtImInfty_E2').sub
        (((tendsto_E2.pow 2).sub tendsto_E₄).const_smul κ)) (by norm_num)

/-- **Ramanujan's identity, unnormalized**: `D E₂ = (ζ(2) / (2π²)) (E₂² - E₄)`. The cusp form
`ramanujanCuspForm` has weight `4 < 12`, so it vanishes. -/
lemma normalizedDerivOfComplex_E2 : D E2 = κ • (E2 ^ 2 - ⇑E₄) :=
  sub_eq_zero.mp <| congrArg (⇑) <| cuspForm_eq_zero (by norm_num) ramanujanCuspForm

lemma κ_mul_α_two : κ * α 2 = -2 := by grind [κ, α_two, α_two_ne_zero]

/-- Solving the coefficient relations for the unnormalized identity, using `κ α₂ = -2`:
`α₂ (α₂ + 24) = 0`. -/
lemma α_two_eq : α 2 = -24 := by grind [coeff_relations normalizedDerivOfComplex_E2, κ_mul_α_two]

end BaselProblem.RamanujanUnnormalized

open BaselProblem BaselProblem.RamanujanUnnormalized in
theorem BaselProblem_RamanujanUnnormalized : BaselProblem := baselProblem_of_α_two α_two_eq
