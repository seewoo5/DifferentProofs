module

public import DifferentProofs.BaselProblem.Eisenstein
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
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
  (`ramanujanCuspForm`), and cusp forms of weight `4` vanish (`cuspForm_eq_zero`, proved below
  without `ζ(2)`).

Comparing coefficients of `q` and `q²` (`BaselProblem.coeff_relations`) gives
`α₂ = κ (2α₂ - α₄)` and `6α₂ = κ (6α₂ + α₂² - 9α₄)`, the note's two equations with `1/12`
replaced by `κ`. Since `κ α₂ = -2` (`κ_mul_α_two`), they still force `α₂ (α₂ + 24) = 0`, so
`α₂ = -24`, which is the Basel problem.

## Cusp forms of weight less than `12` vanish, without `ζ(2)`

Mathlib's dimension formula for level-one modular forms rests on the modularity of the
discriminant `Δ = η²⁴`, and mathlib proves the transformation `η(-1/z) = √(-iz) η(z)` from that of
`E₂`, using `ζ(2) = π² / 6` to identify a constant. In a proof of the Basel problem that would be
circular, so the transformation of `η²⁴` is proved here the classical way, through theta series:

1. Euler's pentagonal number theorem (`hasSum_eulerFunction_pentagonal`) writes `η` as a theta
   series, `η(z) = ∑ₖ (-1)ᵏ exp (πiz (6k - 1)² / 12)` (`hasSum_eta`).
2. Poisson summation for a Gaussian (`Complex.tsum_exp_neg_quadratic`) turns this into
   `η(z) = (-3iz)^{-1/2} ∑ₙ exp (-πi (2n - 1) / 6) exp (πi (-1/z) (2n - 1)² / 12)`
   (`eta_eq_tsum`).
3. Splitting `n` modulo `3`, the last series is `√3 η(-1/z)` (`tsum_twisted`).
4. Taking `24`th powers, which removes the square root, `η(-1/z)²⁴ = z¹² η(z)²⁴`
   (`eta_neg_one_div_pow`). So `Δ` is invariant under `S` (`discriminant_slash_S`), and with
   mathlib's `T`-invariance it is a cusp form of weight `12` (`discriminantCuspForm`).

Dividing by the nowhere vanishing `Δ` sends a cusp form of weight `k` to a modular form of weight
`k - 12` (`divDiscriminant`, after mathlib's `CuspForm.discriminantEquiv`), so cusp forms of weight
`k < 12` vanish (`cuspForm_eq_zero`). This is the part of the dimension formula that the
unnormalized Ramanujan identity needs.

## Independence from mathlib's `ζ(2) = π² / 6`

Several mathlib results that would be natural inputs here are proved using `ζ(2) = π² / 6`, or
using the evaluation of `ζ(2k)` through Bernoulli numbers, and are avoided: Ramanujan's formula
`Derivative.normalizedDerivOfComplex_E₂`, the holomorphy and boundedness of `E₂`
(`E2_mdifferentiable`, `EisensteinSeries.isBoundedAtImInfty_E2`), the limits
`EisensteinSeries.tendsto_E2_atImInfty` and `EisensteinSeries.tendsto_E_atImInfty`, the
transformations of `η` and `Δ`, and the dimension formula. Their replacements are read off from
the `q`-expansions, in which `ζ(2)` and `ζ(4)` stay unevaluated, and from the theta series above.
The only result used from `Mathlib.NumberTheory.ModularForms.RamanujanFormula` is
`Derivative.normalizedDerivOfComplex_D2`, a direct computation. A traversal of the dependencies of
`BaselProblem_RamanujanUnnormalized` finds no declaration of `Mathlib.NumberTheory.ZetaValues` or
`Mathlib.NumberTheory.LSeries.HurwitzZetaValues`.
-/

@[expose] public section

open UpperHalfPlane hiding I
open Complex ModularForm SlashInvariantForm EisensteinSeries Derivative Function Filter
open scoped Real Topology Manifold MatrixGroups

namespace BaselProblem.RamanujanUnnormalized

/-! ### `η²⁴` and cusp forms of weight less than `12` -/

/-- Splitting a sum over `ℤ` according to the residue of the index modulo `3`. -/
private lemma tsum_int_eq_add_add {g : ℤ → ℂ} (hg : Summable g) :
    ∑' n, g n = ∑' j, g (3 * j) + ∑' j, g (3 * j + 1) + ∑' j, g (3 * j + 2) :=
  (((Int.divModEquiv 3).trans (.prodComm _ _)).symm.tsum_eq g).symm.trans <|
    (hg.comp_injective (Equiv.injective _)).tsum_prod.trans <| by
      norm_num [Fin.sum_univ_three, mul_comm]

/-- **Euler's pentagonal number theorem** for `η`:
`η(z) = ∑ₖ (-1)ᵏ exp (πiz (6k - 1)² / 12)`. -/
lemma hasSum_eta {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun k : ℤ ↦ (-1) ^ k * cexp (π * I * z * (6 * k - 1) ^ 2 / 12)) (η z) :=
  have hq := Periodic.norm_qParam_lt_one one_pos hz
  (eulerFunction_eq_tprod hq ▸ (hasSum_eulerFunction_pentagonal hq).mul_left _).congr_fun fun k ↦ by
    rw [Int.cast_negOnePow, mul_left_comm, Periodic.qParam, Periodic.qParam, ofReal_ofNat,
      ofReal_one, ← exp_nat_mul, ← exp_add]
    congr 2
    linear_combination -π * I * z *
      (mod_cast two_mul_natCast_pentagonal k : (2 * pentagonal k : ℂ) = k * (3 * k - 1))

/-- **Poisson summation** applied to the pentagonal series: the Gaussian `k ↦ exp (3πizk²)` has
Fourier transform `ξ ↦ (-3iz)^{-1/2} exp (πi (-1/z) ξ² / 3)`, and the outcome is
`η(z) = (-3iz)^{-1/2} ∑ₙ exp (-πi (2n - 1) / 6) exp (πi (-1/z) (2n - 1)² / 12)`. -/
lemma eta_eq_tsum {z : ℂ} (hz : 0 < z.im) :
    η z = 1 / (-3 * I * z) ^ (1 / 2 : ℂ) * ∑' n : ℤ,
      cexp (-π * I * (2 * n - 1) / 6) * cexp (π * I * (-1 / z) * (2 * n - 1) ^ 2 / 12) := by
  have h := congr(cexp (π * I * z / 12) *
    $(tsum_exp_neg_quadratic (by norm_num [hz] : 0 < (-3 * I * z).re) (I * (1 - z) / 2)))
  rw [← tsum_mul_left, mul_left_comm (cexp _), ← tsum_mul_left] at h
  grind [I_sq, zero_im, =_ exp_add, =_ exp_int_mul, exp_pi_mul_I, (hasSum_eta hz).tsum_eq]

/-- The twisted series of `eta_eq_tsum` is `√3 η`: split `n` modulo `3`; the classes `3j` and
`3j + 1` both give the pentagonal series of `η` (the second after `j ↦ -j`), with factors
`exp (± πi/6)` adding up to `2 cos (π/6) = √3`, and the class `3j + 2` cancels under
`j ↦ -1 - j`. -/
lemma tsum_twisted {w : ℂ} (hw : 0 < w.im) :
    ∑' n : ℤ, cexp (-π * I * (2 * n - 1) / 6) * cexp (π * I * w * (2 * n - 1) ^ 2 / 12) =
      √3 * η w := by
  rw [tsum_int_eq_add_add ?_, (((hasSum_eta hw).mul_left (cexp (π / 6 * I))).congr_fun fun j ↦ by
      push_cast [← exp_neg_pi_mul_I, ← exp_int_mul, ← exp_add]; ring_nf).tsum_eq,
    ← tsum_comp_neg, (((hasSum_eta hw).mul_left (cexp (-(π / 6) * I))).congr_fun fun j ↦ by
      push_cast [← exp_pi_mul_I, ← exp_int_mul, ← exp_add]; ring_nf).tsum_eq,
    self_eq_neg.mp <| ((Equiv.subLeft (-1)).tsum_eq _).symm.trans <| (tsum_congr fun j ↦ by
      push_cast [Equiv.subLeft_apply, ← exp_add, ← exp_add_pi_mul_I, exp_eq_exp_iff_exists_int]
      exact ⟨j, by ring⟩).trans tsum_neg]
  · linear_combination η w * (2 * (by exact_mod_cast Real.cos_pi_div_six : cos (π / 6) = √3 / 2) -
      two_cos (π / 6))
  · exact (((summable_jacobiTheta₂_term_iff (-(w + 1) / 6) (w / 3)).mpr
      (div_ofNat_im w 3 ▸ div_pos hw three_pos)).mul_left (cexp (π * I * (w + 2) / 12))).congr
      fun n ↦ by simp only [jacobiTheta₂_term, ← exp_add]; ring_nf

/-- **The transformation of `η²⁴`**: `η(-1/z)²⁴ = z¹² η(z)²⁴`. Raising `η = (-iz)^{-1/2} η(-1/z)`
to the `24`th power removes the square root. -/
lemma eta_neg_one_div_pow {z : ℂ} (hz : 0 < z.im) :
    η (-1 / z) ^ 24 = z ^ 12 * η z ^ 24 := by
  rw [pow_mul (η z) 2 12, eta_eq_tsum hz, tsum_twisted (mod_cast im_pnat_div_pos 1 ⟨z, hz⟩)]
  norm_num [field, ← ofReal_pow, mul_pow, ← cpow_nat_mul, ne_zero ⟨z, hz⟩]

/-- `Δ = η²⁴` is invariant under `S`, proved through `eta_neg_one_div_pow` rather than through
mathlib's `ModularForm.discriminant_S_invariant`, whose proof uses `ζ(2) = π² / 6`. -/
lemma discriminant_slash_S : (discriminant ∣[(12 : ℤ)] ModularGroup.S) = discriminant := by
  ext z
  simp only [slash_S_apply, discriminant, ← one_div, div_neg_eq_neg_div', eta_neg_one_div_pow z.2]
  field [z.ne_zero]

/-- `Δ` as a cusp form of weight `12`. This is mathlib's `CuspForm.discriminant`, rebuilt on
`discriminant_slash_S`. -/
noncomputable def discriminantCuspForm : CuspForm 𝒮ℒ 12 where
  toFun := discriminant
  slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦
    hγ ▸ slash_action_generators_SL2Z discriminant_slash_S discriminant_T_invariant γ
  holo' z := ((differentiableAt_eta_of_mem_upperHalfPlaneSet z.2).pow 24).mdifferentiableAt.comp z
    (mdifferentiable_coe z)
  zero_at_cusps' hc := (OnePoint.isZeroAt_iff_forall_SL2Z hc).mpr fun γ _ ↦
    (slash_action_generators_SL2Z discriminant_slash_S discriminant_T_invariant γ).symm ▸
      discriminant_isZeroAtImInfty

/-- `f / Δ` is invariant under the weight `k - 12` slash action of `SL(2, ℤ)`. -/
lemma div_discriminant_slash {k : ℤ} (f : CuspForm 𝒮ℒ k) (γ : SL(2, ℤ)) :
    (fun z ↦ f z / discriminant z) ∣[k - 12] γ = fun z ↦ f z / discriminant z :=
  (div_slash_SL2 k 12 γ f discriminantCuspForm).trans <| congrArg₂ (· / ·)
    (slash_action_eqn f _ ⟨γ, rfl⟩) (slash_action_eqn discriminantCuspForm _ ⟨γ, rfl⟩)

/-- A cusp form of weight `k` divided by `Δ` is a modular form of weight `k - 12`. This is the
forward map of mathlib's `CuspForm.discriminantEquiv`, rebuilt on `discriminantCuspForm`. -/
noncomputable def divDiscriminant {k : ℤ} (f : CuspForm 𝒮ℒ k) : ModularForm 𝒮ℒ (k - 12) where
  toFun z := f z / discriminant z
  slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ div_discriminant_slash f γ
  holo' := f.holo'.div discriminantCuspForm.holo' discriminant_ne_zero
  bdd_at_cusps' hc := (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun γ _ ↦
    (div_discriminant_slash f γ).symm ▸
      (Asymptotics.div_isBoundedUnder_of_isBigO f.exp_decay_isBigO_discriminant).isBigO_one ℝ

/-- Cusp forms of weight `k < 12` vanish: dividing by `Δ` lands in negative weight. -/
lemma cuspForm_eq_zero {k : ℤ} (hk : k < 12) (f : CuspForm 𝒮ℒ k) : f = 0 :=
  CuspForm.ext fun z ↦ (div_eq_zero_iff.1 <| congrFun (ModularFormClass.levelOne_neg_weight_eq_zero
    (by lia) (divDiscriminant f)) z).resolve_right (discriminant_ne_zero z)

/-! ### The unnormalized Ramanujan identity -/

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
