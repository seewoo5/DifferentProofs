module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Cusp forms of weight less than `12` vanish, without `ζ(2)`

Mathlib's dimension formula for level-one modular forms rests on the modularity of the
discriminant `Δ = η²⁴`, and mathlib proves the transformation `η(-1/z) = √(-iz) η(z)` from that of
`E₂`, using `ζ(2) = π² / 6` to identify a constant. In a proof of the Basel problem that would be
circular, so this file proves the transformation of `η²⁴` the classical way, through theta series:

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
-/

@[expose] public section

open UpperHalfPlane hiding I
open Complex ModularForm SlashInvariantForm Function Filter
open scoped Real MatrixGroups

namespace BaselProblem.RamanujanUnnormalized

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

end BaselProblem.RamanujanUnnormalized
