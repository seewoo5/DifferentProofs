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
lemma tsum_int_eq_add_add {g : ℤ → ℂ} (hg : Summable g) :
    ∑' n, g n = ∑' j, g (3 * j) + ∑' j, g (3 * j + 1) + ∑' j, g (3 * j + 2) := by
  have hs (r : ℤ) : Summable fun j : ℤ ↦ g (3 * j + r) :=
    hg.comp_injective fun a b h ↦ by lia
  have hs0 : Summable fun j : ℤ ↦ g (3 * j) := by simpa only [add_zero] using hs 0
  calc ∑' n, g n = ∑' p, (g ∘ (Int.divModEquiv 3).symm) p :=
        ((Int.divModEquiv 3).symm.tsum_eq g).symm
    _ = ∑' j, ∑' r, (g ∘ (Int.divModEquiv 3).symm) (j, r) :=
        (hg.comp_injective (Int.divModEquiv 3).symm.injective).tsum_prod
    _ = ∑' j, (g (3 * j) + g (3 * j + 1) + g (3 * j + 2)) := by
        congr 1
        ext j
        rw [tsum_fintype, Fin.sum_univ_three]
        simp only [Fin.isValue, comp_apply, Int.divModEquiv_symm_apply, Nat.cast_ofNat,
          Fin.coe_ofNat_eq_mod, Nat.zero_mod, CharP.cast_eq_zero, add_zero, Nat.one_mod,
          Nat.cast_one, Nat.mod_succ, mul_comm]
    _ = _ := by rw [(hs0.add (hs 1)).tsum_add (hs 2), hs0.tsum_add (hs 1)]

/-- **Euler's pentagonal number theorem** for `η`:
`η(z) = ∑ₖ (-1)ᵏ exp (πiz (6k - 1)² / 12)`. -/
lemma hasSum_eta {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun k : ℤ ↦ (-1) ^ k * cexp (π * I * z * (6 * k - 1) ^ 2 / 12)) (η z) := by
  have hq : ‖Periodic.qParam 1 z‖ < 1 := Periodic.norm_qParam_lt_one one_pos hz
  have h := (hasSum_eulerFunction_pentagonal hq).mul_left (Periodic.qParam 24 z)
  rw [eulerFunction_eq_tprod hq] at h
  convert h using 1
  · ext k
    have hp : (pentagonal k : ℂ) = k * (3 * k - 1) / 2 := by
      have h2 : ((2 * (pentagonal k : ℤ) : ℤ) : ℂ) = ((k * (3 * k - 1) : ℤ) : ℂ) := by
        rw [two_mul_natCast_pentagonal]
      push_cast at h2
      linear_combination h2 / 2
    rw [Int.cast_negOnePow, Periodic.qParam, Periodic.qParam, ← exp_nat_mul, hp,
      mul_left_comm, ← exp_add]
    congr 2
    push_cast
    ring
  · rfl

/-- **Poisson summation** applied to the pentagonal series: the Gaussian `k ↦ exp (3πizk²)` has
Fourier transform `ξ ↦ (-3iz)^{-1/2} exp (πi (-1/z) ξ² / 3)`, and the outcome is
`η(z) = (-3iz)^{-1/2} ∑ₙ exp (-πi (2n - 1) / 6) exp (πi (-1/z) (2n - 1)² / 12)`. -/
lemma eta_eq_tsum {z : ℂ} (hz : 0 < z.im) :
    η z = 1 / (-3 * I * z) ^ (1 / 2 : ℂ) * ∑' n : ℤ,
      cexp (-π * I * (2 * n - 1) / 6) * cexp (π * I * (-1 / z) * (2 * n - 1) ^ 2 / 12) := by
  have hz0 : z ≠ 0 := fun h ↦ by simp only [h, zero_im, lt_self_iff_false] at hz
  have ha : 0 < (-3 * I * z).re := by norm_num [hz]
  rw [← (hasSum_eta hz).tsum_eq]
  have key (k : ℤ) : (-1) ^ k * cexp (π * I * z * (6 * k - 1) ^ 2 / 12) =
      cexp (π * I * z / 12) *
        cexp (-π * (-3 * I * z) * k ^ 2 + 2 * π * (I * (1 - z) / 2) * k) := by
    rw [← exp_pi_mul_I, ← exp_int_mul, ← exp_add, ← exp_add]
    congr 1
    ring
  simp_rw [key]
  rw [tsum_mul_left, tsum_exp_neg_quadratic ha, ← mul_assoc, mul_comm (cexp _), mul_assoc,
    ← tsum_mul_left]
  congr 2
  ext n
  rw [← exp_add, ← exp_add]
  congr 1
  field_simp
  linear_combination (72 * I ^ 2 * z ^ 2 + 288 * n ^ 2 + 72 * I ^ 2 - 144 * I ^ 2 * z) * I_sq

/-- The twisted series of `eta_eq_tsum` is `√3 η`: split `n` modulo `3`; the classes `3j` and
`3j + 1` both give the pentagonal series of `η` (the second after `j ↦ -j`), with factors
`exp (± πi/6)` adding up to `2 cos (π/6) = √3`, and the class `3j + 2` cancels under
`j ↦ -1 - j`. -/
lemma tsum_twisted {w : ℂ} (hw : 0 < w.im) :
    ∑' n : ℤ, cexp (-π * I * (2 * n - 1) / 6) * cexp (π * I * w * (2 * n - 1) ^ 2 / 12) =
      √3 * η w := by
  set u : ℤ → ℂ := fun m ↦ cexp (π * I * w * m ^ 2 / 12) with hu
  have hneg (j : ℤ) : cexp (-π * I * j) = (-1) ^ j := by
    rw [show -π * I * j = j * (-(π * I)) by ring, exp_int_mul, exp_neg, exp_pi_mul_I, inv_neg_one]
  have hsum : Summable fun n : ℤ ↦
      cexp (-π * I * (2 * n - 1) / 6) * cexp (π * I * w * (2 * n - 1) ^ 2 / 12) := by
    refine (((summable_jacobiTheta₂_term_iff (-(w + 1) / 6) (w / 3)).mpr
      (by rw [div_ofNat_im]; exact div_pos hw three_pos)).mul_left
        (cexp (π * I * w / 12 + π * I / 6))).congr fun n ↦ ?_
    rw [jacobiTheta₂_term, ← exp_add, ← exp_add]
    congr 1
    ring
  have h0 (j : ℤ) : cexp (-π * I * (2 * ↑(3 * j) - 1) / 6) *
      cexp (π * I * w * (2 * ↑(3 * j) - 1) ^ 2 / 12) =
        cexp (π * I / 6) * ((-1) ^ j * u (6 * j - 1)) := by
    rw [← hneg, hu]
    simp only
    rw [← exp_add, ← exp_add, ← exp_add]
    congr 1
    push_cast
    ring
  have h1 (j : ℤ) : cexp (-π * I * (2 * ↑(3 * j + 1) - 1) / 6) *
      cexp (π * I * w * (2 * ↑(3 * j + 1) - 1) ^ 2 / 12) =
        cexp (-π * I / 6) * ((-1) ^ j * u (6 * j + 1)) := by
    rw [← hneg, hu]
    simp only
    rw [← exp_add, ← exp_add, ← exp_add]
    congr 1
    push_cast
    ring
  have h2 (j : ℤ) : cexp (-π * I * (2 * ↑(3 * j + 2) - 1) / 6) *
      cexp (π * I * w * (2 * ↑(3 * j + 2) - 1) ^ 2 / 12) = -I * ((-1) ^ j * u (6 * j + 3)) := by
    rw [← hneg, hu, ← exp_neg_pi_div_two_mul_I]
    simp only
    rw [← exp_add, ← exp_add, ← exp_add]
    congr 1
    push_cast
    ring
  have hnegpow (j : ℤ) : (-1 : ℂ) ^ (-j) = (-1) ^ j := by rw [zpow_neg, ← inv_zpow, inv_neg_one]
  have r1 : ∑' j : ℤ, (-1) ^ j * u (6 * j + 1) = ∑' j : ℤ, (-1) ^ j * u (6 * j - 1) := by
    rw [← (Equiv.neg ℤ).tsum_eq]
    congr 1
    ext j
    rw [Equiv.neg_apply, hnegpow, hu]
    push_cast
    ring_nf
  have r2 : ∑' j : ℤ, (-1) ^ j * u (6 * j + 3) = 0 := by
    have h := (Equiv.subLeft (-1 : ℤ)).tsum_eq fun j ↦ (-1) ^ j * u (6 * j + 3)
    have hr (j : ℤ) : (-1 : ℂ) ^ (Equiv.subLeft (-1) j) * u (6 * Equiv.subLeft (-1) j + 3) =
        -((-1) ^ j * u (6 * j + 3)) := by
      rw [Equiv.subLeft_apply, show (-1 : ℤ) - j = -(1 + j) by ring, hnegpow,
        zpow_add₀ (by norm_num), zpow_one, hu]
      push_cast
      ring_nf
    simp only [hr, tsum_neg] at h
    linear_combination -h / 2
  have hη : η w = ∑' j : ℤ, (-1) ^ j * u (6 * j - 1) := by
    rw [← (hasSum_eta hw).tsum_eq, hu]
    push_cast
    rfl
  have hcos : cexp (π * I / 6) + cexp (-π * I / 6) = √3 := by
    have h := Complex.cos.eq_def (π / 6)
    have hc : Complex.cos (π / 6) = (√3 / 2 : ℝ) := by
      rw [← Real.cos_pi_div_six]
      push_cast
      rfl
    rw [hc] at h
    push_cast at h
    rw [show (π : ℂ) * I / 6 = π / 6 * I by ring, show -(π : ℂ) * I / 6 = -(π / 6) * I by ring]
    linear_combination -2 * h
  rw [tsum_int_eq_add_add hsum, tsum_congr h0, tsum_congr h1, tsum_congr h2, tsum_mul_left,
    tsum_mul_left, tsum_mul_left, r1, r2, ← hη, ← hcos]
  ring

/-- **The transformation of `η²⁴`**: `η(-1/z)²⁴ = z¹² η(z)²⁴`. Raising `η = (-iz)^{-1/2} η(-1/z)`
to the `24`th power removes the square root. -/
lemma eta_neg_one_div_pow {z : ℂ} (hz : 0 < z.im) :
    η (-1 / z) ^ 24 = z ^ 12 * η z ^ 24 := by
  have hz0 : z ≠ 0 := fun h ↦ by simp only [h, zero_im, lt_self_iff_false] at hz
  have hw : 0 < (-1 / z).im := by
    rw [neg_div, neg_im, one_div, inv_im, neg_div, neg_neg]
    exact div_pos hz (normSq_pos.mpr hz0)
  have h := eta_eq_tsum hz
  rw [tsum_twisted hw] at h
  have hx : ((-3 * I * z) ^ (1 / 2 : ℂ)) ^ 24 = (-3 * I * z) ^ 12 := by
    rw [← cpow_nat_mul]
    norm_num
  have h3 : (√3 : ℂ) ^ 24 = 3 ^ 12 := by
    rw [show 24 = 2 * 12 by rfl, pow_mul, ← ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hI : I ^ 12 = 1 := by rw [show 12 = 4 * 3 by rfl, pow_mul, I_pow_four, one_pow]
  have h24 := congrArg (· ^ 24) h
  simp only [div_pow, mul_pow, one_pow, hx, h3, hI] at h24
  rw [h24]
  field_simp

/-- `Δ = η²⁴` is invariant under `S`, proved through `eta_neg_one_div_pow` rather than through
mathlib's `ModularForm.discriminant_S_invariant`, whose proof uses `ζ(2) = π² / 6`. -/
lemma discriminant_slash_S : (discriminant ∣[(12 : ℤ)] ModularGroup.S) = discriminant := by
  ext z
  suffices η (-(↑z)⁻¹) ^ 24 * ((z : ℂ) ^ 12)⁻¹ = η z ^ 24 by
    rw [SL_slash_apply, UpperHalfPlane.modular_S_smul, ModularGroup.denom_S]
    simpa only [discriminant, inv_neg, Int.reduceNeg, zpow_neg, zpow_ofNat] using this
  rw [← one_div, ← neg_div, eta_neg_one_div_pow z.im_pos]
  field_simp [z.ne_zero]

/-- `Δ` as a cusp form of weight `12`. This is mathlib's `CuspForm.discriminant`, rebuilt on
`discriminant_slash_S`. -/
noncomputable def discriminantCuspForm : CuspForm 𝒮ℒ 12 where
  toFun := discriminant
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact slash_action_generators_SL2Z discriminant_slash_S discriminant_T_invariant A
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine .congr (fun z hz ↦ (differentiableAt_eta_of_mem_upperHalfPlaneSet hz).pow
      24 |>.differentiableWithinAt) fun z hz ↦ ?_
    simp only [SlashInvariantForm.coe_mk, comp_apply, discriminant,
      UpperHalfPlane.ofComplex_apply_of_im_pos hz, Pi.pow_apply]
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slash_action_generators_SL2Z discriminant_slash_S discriminant_T_invariant]
    exact discriminant_isZeroAtImInfty

lemma div_discriminant_slash {k : ℤ} (f : CuspForm 𝒮ℒ k) (γ : SL(2, ℤ)) :
    (fun z ↦ f z / discriminant z) ∣[k - 12] γ = fun z ↦ f z / discriminant z := by
  have hγ : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  change (⇑f / ⇑discriminantCuspForm) ∣[k - 12] γ = ⇑f / ⇑discriminantCuspForm
  simp_rw [div_slash_SL2, ModularForm.SL_slash, slash_action_eqn _ _ hγ]

/-- A cusp form of weight `k` divided by `Δ` is a modular form of weight `k - 12`. This is the
forward map of mathlib's `CuspForm.discriminantEquiv`, rebuilt on `discriminantCuspForm`. -/
noncomputable def divDiscriminant {k : ℤ} (f : CuspForm 𝒮ℒ k) : ModularForm 𝒮ℒ (k - 12) where
  toFun z := f z / discriminant z
  slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ div_discriminant_slash f γ
  holo' := f.holo'.div discriminantCuspForm.holo' discriminant_ne_zero
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [div_discriminant_slash f γ, IsBoundedAtImInfty, BoundedAtFilter]
    exact (Asymptotics.div_isBoundedUnder_of_isBigO
      (CuspForm.exp_decay_isBigO_discriminant f)).isBigO_one ℝ

/-- Cusp forms of weight `k < 12` vanish: dividing by `Δ` lands in negative weight. -/
lemma cuspForm_eq_zero {k : ℤ} (hk : k < 12) (f : CuspForm 𝒮ℒ k) : f = 0 := by
  ext z
  have h : f z / discriminant z = 0 :=
    congrFun (ModularFormClass.levelOne_neg_weight_eq_zero (by lia) (divDiscriminant f)) z
  simpa only [zero_apply, div_eq_zero_iff, discriminant_ne_zero z, or_false] using h

end BaselProblem.RamanujanUnnormalized
