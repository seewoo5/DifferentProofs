/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import DifferentProofsForMathlib.Analysis.Complex.Periodic
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Functions given by a convergent `q`-series

Let `f : ℍ → ℂ` satisfy `f τ = ∑ cₘ qᵐ` for every `τ`, where `q = exp (2πiτ / h)`. Then the power
series `∑ cₘ wᵐ` converges on the unit disc, so `f` is holomorphic and `h`-periodic, and its
`q`-expansion is `∑ cₘ qᵐ`. Mathlib's `UpperHalfPlane.qExpansion_coeff_unique` proves the last
statement for bundled modular forms; the version here applies to any function, such as the
quasimodular `E₂` and its derivative.

These are intended for `Mathlib/NumberTheory/ModularForms/QExpansion.lean`, next to
`UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion`.
-/

@[expose] public section

open Complex Filter Function
open scoped Real Topology Manifold

namespace UpperHalfPlane

variable {f : ℍ → ℂ} {h : ℝ} {c : ℕ → ℂ}

local notation "𝕢" => Periodic.qParam

/-- A `q`-series that converges on `ℍ` converges absolutely on every disc of radius `r < 1`. -/
theorem summable_norm_mul_pow_of_hasSum_qExpansion (hh : 0 < h)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) : Summable fun m ↦ ‖c m‖ * r ^ m := by
  obtain ⟨s, hrs, hs1⟩ := exists_between hr1
  have hs0 : 0 < s := hr0.trans_lt hrs
  have hs : (s : ℂ) ≠ 0 := mod_cast hs0.ne'
  have hτ := Periodic.im_invQParam_pos_of_norm_lt_one hh
    (by simpa only [norm_real, Real.norm_eq_abs, abs_of_pos hs0] using hs1 : ‖(s : ℂ)‖ < 1) hs
  have := (hf ⟨_, hτ⟩).summable.norm
  simp only [Periodic.qParam_right_inv hh.ne' hs, norm_smul, norm_pow, norm_real,
    Real.norm_eq_abs, abs_of_pos hs0] at this
  exact this.of_nonneg_of_le (fun m ↦ by positivity) fun m ↦ by gcongr

/-- The power series `∑ cₘ wᵐ` of a `q`-series that converges on `ℍ` has radius at least `1`. -/
theorem one_le_radius_of_hasSum_qExpansion (hh : 0 < h)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) :
    1 ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
  lift r to NNReal using hr.ne_top
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  simpa only [FormalMultilinearSeries.norm_apply_eq_norm_coef,
    FormalMultilinearSeries.coeff_ofScalars, NNReal.val_eq_coe] using
    summable_norm_mul_pow_of_hasSum_qExpansion hh hf r.2 (mod_cast hr)

/-- A function given on `ℍ` by a convergent `q`-series is the sum of that power series at `q`. -/
theorem eq_sum_ofScalars_of_hasSum_qExpansion
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) (τ : ℍ) :
    f τ = (FormalMultilinearSeries.ofScalars ℂ c).sum (𝕢 h τ) :=
  (hf τ).tsum_eq.symm.trans (FormalMultilinearSeries.ofScalars_sum_eq c _).symm

/-- A function given on `ℍ` by a convergent `q`-series is holomorphic. -/
theorem mdifferentiable_of_hasSum_qExpansion (hh : 0 < h)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) : MDiff f := by
  rw [mdifferentiable_iff]
  have hrad := one_le_radius_of_hasSum_qExpansion hh hf
  have hd := ((FormalMultilinearSeries.ofScalars ℂ c).hasFPowerSeriesOnBall
    (zero_lt_one.trans_le hrad)).differentiableOn
  intro z hz
  have hq : 𝕢 h z ∈ Metric.eball (0 : ℂ) (FormalMultilinearSeries.ofScalars ℂ c).radius := by
    refine Metric.mem_eball.mpr (lt_of_lt_of_le ?_ hrad)
    simpa only [edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one] using
      Periodic.norm_qParam_lt_one hh hz
  refine (((hd.differentiableAt (Metric.isOpen_eball.mem_nhds hq)).comp z
    (Periodic.differentiable_qParam z)).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  simpa only [comp_apply, ofComplex_apply_of_im_pos hw] using
    eq_sum_ofScalars_of_hasSum_qExpansion hf ⟨w, hw⟩

/-- A function given on `ℍ` by a convergent `q`-series is `h`-periodic. -/
theorem periodic_comp_ofComplex_of_hasSum_qExpansion
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) : Periodic (f ∘ ofComplex) h :=
  periodic_comp_ofComplex fun τ ↦ by
    rw [eq_sum_ofScalars_of_hasSum_qExpansion hf, eq_sum_ofScalars_of_hasSum_qExpansion hf,
      coe_vadd, add_comm, Periodic.qParam_add_self]

/-- The coefficients of a convergent `q`-series on `ℍ` are the `q`-expansion coefficients of its
sum. This is `UpperHalfPlane.qExpansion_coeff_unique` for functions that need not be bundled. -/
theorem qExpansion_coeff_eq_of_hasSum (hh : 0 < h)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) (m : ℕ) :
    (qExpansion h f).coeff m = c m := by
  have han := analyticAt_cuspFunction_zero hh (periodic_comp_ofComplex_of_hasSum_qExpansion hf)
    (mdifferentiable_of_hasSum_qExpansion hh hf) (isBoundedAtImInfty_of_hasSum_qExpansion hh hf)
  have := congr(FormalMultilinearSeries.coeff
    $((hasFPowerSeriesOnBall_cuspFunction hh han hf).hasFPowerSeriesAt.eq_formalMultilinearSeries
      han.hasFPowerSeriesAt) m)
  simp only [FormalMultilinearSeries.coeff_ofScalars] at this
  rw [this, qExpansion_coeff, div_eq_inv_mul]

end UpperHalfPlane
