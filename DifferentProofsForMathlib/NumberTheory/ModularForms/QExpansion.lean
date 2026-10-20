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
statement for bundled functions whose cusp function is known to be analytic at `0`; the version
here derives that analyticity from the `q`-series and applies to any function, such as the
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

/-- The power series `∑ cₘ wᵐ` of a `q`-series that converges on `ℍ` has radius at least `1`. -/
theorem one_le_radius_of_hasSum_qExpansion (hh : 0 < h)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) :
    1 ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius := by
  refine ENNReal.le_of_forall_pos_nnreal_lt fun r hr0 hr1 ↦
    FormalMultilinearSeries.le_radius_of_summable_norm _ ?_
  have hr : (r : ℂ) ≠ 0 := mod_cast hr0.ne'
  have hn : ‖(r : ℂ)‖ = r := Complex.norm_of_nonneg r.coe_nonneg
  simpa only [FormalMultilinearSeries.ofScalars_norm, Periodic.qParam_right_inv hh.ne' hr,
    norm_smul, norm_pow, hn] using (hf ⟨_, Periodic.im_invQParam_pos_of_norm_lt_one hh
      (hn.trans_lt (mod_cast hr1)) hr⟩).summable.norm

/-- A function given on `ℍ` by a convergent `q`-series is the sum of that power series at `q`. -/
theorem eq_sum_ofScalars_of_hasSum_qExpansion
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) (τ : ℍ) :
    f τ = (FormalMultilinearSeries.ofScalars ℂ c).sum (𝕢 h τ) :=
  ((FormalMultilinearSeries.ofScalars_sum_eq c _).trans (hf τ).tsum_eq).symm

/-- A function given on `ℍ` by a convergent `q`-series is holomorphic. -/
theorem mdifferentiable_of_hasSum_qExpansion (hh : 0 < h)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) : MDiff f := by
  rw [funext (eq_sum_ofScalars_of_hasSum_qExpansion hf)]
  refine fun τ ↦ (((FormalMultilinearSeries.ofScalars ℂ c).analyticOnNhd _ ?_).differentiableAt.comp
    _ (Periodic.differentiable_qParam _)).mdifferentiableAt.comp τ (mdifferentiable_coe τ)
  exact mem_eball_zero_iff.2 (((ofReal_norm _).symm.trans_lt (ENNReal.ofReal_lt_one.2
    (Periodic.norm_qParam_lt_one hh τ.im_pos))).trans_le (one_le_radius_of_hasSum_qExpansion hh hf))

/-- A function given on `ℍ` by a convergent `q`-series is `h`-periodic. -/
theorem periodic_comp_ofComplex_of_hasSum_qExpansion
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) : Periodic (f ∘ ofComplex) h :=
  periodic_comp_ofComplex fun τ ↦ (hf _).unique <| by
    simpa only [coe_vadd, add_comm, Periodic.qParam_periodic h _] using hf τ

/-- A function given on `ℍ` by a convergent `q`-series has a cusp function analytic at `0`. -/
theorem analyticAt_cuspFunction_zero_of_hasSum_qExpansion (hh : 0 < h)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) : AnalyticAt ℂ (cuspFunction h f) 0 :=
  analyticAt_cuspFunction_zero hh (periodic_comp_ofComplex_of_hasSum_qExpansion hf)
    (mdifferentiable_of_hasSum_qExpansion hh hf) (isBoundedAtImInfty_of_hasSum_qExpansion hh hf)

/-- The coefficients of a convergent `q`-series on `ℍ` are the `q`-expansion coefficients of its
sum. This is `UpperHalfPlane.qExpansion_coeff_unique` for functions that need not be bundled,
applied through the identity `FunLike` structure on `ℍ → ℂ`. -/
theorem qExpansion_coeff_eq_of_hasSum (hh : 0 < h)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) (m : ℕ) :
    (qExpansion h f).coeff m = c m :=
  letI : FunLike (ℍ → ℂ) ℍ ℂ := ⟨id, injective_id⟩
  (qExpansion_coeff_unique f hh (analyticAt_cuspFunction_zero_of_hasSum_qExpansion hh hf) hf m).symm

end UpperHalfPlane
