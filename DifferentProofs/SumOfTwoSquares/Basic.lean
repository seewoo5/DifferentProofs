module

public import DifferentProofs.SumOfTwoSquares.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

/-!
# Shared descent step for the sum-of-two-squares proofs

The quadratic-reciprocity proof and the Wilson proof both reduce to the same fact: once one
knows that `-1` is a square modulo the prime `p`, one recovers `p = a² + b²` by an elementary
descent. This file isolates that descent (a form of **Thue's lemma**) so the two proofs differ
only in how they establish `IsSquare (-1 : ZMod p)`.
-/

@[expose] public section

namespace SumOfTwoSquares

/-- **Thue's descent.** If `-1` is a square modulo a prime `p`, then `p` is a sum of two
squares of natural numbers. The proof is a pigeonhole argument: with `r = ⌊√p⌋`, the `(r+1)²`
pairs `(s, t)` with `0 ≤ s, t ≤ r` cannot inject into `ZMod p` via `(s, t) ↦ s - u·t`, where
`u² = -1`; a collision yields `a, b` with `|a|, |b| ≤ r`, not both zero and `a² + b² ≡ 0`,
whence `0 < a² + b² < 2p` forces `a² + b² = p`. -/
theorem sq_add_sq_of_isSquare_neg_one {p : ℕ} (hp : p.Prime) (h : IsSquare (-1 : ZMod p)) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := h
  have hrr : Nat.sqrt p ^ 2 < p :=
    (Nat.sqrt_le' p).lt_of_ne fun hsq => hp.prime.not_isSquare ⟨_, by rw [← hsq, pow_two]⟩
  have hcard : (Finset.univ : Finset (ZMod p)).card <
      (Finset.range (Nat.sqrt p + 1) ×ˢ Finset.range (Nat.sqrt p + 1)).card := by
    simpa using Nat.lt_succ_sqrt p
  obtain ⟨⟨s₁, t₁⟩, hmem₁, ⟨s₂, t₂⟩, hmem₂, hne, hmap⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := fun st : ℕ × ℕ ↦ (st.1 : ZMod p) - u * (st.2 : ZMod p)) fun _ _ => Finset.mem_univ _
  simp only [Finset.mem_product, Finset.mem_range] at hmem₁ hmem₂
  have hdvd : (p : ℤ) ∣ ((s₁ : ℤ) - s₂) ^ 2 + ((t₁ : ℤ) - t₂) ^ 2 := by
    push_cast [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    linear_combination ((s₁ : ZMod p) - s₂ + u * ((t₁ : ZMod p) - t₂)) * hmap -
      ((t₁ : ZMod p) - t₂) ^ 2 * hu
  set a : ℤ := (s₁ : ℤ) - (s₂ : ℤ) with ha
  set b : ℤ := (t₁ : ℤ) - (t₂ : ℤ) with hb
  refine ⟨a.natAbs, b.natAbs, Nat.eq_of_dvd_of_lt_two_mul (fun h0 => ?_) ?_ ?_⟩
  · simp only [Nat.add_eq_zero_iff, pow_eq_zero_iff two_ne_zero, Int.natAbs_eq_zero] at h0
    exact hne (by simp only [Prod.mk.injEq]; lia)
  · zify [sq_abs]
    exact hdvd
  · nlinarith [Nat.pow_le_pow_left (show a.natAbs ≤ Nat.sqrt p by lia) 2,
      Nat.pow_le_pow_left (show b.natAbs ≤ Nat.sqrt p by lia) 2]

end SumOfTwoSquares
