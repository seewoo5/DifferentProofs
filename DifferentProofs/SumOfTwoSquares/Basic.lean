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

open Finset

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
  set r := Nat.sqrt p
  have hr : r ^ 2 < p :=
    (Nat.sqrt_le' p).lt_of_ne fun h ↦ hp.prime.not_isSquare ⟨r, by rw [← h, sq]⟩
  obtain ⟨⟨s₁, t₁⟩, hmem₁, ⟨s₂, t₂⟩, hmem₂, hne, hmap⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
    (s := range (r + 1) ×ˢ range (r + 1))
    (by simpa only [card_univ, ZMod.card, card_product, card_range] using Nat.lt_succ_sqrt p)
    (f := fun (s, t) ↦ (s : ZMod p) - u * t) fun _ _ ↦ mem_univ _
  simp only [mem_product, mem_range, ne_eq, Prod.mk.injEq] at hmem₁ hmem₂ hne
  set a : ℤ := (s₁ : ℤ) - s₂ with ha
  set b : ℤ := (t₁ : ℤ) - t₂ with hb
  refine ⟨a.natAbs, b.natAbs, Nat.eq_of_dvd_of_lt_two_mul (fun h0 ↦ ?_) ?_ ?_⟩
  · simp only [sq_add_sq_eq_zero, Int.natAbs_eq_zero] at h0
    lia
  · zify [sq_abs]
    push_cast [ha, hb, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    linear_combination ((s₁ : ZMod p) - s₂ + u * ((t₁ : ZMod p) - t₂)) * hmap -
      ((t₁ : ZMod p) - t₂) ^ 2 * hu
  · linarith [Nat.pow_le_pow_left (show a.natAbs ≤ r by lia) 2,
      Nat.pow_le_pow_left (show b.natAbs ≤ r by lia) 2]

end SumOfTwoSquares
