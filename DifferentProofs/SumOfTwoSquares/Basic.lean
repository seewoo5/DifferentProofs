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

/-- **Thue's descent.** If `-1` is a square modulo a prime `p`, then `p` is a sum of two
squares of natural numbers. The proof is a pigeonhole argument: with `r = ⌊√p⌋`, the `(r+1)²`
pairs `(s, t)` with `0 ≤ s, t ≤ r` cannot inject into `ZMod p` via `(s, t) ↦ s - u·t`, where
`u² = -1`; a collision yields `a, b` with `|a|, |b| ≤ r`, not both zero and `a² + b² ≡ 0`,
whence `0 < a² + b² < 2p` forces `a² + b² = p`. -/
theorem sq_add_sq_of_isSquare_neg_one {p : ℕ} (hp : p.Prime) (h : IsSquare (-1 : ZMod p)) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  obtain ⟨u, hu⟩ := h
  have hu2 : u ^ 2 = -1 := by rw [sq, ← hu]
  set r := Nat.sqrt p with hr
  -- A prime is not a perfect square, so `r * r < p` strictly.
  have hrr : r * r < p := by
    have hle : r * r ≤ p := by rw [hr]; exact Nat.sqrt_le p
    rcases hle.lt_or_eq with hlt | heq
    · exact hlt
    · rcases hp.eq_one_or_self_of_dvd r ⟨r, heq.symm⟩ with h1 | h1
      · rw [h1] at heq; have := hp.two_le; omega
      · rw [h1] at heq; have := hp.two_le; nlinarith
  -- Pigeonhole: the `(r+1)²` pairs cannot inject into `ZMod p`.
  have hcard : (Finset.univ : Finset (ZMod p)).card
      < ((Finset.range (r + 1)) ×ˢ (Finset.range (r + 1))).card := by
    rw [Finset.card_univ, ZMod.card, Finset.card_product, Finset.card_range]
    have h := Nat.lt_succ_sqrt' p
    rw [← hr] at h
    calc p < (r + 1) ^ 2 := h
      _ = (r + 1) * (r + 1) := by ring
  obtain ⟨⟨s₁, t₁⟩, hmem₁, ⟨s₂, t₂⟩, hmem₂, hne, hmap⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := fun st : ℕ × ℕ => (st.1 : ZMod p) - u * (st.2 : ZMod p))
      (fun _ _ => Finset.mem_univ _)
  simp only [Finset.mem_product, Finset.mem_range] at hmem₁ hmem₂
  simp only at hmap
  set a : ℤ := (s₁ : ℤ) - (s₂ : ℤ) with ha
  set b : ℤ := (t₁ : ℤ) - (t₂ : ℤ) with hb
  -- The collision gives `a ≡ u·b (mod p)`, hence `p ∣ a² + b²`.
  have hcong : (a : ZMod p) = u * (b : ZMod p) := by
    rw [ha, hb]; push_cast; linear_combination hmap
  have hzero : ((a ^ 2 + b ^ 2 : ℤ) : ZMod p) = 0 := by
    push_cast; rw [hcong, mul_pow, hu2]; ring
  have hdvdZ : (p : ℤ) ∣ a ^ 2 + b ^ 2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  refine ⟨a.natAbs, b.natAbs, ?_⟩
  have hcast : ((a.natAbs ^ 2 + b.natAbs ^ 2 : ℕ) : ℤ) = a ^ 2 + b ^ 2 := by
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_pow, Int.natCast_natAbs, Int.natCast_natAbs,
      sq_abs, sq_abs]
  have hdvdN : p ∣ a.natAbs ^ 2 + b.natAbs ^ 2 := by
    rw [← Int.natCast_dvd_natCast, hcast]; exact hdvdZ
  -- Bounds: `|a|, |b| ≤ r`, so `a² + b² ≤ 2r² < 2p`.
  have hAr : a.natAbs ≤ r := by omega
  have hBr : b.natAbs ≤ r := by omega
  have hr2 : r ^ 2 < p := by rw [sq]; exact hrr
  have hlt : a.natAbs ^ 2 + b.natAbs ^ 2 < 2 * p := by
    have h1 : a.natAbs ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hAr 2
    have h2 : b.natAbs ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hBr 2
    omega
  -- Positivity: the two pairs differ, so `a² + b² ≠ 0`.
  have hpos : a.natAbs ^ 2 + b.natAbs ^ 2 ≠ 0 := by
    intro h0
    rw [Nat.add_eq_zero_iff] at h0
    have hae : a = 0 := Int.natAbs_eq_zero.mp (by simpa using h0.1)
    have hbe : b = 0 := Int.natAbs_eq_zero.mp (by simpa using h0.2)
    exact hne (by simp only [Prod.mk.injEq]; exact ⟨by omega, by omega⟩)
  exact Nat.eq_of_dvd_of_lt_two_mul hpos hdvdN hlt
