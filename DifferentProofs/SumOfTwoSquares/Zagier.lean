module

public import DifferentProofs.SumOfTwoSquares.Defs
public import DifferentProofsForMathlib.Combinatorics.Enumerative.Involution
public import Mathlib.Tactic
public import Mathlib.Data.Int.Interval

/-!
# Sum of two squares via Zagier's "one-sentence" proof

Zagier's proof considers the finite set `S = {(x, y, z) ∈ ℤ³ | x, y, z > 0, x² + 4yz = p}`.
The windmill involution

```
(x, y, z) ↦ (x + 2z, z, y - x - z)  if x < y - z
          ↦ (2y - x, y, x - y + z)  if y - z < x < 2y
          ↦ (x - 2y, x - y + z, y)  if x > 2y
```

has a single fixed point `(1, 1, (p-1)/4)` (using `p ≡ 1 (mod 4)`), so `|S|` is odd. Hence the
simple involution `(x, y, z) ↦ (x, z, y)` also has a fixed point, i.e. some `(x, y, y)` with
`x² + 4y² = p`, giving `p = x² + (2y)²`.
-/

@[expose] public section

namespace SumOfTwoSquares.Zagier

/-! ### The windmill set and its two involutions -/

/-- Zagier's windmill set `{(x, y, z) | x, y, z > 0, x² + 4yz = p}`, cut out of a box. -/
private noncomputable def S (p : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  ((Finset.Icc 1 (p : ℤ)) ×ˢ (Finset.Icc 1 (p : ℤ)) ×ˢ (Finset.Icc 1 (p : ℤ))).filter
    (fun t ↦ t.1 ^ 2 + 4 * t.2.1 * t.2.2 = (p : ℤ))

private lemma mem_S {p : ℕ} {x y z : ℤ} :
    (x, y, z) ∈ S p ↔ 0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 2 + 4 * y * z = (p : ℤ) := by
  simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨hx1, _⟩, ⟨hy1, _⟩, ⟨hz1, _⟩⟩, heq⟩
    exact ⟨by lia, by lia, by lia, heq⟩
  · rintro ⟨hx, hy, hz, heq⟩
    refine ⟨⟨⟨by lia, ?_⟩, ⟨by lia, ?_⟩, ⟨by lia, ?_⟩⟩, heq⟩
    · nlinarith [heq, mul_pos hy hz, mul_nonneg (by lia : (0:ℤ) ≤ x - 1) (by lia : (0:ℤ) ≤ x)]
    · nlinarith [heq, sq_nonneg x, mul_nonneg (by lia : (0:ℤ) ≤ y) (by lia : (0:ℤ) ≤ 4 * z - 1)]
    · nlinarith [heq, sq_nonneg x, mul_nonneg (by lia : (0:ℤ) ≤ z) (by lia : (0:ℤ) ≤ 4 * y - 1)]

/-- On `S`, a prime `p` cannot satisfy `x = y - z` (else `p = (y+z)²`) nor `x = 2y`
(else `4 ∣ p`). -/
private lemma S_ne {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) {x y z : ℤ}
    (h : (x, y, z) ∈ S p) : x ≠ y - z ∧ x ≠ 2 * y := by
  rw [mem_S] at h
  obtain ⟨hx, hy, hz, heq⟩ := h
  constructor
  · rintro rfl
    have hsq : (p : ℤ) = (y + z) * (y + z) := by linear_combination -heq
    rcases (Nat.prime_iff_prime_int.mp hp).irreducible.isUnit_or_isUnit hsq with h1 | h1 <;>
      rw [Int.isUnit_iff] at h1 <;> lia
  · rintro rfl
    have hdvd : (4 : ℤ) ∣ (p : ℤ) := ⟨y * (y + z), by linear_combination -heq⟩
    lia

/-- The windmill involution. -/
private def wind (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  if t.1 < t.2.1 - t.2.2 then (t.1 + 2 * t.2.2, t.2.2, t.2.1 - t.1 - t.2.2)
  else if t.1 < 2 * t.2.1 then (2 * t.2.1 - t.1, t.2.1, t.1 - t.2.1 + t.2.2)
  else (t.1 - 2 * t.2.1, t.1 - t.2.1 + t.2.2, t.2.1)

private lemma wind_eq (x y z : ℤ) :
    wind (x, y, z) =
      if x < y - z then (x + 2 * z, z, y - x - z)
      else if x < 2 * y then (2 * y - x, y, x - y + z)
      else (x - 2 * y, x - y + z, y) := rfl

/-- Zagier's swap involution `(x, y, z) ↦ (x, z, y)`. -/
private def swp (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (t.1, t.2.2, t.2.1)

private lemma swp_eq (x y z : ℤ) : swp (x, y, z) = (x, z, y) := rfl

private lemma swp_invol (t : ℤ × ℤ × ℤ) : swp (swp t) = t := rfl

private lemma swp_mem {p : ℕ} : ∀ t ∈ S p, swp t ∈ S p := by
  rintro ⟨x, y, z⟩ ht
  simp only [swp_eq, mem_S] at ht ⊢
  exact ⟨ht.1, ht.2.2.1, ht.2.1, by linear_combination ht.2.2.2⟩

private lemma wind_mem {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) : ∀ t ∈ S p, wind t ∈ S p := by
  rintro ⟨x, y, z⟩ ht
  obtain ⟨hne1, hne2⟩ := S_ne hp hp4 ht
  rw [mem_S] at ht
  obtain ⟨hx, hy, hz, heq⟩ := ht
  rw [wind_eq]
  split_ifs with h1 h2 <;> rw [mem_S] <;>
    exact ⟨by lia, by lia, by lia, by linear_combination heq⟩

private lemma wind_invol {p : ℕ} : ∀ t ∈ S p, wind (wind t) = t := by
  rintro ⟨x, y, z⟩ ht
  rw [mem_S] at ht
  obtain ⟨hx, hy, hz, -⟩ := ht
  rw [wind_eq x y z]
  split_ifs with h1 h2 <;>
    rw [wind_eq] <;> split_ifs <;> rw [Prod.mk.injEq, Prod.mk.injEq] <;> lia

/-- The windmill involution has a unique fixed point on `S`, namely `(1, 1, (p-1)/4)`. -/
private lemma wind_fixed {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    (S p).filter (fun t ↦ wind t = t) = {(1, 1, ((p : ℤ) - 1) / 4)} := by
  have h2 := hp.two_le
  ext ⟨x, y, z⟩
  simp only [Finset.mem_filter, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨hS, hfix⟩
    rw [mem_S] at hS
    obtain ⟨hx, hy, hz, heq⟩ := hS
    rw [wind_eq] at hfix
    split_ifs at hfix with h1 hm
    · simp only [Prod.mk.injEq] at hfix; lia
    · simp only [Prod.mk.injEq] at hfix
      have hxy : x = y := by lia
      have hxz : x * (x + 4 * z) = (p : ℤ) := by rw [hxy] at heq ⊢; linear_combination heq
      obtain h | h := (Nat.prime_iff_prime_int.mp hp).irreducible.isUnit_or_isUnit hxz.symm <;>
        rw [Int.isUnit_iff] at h
      repeat lia
    · simp only [Prod.mk.injEq] at hfix; lia
  · rintro ⟨rfl, rfl, rfl⟩
    have h4z : (4 : ℤ) * (((p : ℤ) - 1) / 4) = (p : ℤ) - 1 := by lia
    refine ⟨?_, ?_⟩
    · rw [mem_S]
      exact ⟨one_pos, one_pos, by lia, by linear_combination h4z⟩
    · rw [wind_eq]
      split_ifs <;> rw [Prod.mk.injEq, Prod.mk.injEq] <;> lia

/-! ### Assembling the proof -/

end SumOfTwoSquares.Zagier

open SumOfTwoSquares.Zagier in
/-- **Zagier's one-sentence proof** of Fermat's theorem on sums of two squares. -/
theorem FermatSumOfTwoSquares_Zagier : FermatSumOfTwoSquares := by
  intro p hp hp4
  have hpar1 : (S p).card % 2 = 1 % 2 := by
    have h := Finset.card_modEq_card_filter_fixed (wind_mem hp hp4) wind_invol
    rwa [wind_fixed hp hp4, Finset.card_singleton] at h
  have hpar2 : (S p).card % 2 = ((S p).filter fun t ↦ swp t = t).card % 2 :=
    Finset.card_modEq_card_filter_fixed swp_mem fun t _ ↦ swp_invol t
  have hpos : 0 < ((S p).filter fun t ↦ swp t = t).card := by lia
  obtain ⟨⟨x, y, z⟩, hmem⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter, swp_eq, mem_S] at hmem
  obtain ⟨⟨hx, hy, hz, heq⟩, hfix⟩ := hmem
  simp only [Prod.mk.injEq] at hfix
  obtain rfl : y = z := by lia
  refine ⟨x.natAbs, (2 * y).natAbs, ?_⟩
  zify [sq_abs]
  linear_combination heq
