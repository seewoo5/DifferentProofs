module

public import DifferentProofs.SumOfTwoSquares.Defs
public import DifferentProofsForMathlib.Combinatorics.Enumerative.Involution
public import Mathlib.Tactic

/-!
# Sum of two squares via Zagier's "one-sentence" proof

Zagier's proof considers the finite set `S = {(x, y, z) ∈ ℕ³ | x, y, z > 0, x² + 4yz = p}` and
the involution

```
(x, y, z) ↦ (x + 2z, z, y - x - z)  if x < y - z
          ↦ (2y - x, y, x - y + z)  if y - z < x < 2y
          ↦ (x - 2y, x - y + z, y)  if x > 2y
```

It has a single fixed point `(1, 1, (p-1)/4)` (using `p ≡ 1 (mod 4)`), so `|S|` is odd. Hence the
simple involution `(x, y, z) ↦ (x, z, y)` also has a fixed point, i.e. some `(x, y, y)` with
`x² + 4y² = p`, giving `p = x² + (2y)²`.

We work in `ℕ`, as Zagier does. Truncated subtraction is harmless above: `x < y - z` still means
`x + z < y`, and every value is nonnegative in its own case. The one exception is the
intermediate `x - y` of the middle case, which truncates when `x < y`; so `x - y + z` is written
`x + z - y`.

Zagier only says "the involution". The popular name "windmill involution" comes from A. Spivak's
geometric reading of a triple as a central `x × x` square with four `y × z` arms attached (his
lecture *Winged squares*, Moscow State University, 2007); such figures are now called windmills.
-/

@[expose] public section

open Finset

namespace SumOfTwoSquares.Zagier

/-! ### Zagier's set and its two involutions -/

/-- Zagier's set `{(x, y, z) ∈ ℕ³ | x, y, z > 0, x² + 4yz = p}`, cut out of a box. -/
private def S (p : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Ioc 0 p ×ˢ Ioc 0 p ×ˢ Ioc 0 p).filter fun (x, y, z) ↦ x ^ 2 + 4 * y * z = p

private lemma mem_S {p x y z : ℕ} :
    (x, y, z) ∈ S p ↔ 0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 2 + 4 * y * z = p := by
  simp only [S, mem_filter, mem_product, mem_Ioc]
  refine ⟨by tauto, fun ⟨hx, hy, hz, h⟩ ↦ ⟨⟨⟨hx, ?_⟩, ⟨hy, ?_⟩, hz, ?_⟩, h⟩⟩ <;> nlinarith

/-- Zagier's involution, with `x - y + z` written `x + z - y` to avoid truncation. -/
private def invol : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun (x, y, z) ↦
  if x < y - z then (x + 2 * z, z, y - x - z)
  else if x < 2 * y then (2 * y - x, y, x + z - y)
  else (x - 2 * y, x + z - y, y)

/-- The involution `(x, y, z) ↦ (x, z, y)`. -/
private def swap : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun (x, y, z) ↦ (x, z, y)

private lemma swap_mem {p : ℕ} : ∀ t ∈ S p, swap t ∈ S p := by
  rintro ⟨x, y, z⟩ ht
  obtain ⟨hx, hy, hz, h⟩ := mem_S.mp ht
  exact mem_S.mpr ⟨hx, hz, hy, by lia⟩

/-- On `S`, a prime `p ≡ 1 (mod 4)` rules out the boundary cases `x = y - z` (else
`p = (x + 2z)²`) and `x = 2y` (else `4 ∣ p`), so `invol` maps `S` to itself. -/
private lemma invol_mem {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) : ∀ t ∈ S p, invol t ∈ S p := by
  rintro ⟨x, y, z⟩ ht
  obtain ⟨hx, hy, hz, h⟩ := mem_S.mp ht
  have h₁ : x + z ≠ y := fun e ↦ hp.prime.not_isSquare ⟨x + 2 * z, by rw [← h, ← e]; ring⟩
  have h₂ : x ≠ 2 * y := by rintro rfl; lia
  simp only [invol]
  split_ifs <;> refine mem_S.mpr ⟨by lia, by lia, by lia, ?_⟩ <;> zify at h ⊢ <;>
    push_cast (disch := lia) [Nat.cast_sub] <;> linear_combination h

private lemma invol_invol {p : ℕ} : ∀ t ∈ S p, invol (invol t) = t := by
  rintro ⟨x, y, z⟩ ht
  obtain ⟨hx, hy, hz, -⟩ := mem_S.mp ht
  simp only [invol]
  split_ifs <;> simp only [Prod.mk.injEq] <;> lia

/-- `invol` has a unique fixed point on `S`, namely `(1, 1, (p-1)/4)`. -/
private lemma invol_fixed {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    (S p).filter (fun t ↦ invol t = t) = {(1, 1, (p - 1) / 4)} := by
  ext ⟨x, y, z⟩
  rw [mem_filter, mem_singleton, mem_S]
  simp only [invol, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hx, hy, hz, h⟩, hfix⟩
    obtain rfl : x = y := by split_ifs at hfix <;> lia
    rw [← h, show x ^ 2 + 4 * x * z = x * (x + 4 * z) by ring, Nat.prime_mul_iff] at hp
    lia
  · rintro ⟨rfl, rfl, rfl⟩
    have := hp.two_le
    exact ⟨⟨one_pos, one_pos, by lia, by lia⟩, by split_ifs <;> lia⟩

end SumOfTwoSquares.Zagier

/-! ### Assembling the proof -/

open SumOfTwoSquares.Zagier in
/-- **Zagier's one-sentence proof** of Fermat's theorem on sums of two squares. -/
theorem FermatSumOfTwoSquares_Zagier : FermatSumOfTwoSquares := by
  intro p hp hp4
  have h := (card_modEq_card_filter_fixed swap_mem fun _ _ ↦ rfl).symm.trans
    (card_modEq_card_filter_fixed (invol_mem hp hp4) invol_invol)
  rw [invol_fixed hp hp4, card_singleton] at h
  obtain ⟨⟨x, y, z⟩, hmem⟩ := card_pos.mp (Nat.odd_iff.mpr h).pos
  rw [mem_filter, mem_S] at hmem
  simp only [swap, Prod.mk.injEq] at hmem
  obtain ⟨⟨-, -, -, h⟩, -, rfl, -⟩ := hmem
  exact ⟨x, 2 * z, by lia⟩
