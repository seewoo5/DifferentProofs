module

public import DifferentProofs.SumOfTwoSquares.Defs
public import Mathlib.Tactic
public import Mathlib.Data.ZMod.Basic
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

/-! ### A parity lemma for involutions on finite sets -/

set_option linter.unusedDecidableInType false in
/-- A fixed-point-free involution on a finite set has an even number of elements. -/
private lemma even_card_of_fpf {β : Type*} [DecidableEq β] (f : β → β) :
    ∀ s : Finset β, (∀ t ∈ s, f t ∈ s) → (∀ t ∈ s, f (f t) = t) → (∀ t ∈ s, f t ≠ t) →
      Even s.card := by
  intro s
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    intro hmaps hinv hfpf
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact ⟨0, by simp⟩
    · have hfa : f a ∈ s := hmaps a ha
      have hne : f a ≠ a := hfpf a ha
      have hsub : ({a, f a} : Finset β) ⊆ s := by
        intro b hb
        rw [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl
        · exact ha
        · exact hfa
      have hpair : ({a, f a} : Finset β).card = 2 := Finset.card_pair (Ne.symm hne)
      set s' := s \ {a, f a} with hs'def
      have hssub : s' ⊂ s := hs'def ▸ Finset.sdiff_ssubset hsub ⟨a, by simp⟩
      have hmaps' : ∀ t ∈ s', f t ∈ s' := by
        intro t ht
        have hts : t ∈ s := (Finset.mem_sdiff.mp ht).1
        have htni := (Finset.mem_sdiff.mp ht).2
        rw [Finset.mem_insert, Finset.mem_singleton] at htni
        rw [hs'def, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        refine ⟨hmaps t hts, ?_⟩
        rintro (h | h)
        · exact htni (Or.inr (by rw [← hinv t hts, h]))
        · exact htni (Or.inl (by rw [← hinv t hts, h, hinv a ha]))
      have hinv' : ∀ t ∈ s', f (f t) = t := fun t ht => hinv t (Finset.mem_sdiff.mp ht).1
      have hfpf' : ∀ t ∈ s', f t ≠ t := fun t ht => hfpf t (Finset.mem_sdiff.mp ht).1
      have hcard : s.card = s'.card + 2 := by
        have hle : 2 ≤ s.card := hpair ▸ Finset.card_le_card hsub
        have : s'.card = s.card - 2 := by
          rw [hs'def, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hpair]
        omega
      rw [hcard]
      exact (ih s' hssub hmaps' hinv' hfpf').add even_two

set_option linter.unusedDecidableInType false in
/-- For an involution on a finite set, the cardinality of the set and of its fixed-point set
have the same parity. -/
private lemma card_modEq_filter_fixed {β : Type*} [DecidableEq β] (s : Finset β) (f : β → β)
    (hmaps : ∀ t ∈ s, f t ∈ s) (hinv : ∀ t ∈ s, f (f t) = t) :
    (s.filter fun t => f t = t).card ≡ s.card [MOD 2] := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := s) (fun t => f t = t)
  have heven : Even (s.filter fun t => ¬ f t = t).card := by
    refine even_card_of_fpf f _ (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
    · rw [Finset.mem_filter] at ht ⊢
      exact ⟨hmaps t ht.1, by rw [hinv t ht.1]; exact fun h => ht.2 h.symm⟩
    · exact hinv t (Finset.mem_filter.mp ht).1
    · exact (Finset.mem_filter.mp ht).2
  obtain ⟨k, hk⟩ := heven
  change (s.filter fun t => f t = t).card % 2 = s.card % 2
  omega

/-! ### The windmill set and its two involutions -/

/-- Zagier's windmill set `{(x, y, z) | x, y, z > 0, x² + 4yz = p}`, cut out of a box. -/
private noncomputable def S (p : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  ((Finset.Icc 1 (p : ℤ)) ×ˢ (Finset.Icc 1 (p : ℤ)) ×ˢ (Finset.Icc 1 (p : ℤ))).filter
    (fun t => t.1 ^ 2 + 4 * t.2.1 * t.2.2 = (p : ℤ))

private lemma mem_S {p : ℕ} {x y z : ℤ} :
    (x, y, z) ∈ S p ↔ 0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 2 + 4 * y * z = (p : ℤ) := by
  simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨hx1, _⟩, ⟨hy1, _⟩, ⟨hz1, _⟩⟩, heq⟩
    exact ⟨by omega, by omega, by omega, heq⟩
  · rintro ⟨hx, hy, hz, heq⟩
    refine ⟨⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩, ⟨by omega, ?_⟩⟩, heq⟩
    · nlinarith [heq, mul_pos hy hz, mul_nonneg (by omega : (0:ℤ) ≤ x - 1) (by omega : (0:ℤ) ≤ x)]
    · nlinarith [heq, sq_nonneg x, mul_nonneg (by omega : (0:ℤ) ≤ y) (by omega : (0:ℤ) ≤ 4 * z - 1)]
    · nlinarith [heq, sq_nonneg x, mul_nonneg (by omega : (0:ℤ) ≤ z) (by omega : (0:ℤ) ≤ 4 * y - 1)]

/-- On `S`, a prime `p` cannot satisfy `x = y - z` (else `p = (y+z)²`) nor `x = 2y`
(else `4 ∣ p`). -/
private lemma S_ne {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) {x y z : ℤ}
    (h : (x, y, z) ∈ S p) : x ≠ y - z ∧ x ≠ 2 * y := by
  rw [mem_S] at h
  obtain ⟨hx, hy, hz, heq⟩ := h
  refine ⟨fun hxy => ?_, fun hx2 => ?_⟩
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = y + z := ⟨(y + z).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hmp : m ^ 2 = p := by
      have : (m : ℤ) ^ 2 = (p : ℤ) := by rw [hm]; nlinarith [heq, hxy]
      exact_mod_cast this
    have hm2 : 2 ≤ m := by omega
    rcases hp.eq_one_or_self_of_dvd m ⟨m, by rw [← hmp]; ring⟩ with h1 | h1
    · omega
    · rw [h1] at hmp; nlinarith [hp.two_le]
  · have hdvd : (4 : ℤ) ∣ (p : ℤ) := ⟨y * (y + z), by rw [← heq, hx2]; ring⟩
    have : (4 : ℕ) ∣ p := by exact_mod_cast hdvd
    omega

/-- The windmill involution. -/
private noncomputable def wind (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
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
  rw [mem_S] at ht
  obtain ⟨hx, hy, hz, heq⟩ := ht
  rw [swp_eq, mem_S]
  exact ⟨hx, hz, hy, by linear_combination heq⟩

private lemma wind_mem {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) : ∀ t ∈ S p, wind t ∈ S p := by
  rintro ⟨x, y, z⟩ ht
  obtain ⟨hne1, hne2⟩ := S_ne hp hp4 ht
  rw [mem_S] at ht
  obtain ⟨hx, hy, hz, heq⟩ := ht
  rw [wind_eq]
  split_ifs with h1 h2
  · rw [mem_S]; exact ⟨by omega, by omega, by omega, by linear_combination heq⟩
  · rw [mem_S]; exact ⟨by omega, by omega, by omega, by linear_combination heq⟩
  · rw [mem_S]; exact ⟨by omega, by omega, by omega, by linear_combination heq⟩

private lemma wind_invol {p : ℕ} : ∀ t ∈ S p, wind (wind t) = t := by
  rintro ⟨x, y, z⟩ ht
  rw [mem_S] at ht
  obtain ⟨hx, hy, hz, heq⟩ := ht
  rw [wind_eq x y z]
  split_ifs with h1 h2 <;>
    rw [wind_eq] <;> split_ifs <;> rw [Prod.mk.injEq, Prod.mk.injEq] <;> omega

/-- The windmill involution has a unique fixed point on `S`, namely `(1, 1, (p-1)/4)`. -/
private lemma wind_fixed {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    (S p).filter (fun t => wind t = t) = {(1, 1, ((p : ℤ) - 1) / 4)} := by
  have h2 := hp.two_le
  have hp5 : 5 ≤ p := by omega
  ext ⟨x, y, z⟩
  simp only [Finset.mem_filter, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨hS, hfix⟩
    obtain ⟨hne1, hne2⟩ := S_ne hp hp4 hS
    rw [mem_S] at hS
    obtain ⟨hx, hy, hz, heq⟩ := hS
    rw [wind_eq] at hfix
    split_ifs at hfix with h1 h2
    · simp only [Prod.mk.injEq] at hfix; omega
    · simp only [Prod.mk.injEq] at hfix
      obtain ⟨hf1, _, _⟩ := hfix
      have hxy : x = y := by omega
      have hxz : x * (x + 4 * z) = (p : ℤ) := by rw [hxy] at heq ⊢; linear_combination heq
      obtain ⟨a, ha⟩ : ∃ a : ℕ, x = (a : ℤ) := ⟨x.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
      obtain ⟨c, hc⟩ : ∃ c : ℕ, z = (c : ℤ) := ⟨z.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
      have hanat : a * (a + 4 * c) = p := by
        have : (a : ℤ) * ((a : ℤ) + 4 * (c : ℤ)) = (p : ℤ) := by rw [← ha, ← hc]; exact hxz
        exact_mod_cast this
      have ha1 : a = 1 := by
        rcases hp.eq_one_or_self_of_dvd a ⟨a + 4 * c, hanat.symm⟩ with h | h
        · exact h
        · exfalso; rw [h] at hanat; nlinarith [hp5]
      have hcp : 1 + 4 * c = p := by rw [ha1] at hanat; omega
      refine ⟨by rw [ha, ha1]; norm_num, by rw [← hxy, ha, ha1]; norm_num, ?_⟩
      rw [hc]; omega
    · simp only [Prod.mk.injEq] at hfix; omega
  · rintro ⟨hx1, hy1, hz1⟩
    subst hx1 hy1 hz1
    have hzdvd : (4 : ℤ) ∣ ((p : ℤ) - 1) := by
      have h1 : (4 : ℕ) ∣ (p - 1) := by omega
      have h2' : ((p : ℤ) - 1) = ((p - 1 : ℕ) : ℤ) := by omega
      rw [h2']; exact_mod_cast h1
    have h4z : (4 : ℤ) * (((p : ℤ) - 1) / 4) = (p : ℤ) - 1 := Int.mul_ediv_cancel' hzdvd
    refine ⟨?_, ?_⟩
    · rw [mem_S]
      exact ⟨by norm_num, by norm_num, by omega, by nlinarith [h4z]⟩
    · rw [wind_eq]
      split_ifs <;> rw [Prod.mk.injEq, Prod.mk.injEq] <;> omega

/-! ### Assembling the proof -/

theorem FermatSumOfTwoSquares_Zagier : FermatSumOfTwoSquares := by
  intro p hp hp4
  -- The windmill involution has one fixed point, so `|S|` is odd.
  have hpar1 := card_modEq_filter_fixed (S p) wind (wind_mem hp hp4) wind_invol
  rw [wind_fixed hp hp4, Finset.card_singleton] at hpar1
  have hpar1' : 1 % 2 = (S p).card % 2 := hpar1
  -- The swap involution then must have a fixed point.
  have hpar2 := card_modEq_filter_fixed (S p) swp swp_mem (fun t _ => swp_invol t)
  have hpar2' : ((S p).filter fun t => swp t = t).card % 2 = (S p).card % 2 := hpar2
  have hpos : 0 < ((S p).filter fun t => swp t = t).card := by omega
  obtain ⟨⟨x, y, z⟩, hmem⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hmem
  obtain ⟨hS, hfix⟩ := hmem
  rw [mem_S] at hS
  obtain ⟨hx, hy, hz, heq⟩ := hS
  rw [swp_eq] at hfix
  simp only [Prod.mk.injEq] at hfix
  have hyz : y = z := by omega
  refine ⟨x.natAbs, (2 * y).natAbs, ?_⟩
  have hint : ((x.natAbs : ℤ)) ^ 2 + ((2 * y).natAbs : ℤ) ^ 2 = (p : ℤ) := by
    rw [Int.natCast_natAbs, Int.natCast_natAbs, sq_abs, sq_abs]
    rw [← hyz] at heq; linear_combination heq
  exact_mod_cast hint

end SumOfTwoSquares.Zagier
