/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Parity of the number of fixed points of an involution

For an involution `f` of a finite set `s`, the non-fixed points of `f` pair off, so the
cardinality of `s` is congruent mod `2` to the number of fixed points of `f` in `s`. In
particular, a fixed-point-free involution only acts on sets of even cardinality.

These lemmas are the counting backbone of "(sign-reversing) involution" arguments in
enumerative combinatorics, such as Zagier's one-sentence proof of Fermat's theorem on sums of
two squares.

This file is intended for `Mathlib/Combinatorics/Enumerative/Involution.lean`; alternatively
the lemmas could live next to `Finset.prod_involution` if given a `ZMod`-free proof.
-/

public section

namespace Finset

variable {β : Type*} {f : β → β} {s : Finset β}

/-- A fixed-point-free involution on a finite set pairs off its elements, so the set has even
cardinality. -/
theorem even_card_of_involution_of_forall_ne (hmaps : ∀ a ∈ s, f a ∈ s)
    (hinv : ∀ a ∈ s, f (f a) = a) (hne : ∀ a ∈ s, f a ≠ a) : Even s.card := by
  have h : ∑ _a ∈ s, (1 : ZMod 2) = 0 :=
    sum_involution (fun a _ ↦ f a) (fun _ _ ↦ by decide) (fun a ha _ ↦ hne a ha) hmaps hinv
  rw [sum_const, nsmul_eq_mul, mul_one, ZMod.natCast_eq_zero_iff] at h
  exact ⟨s.card / 2, by lia⟩

/-- For an involution `f` on a finite set `s`, the cardinality of `s` is congruent mod `2` to
the number of fixed points of `f` in `s`. -/
theorem card_modEq_card_filter_fixed [DecidableEq β] (hmaps : ∀ a ∈ s, f a ∈ s)
    (hinv : ∀ a ∈ s, f (f a) = a) :
    s.card ≡ (s.filter fun a ↦ f a = a).card [MOD 2] := by
  have hsplit := card_filter_add_card_filter_not (s := s) (fun a ↦ f a = a)
  obtain ⟨k, hk⟩ : Even (s.filter fun a ↦ ¬ f a = a).card := by
    refine even_card_of_involution_of_forall_ne (fun a ha ↦ ?_)
      (fun a ha ↦ hinv a (mem_filter.mp ha).1) fun a ha ↦ (mem_filter.mp ha).2
    rw [mem_filter] at ha ⊢
    exact ⟨hmaps a ha.1, by rw [hinv a ha.1]; exact Ne.symm ha.2⟩
  change _ % 2 = _ % 2
  lia

end Finset
