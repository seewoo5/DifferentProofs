/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Data.Finset.Powerset

/-!
# Splitting `Finset.powersetCard` at a distinguished element

Fix `a ∈ s`. The subsets of `s` of a given cardinality split according to whether they contain
`a`. Those that avoid `a` are literally the subsets of `s.erase a` of that cardinality
(`Finset.filter_notMem_powersetCard`), and deleting `a` is a bijection from those that contain
`a` onto the subsets of `s.erase a` with one element fewer
(`Finset.card_filter_mem_powersetCard_succ`).

This is the counting content of Pascal's rule, and the basic move behind bijective proofs of
binomial identities: distinguish an element, then partition by whether a subset uses it.

These lemmas are intended for `Mathlib/Data/Finset/Powerset.lean`, next to
`Finset.powersetCard_succ_insert`.
-/

@[expose] public section

namespace Finset

variable {α : Type*} [DecidableEq α] {s : Finset α} {a : α}

/-- The subsets of `s` of cardinality `k` avoiding `a` are exactly the subsets of `s.erase a`
of cardinality `k`. -/
theorem filter_notMem_powersetCard (s : Finset α) (a : α) (k : ℕ) :
    {S ∈ s.powersetCard k | a ∉ S} = (s.erase a).powersetCard k := by
  ext S; grind

/-- Deleting `a` is a bijection from the `(k + 1)`-element subsets of `s` containing `a` onto the
`k`-element subsets of `s.erase a`, with inverse reinserting `a`. -/
theorem card_filter_mem_powersetCard_succ (ha : a ∈ s) (k : ℕ) :
    #{S ∈ s.powersetCard (k + 1) | a ∈ S} = #((s.erase a).powersetCard k) := by
  refine card_bij' (fun S _ => S.erase a) (fun T _ => insert a T) ?_ ?_ ?_ ?_ <;> grind

end Finset
