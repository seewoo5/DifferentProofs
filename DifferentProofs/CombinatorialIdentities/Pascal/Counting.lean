module

public import DifferentProofs.CombinatorialIdentities.Defs
public import DifferentProofsForMathlib.Data.Finset.Powerset

@[expose] public section

open Finset

/-- **Pascal's rule**, by counting the `(k + 1)`-element subsets of `{0, 1, …, n}` in two ways:
directly, and after splitting them according to whether they contain the distinguished element
`n`. Those that do biject with the `k`-element subsets of `{0, 1, …, n - 1}` by deleting `n`;
those that do not are exactly the `(k + 1)`-element subsets of `{0, 1, …, n - 1}`. -/
theorem PascalIdentity_counting : PascalIdentity := by
  rw [PascalIdentity]
  intro n k
  calc n.choose k + n.choose (k + 1)
      = #{S ∈ (range (n + 1)).powersetCard (k + 1) | n ∈ S}
        + #{S ∈ (range (n + 1)).powersetCard (k + 1) | n ∉ S} := by
        rw [Finset.card_filter_mem_powersetCard_succ (self_mem_range_succ n),
          Finset.filter_notMem_powersetCard, show (range (n + 1)).erase n = range n by grind]
        simp
    _ = #((range (n + 1)).powersetCard (k + 1)) := Finset.card_filter_add_card_filter_not _
    _ = (n + 1).choose (k + 1) := by simp
