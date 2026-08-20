module

public import DifferentProofs.CombinatorialIdentities.Defs
public import DifferentProofsForMathlib.Data.Finset.Powerset

@[expose] public section

open Finset

namespace CombinatorialIdentities.HockeyStick.DoubleCounting

/-- The largest element of a nonempty finite set of naturals is one of its elements. -/
private lemma sup_id_mem {S : Finset ℕ} (hS : S.Nonempty) : S.sup id ∈ S :=
  (S.exists_mem_eq_sup hS id).elim fun _ ⟨hi, h⟩ => h ▸ hi

/-- A `(k + 1)`-element set of naturals has largest element at least `k`, since it is contained
in `{0, 1, …, S.sup id}`. -/
private lemma le_sup_id {S : Finset ℕ} {k : ℕ} (hcard : #S = k + 1) : k ≤ S.sup id := by
  simpa [hcard] using Finset.card_le_card S.subset_range_sup_succ

/-- A `(k + 1)`-element subset of `{0, 1, …, n + k}` has largest element `m` exactly when it is a
subset of `{0, 1, …, m}` containing `m`. Deleting `m` therefore leaves a `k`-element subset of
`{0, 1, …, m - 1}`, so there are `m.choose k` such sets. -/
private lemma card_fiber (n k m : ℕ) (hm : m ≤ n + k) :
    #{S ∈ (range (n + k + 1)).powersetCard (k + 1) | S.sup id = m} = m.choose k := by
  rw [show {S ∈ (range (n + k + 1)).powersetCard (k + 1) | S.sup id = m}
      = {S ∈ (range (m + 1)).powersetCard (k + 1) | m ∈ S} by
    ext S; grind [sup_id_mem, Finset.card_pos, Finset.le_sup]]
  simpa using Finset.card_filter_mem_powersetCard_succ (self_mem_range_succ m) k

/-- Sorting the `(k + 1)`-element subsets of `{0, 1, …, n + k}` by their largest element. -/
private lemma card_eq_sum_fibers (n k : ℕ) :
    #((range (n + k + 1)).powersetCard (k + 1))
      = ∑ m ∈ Icc k (n + k), #{S ∈ (range (n + k + 1)).powersetCard (k + 1) | S.sup id = m} :=
  Finset.card_eq_sum_card_fiberwise fun _ hS => Finset.mem_Icc.mpr
    ⟨le_sup_id (Finset.mem_powersetCard.mp hS).2, Finset.sup_le fun _ hx =>
      Finset.mem_range_succ_iff.mp ((Finset.mem_powersetCard.mp hS).1 hx)⟩

end CombinatorialIdentities.HockeyStick.DoubleCounting

open CombinatorialIdentities.HockeyStick.DoubleCounting in
/-- **Hockey-stick identity**, by counting the `(k + 1)`-element subsets of `{0, 1, …, n + k}`
in two ways: directly, and after partitioning them according to their largest element `m`,
which ranges over `k, k + 1, …, n + k`. -/
theorem HockeyStickIdentity_doubleCounting : HockeyStickIdentity := by
  rw [HockeyStickIdentity]
  intro n k
  calc ∑ i ∈ range (n + 1), (i + k).choose k
      = ∑ m ∈ Icc k (n + k), m.choose k := by
        refine Finset.sum_nbij' (· + k) (· - k) ?_ ?_ ?_ ?_ ?_ <;> grind
    _ = ∑ m ∈ Icc k (n + k), #{S ∈ (range (n + k + 1)).powersetCard (k + 1) | S.sup id = m} :=
        Finset.sum_congr rfl fun m hm => (card_fiber n k m (Finset.mem_Icc.mp hm).2).symm
    _ = #((range (n + k + 1)).powersetCard (k + 1)) := (card_eq_sum_fibers n k).symm
    _ = (n + k + 1).choose (k + 1) := by simp
