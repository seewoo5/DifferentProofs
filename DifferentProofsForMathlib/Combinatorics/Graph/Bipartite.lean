/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Data.Set.Card

/-!
# Bipartite multigraphs

A multigraph is *bipartite* with parts `s` and `t` when they are disjoint and every edge joins a
vertex of `s` to a vertex of `t` (`Graph.IsBipartiteWith`). Its edges can then be counted from
either side: the numbers of edges at the vertices of `s` add up to the number of edges
(`Graph.IsBipartiteWith.sum_ncard_incidenceSet_eq_ncard_edgeSet`), and so do the numbers of edges
at the vertices of `t` (`Graph.IsBipartiteWith.sum_ncard_incidenceSet_eq`).
This is the multigraph counterpart of `SimpleGraph.isBipartiteWith_sum_degrees_eq`. Mathlib's
multigraphs have no degrees yet, so the edges at a vertex are counted through its incidence set,
in which a loop would count once; a bipartite multigraph has no loops.

This file is intended for `Mathlib/Combinatorics/Graph/Bipartite.lean`.
-/

@[expose] public section

open Finset

namespace Graph

variable {α β : Type*} {G : Graph α β} {s t : Set α}

/-- A multigraph is **bipartite** with parts `s` and `t` when they are disjoint and every edge
joins a vertex of `s` to a vertex of `t`. -/
structure IsBipartiteWith (G : Graph α β) (s t : Set α) : Prop where
  /-- The two parts are disjoint. -/
  disjoint : Disjoint s t
  /-- Every edge joins a vertex of `s` to a vertex of `t`. -/
  mem_of_isLink ⦃e : β⦄ ⦃x y : α⦄ : G.IsLink e x y → x ∈ s ∧ y ∈ t ∨ x ∈ t ∧ y ∈ s

/-- The two parts of a bipartite multigraph can be swapped. -/
protected lemma IsBipartiteWith.symm (h : G.IsBipartiteWith s t) : G.IsBipartiteWith t s :=
  ⟨h.disjoint.symm, fun _ _ _ he ↦ (h.mem_of_isLink he).symm⟩

/-- **Counting the edges of a bipartite multigraph from one side.** If the multigraph has finitely
many edges, the numbers of edges at the vertices of `s` add up to the number of edges, since every
edge has exactly one end in `s`. -/
theorem IsBipartiteWith.sum_ncard_incidenceSet_eq_ncard_edgeSet {s : Finset α}
    (h : G.IsBipartiteWith s t) (hE : E(G).Finite) :
    ∑ x ∈ s, (G.incidenceSet x).ncard = E(G).ncard := by
  classical
  have hinc (x : α) : G.incidenceSet x = ↑(hE.toFinset.bipartiteBelow G.Inc x) := by
    ext; grind [mem_incidenceSet, mem_bipartiteBelow, hE.mem_toFinset, Inc.edge_mem]
  simp_rw [hinc, Set.ncard_coe_finset, ← sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow,
    Set.ncard_eq_toFinset_card _ hE, card_eq_sum_ones hE.toFinset]
  refine sum_congr rfl fun e he ↦ ?_
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet (hE.mem_toFinset.mp he)
  exact card_eq_one.mpr ⟨if x ∈ s then x else y, by
    ext; grind [h.mem_of_isLink hxy, h.disjoint, isLink_iff_inc, mem_bipartiteAbove]⟩

/-- **Counting the edges of a bipartite multigraph from either side.** The numbers of edges at the
vertices of `s` and at the vertices of `t` have the same sum, the number of edges. -/
theorem IsBipartiteWith.sum_ncard_incidenceSet_eq {s t : Finset α} (h : G.IsBipartiteWith s t)
    (hE : E(G).Finite) : ∑ x ∈ s, (G.incidenceSet x).ncard = ∑ y ∈ t, (G.incidenceSet y).ncard :=
  (h.sum_ncard_incidenceSet_eq_ncard_edgeSet hE).trans
    (h.symm.sum_ncard_incidenceSet_eq_ncard_edgeSet hE).symm

end Graph
