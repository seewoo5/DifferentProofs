/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import DifferentProofsForMathlib.Combinatorics.Enumerative.Involution
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Mathlib.Combinatorics.Graph.Delete

/-!
# Pairings of half-edges and the handshake lemma

A multigraph can be described through its **half-edges**, also called **darts**: each edge is cut
into two half-edges, one at each of its ends, a loop having both at the same vertex. Pairing the
half-edges up into edges is a fixed-point-free involution, and attaching each half-edge to a vertex
recovers the multigraph. This is the half-edge description of a graph, as in Serre's definition of
a graph, or in the configuration model of random graphs, where a random multigraph is made by
pairing up half-edges at random.

A `HalfEdgePairing E D` records this description before any vertices are chosen: the half-edges
`D`, the involution `edgePerm` exchanging the two half-edges of each edge, and a labelling `edge` of
the half-edges by the edges `E` whose fibres are these pairs. Attaching the half-edges to vertices,
`lab : D → W`, gives a multigraph `HalfEdgePairing.labelGraph lab : Graph W E`, in which the edge
of a half-edge joins its label to the label of the other half-edge of the edge. Keeping the
attachment separate lets the same half-edges carry several graphs: the darts of a combinatorial
map, attached to vertices, give the graph of the map, and attached to faces, its dual.

The degree of a vertex of `labelGraph lab` is the number of half-edges attached to it, a loop
counting twice. Mathlib's multigraphs have no degrees yet, so the statements below count the
half-edges directly; and they have no walks yet, so `Relation.ReflTransGen (labelGraph lab).Adj`
stands in for reachability.

## Main results

* `HalfEdgePairing.even_card_of_forall_adj`: **the handshake lemma**, for a union of connected
  components. A set of labels closed under adjacency carries an even number of half-edges.
  `HalfEdgePairing.even_card_of_forall_adj_restrict` is the same on the edges of a given set.
* `HalfEdgePairing.exists_ne_reflTransGen_of_odd`: a label carried by an odd number of half-edges
  is joined by a chain of edges to another label carried by an odd number of half-edges.

This file is intended for `Mathlib/Combinatorics/Graph/HalfEdgePairing.lean`.
-/
@[expose] public section

open Finset

/-- A **pairing of half-edges** with edges `E` on the half-edges `D`: the fixed-point-free
involution `edgePerm` exchanging the two half-edges of each edge, together with a labelling `edge`
of the half-edges whose fibres are the orbits of `edgePerm`. -/
structure HalfEdgePairing (E D : Type*) where
  /-- The involution exchanging the two half-edges of each edge. -/
  edgePerm : Equiv.Perm D
  /-- The edge of a half-edge. -/
  edge : D → E
  edgePerm_edgePerm (d : D) : edgePerm (edgePerm d) = d
  edgePerm_ne (d : D) : edgePerm d ≠ d
  edge_eq_edge_iff (d d' : D) : edge d = edge d' ↔ d' = d ∨ d' = edgePerm d
  edge_surjective : Function.Surjective edge

namespace HalfEdgePairing

variable {E D W : Type*} (P : HalfEdgePairing E D)

lemma edge_edgePerm (d : D) : P.edge (P.edgePerm d) = P.edge d :=
  ((P.edge_eq_edge_iff _ _).mpr (.inr rfl)).symm

/-! ### The graph of a labelling of the half-edges -/

/-- The multigraph whose vertices are the labels `lab` of the half-edges and whose edges are those
of the pairing, the edge of a half-edge `d` joining the label of `d` to the label of the other
half-edge of its edge. -/
def labelGraph (lab : D → W) : Graph W E where
  vertexSet := Set.univ
  IsLink e x y := ∃ d, P.edge d = e ∧ lab d = x ∧ lab (P.edgePerm d) = y
  edgeSet := Set.univ
  isLink_symm _ _ := ⟨by grind [edge_eq_edge_iff]⟩
  eq_or_eq_of_isLink_of_isLink := by grind [edge_eq_edge_iff]
  edge_mem_iff_exists_isLink e := by grind [P.edge_surjective e]

lemma labelGraph_isLink {lab : D → W} {e : E} {x y : W} :
    (P.labelGraph lab).IsLink e x y ↔ ∃ d, P.edge d = e ∧ lab d = x ∧ lab (P.edgePerm d) = y :=
  Iff.rfl

lemma labelGraph_isLink_dart (lab : D → W) (d : D) :
    (P.labelGraph lab).IsLink (P.edge d) (lab d) (lab (P.edgePerm d)) :=
  ⟨d, rfl, rfl, rfl⟩

/-! ### The handshake lemma -/

section Handshake

variable [Finite D] (lab : D → W)

/-- **The handshake lemma** on the edges of a set `C`: let `S` be a set of labels closed under
adjacency along the edges of `C`. Then the half-edges of edges of `C` carrying labels in `S` are
evenly many, since the other half-edge of the edge of such a half-edge is one too, and `edgePerm`
pairs them off. -/
theorem even_card_of_forall_adj_restrict (C : Set E) {S : Set W}
    (hS : ∀ ⦃x y⦄, x ∈ S → ((P.labelGraph lab).restrict C).Adj x y → y ∈ S) :
    Even (Nat.card {d // lab d ∈ S ∧ P.edge d ∈ C}) := by
  rw [← Set.coe_ofPred, Nat.card_eq_card_finite_toFinset (Set.toFinite _)]
  refine even_card_of_involution_of_forall_ne (fun d hd ↦ ?_) (fun d _ ↦ P.edgePerm_edgePerm d)
    fun d _ ↦ P.edgePerm_ne d
  rw [Set.Finite.mem_toFinset] at hd ⊢
  exact ⟨hS hd.1 ⟨_, hd.2, P.labelGraph_isLink_dart lab d⟩, P.edge_edgePerm d ▸ hd.2⟩

/-- **The handshake lemma.** A set of labels closed under adjacency in `labelGraph lab`, a union
of connected components, carries an even number of half-edges: the degrees of its vertices add up
to twice the number of its edges. -/
theorem even_card_of_forall_adj {S : Set W}
    (hS : ∀ ⦃x y⦄, x ∈ S → (P.labelGraph lab).Adj x y → y ∈ S) :
    Even (Nat.card {d // lab d ∈ S}) := by
  simpa only [Set.mem_univ, and_true] using
    P.even_card_of_forall_adj_restrict lab Set.univ fun _ _ hx ⟨e, _, he⟩ ↦ hS hx ⟨e, he⟩

/-- **A vertex of odd degree is joined to another one.** A label carried by an odd number of
half-edges is joined by a chain of edges of `labelGraph lab` to a different label carried by an
odd number of half-edges: by the handshake lemma, the labels it reaches carry evenly many
half-edges in all. -/
theorem exists_ne_reflTransGen_of_odd {x : W} (hx : Odd (Nat.card {d // lab d = x})) :
    ∃ y ≠ x, Relation.ReflTransGen (P.labelGraph lab).Adj x y ∧
      Odd (Nat.card {d // lab d = y}) := by
  classical
  by_contra! h
  have hfin : {y | Relation.ReflTransGen (P.labelGraph lab).Adj x y}.Finite :=
    ((Set.finite_range lab).insert x).subset fun y hy ↦
      hy.cases_tail.imp_right fun ⟨_, _, _, _, _, _, hd⟩ ↦ ⟨_, hd⟩
  have heven : Even (Nat.card (lab ⁻¹' hfin.toFinset)) := hfin.coe_toFinset.symm ▸
    P.even_card_of_forall_adj lab fun _ _ hy hyz ↦ hy.tail hyz
  rw [card_preimage_eq_sum_card_image_eq fun _ _ ↦ Set.toFinite _,
    ← add_sum_erase _ _ (hfin.mem_toFinset.2 .refl)] at heven
  exact Nat.not_even_iff_odd.2 (hx.add_even (even_sum _ fun y hy ↦ Nat.not_odd_iff_even.1 <|
    h y (ne_of_mem_erase hy) (hfin.mem_toFinset.1 (mem_of_mem_erase hy)))) heven

end Handshake

end HalfEdgePairing
