/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import DifferentProofsForMathlib.Combinatorics.Enumerative.Involution
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Combinatorics.Graph.Delete

/-!
# Dart pairings and the handshake lemma

A multigraph can be described through its **darts**, or half-edges: each edge has two darts, one
at each of its ends, a loop having both at the same vertex. A `DartPairing E D` records the edges
`E` on the darts `D`: a fixed-point-free involution `edgePerm` exchanging the two darts of each
edge, and a labelling `edge` of the darts by the edges whose fibres are these pairs. Labelling the
darts by the vertices they sit at, `lab : D → W`, then gives a multigraph
`DartPairing.labelGraph lab : Graph W E`, in which the edge of a dart joins its label to the label
of the other dart of the edge. The darts of a combinatorial map form a dart pairing, labelled by
the vertices for the graph of the map and by the faces for its dual.

The degree of a vertex of `labelGraph lab` is the number of darts carrying it as their label, a
loop counting twice. Mathlib's multigraphs have no degrees yet, so the statements below count the
darts directly; and they have no walks yet, so `Relation.ReflTransGen (labelGraph lab).Adj` stands
in for reachability.

## Main results

* `DartPairing.even_card_of_forall_adj`: **the handshake lemma**, for a union of connected
  components. A set of labels closed under adjacency carries an even number of darts.
  `DartPairing.even_card_of_forall_adj_restrict` is the same on the edges of a given set.
* `DartPairing.exists_ne_reflTransGen_of_odd`: a label carried by an odd number of darts is joined
  by a chain of edges to another label carried by an odd number of darts.

This file is intended for `Mathlib/Combinatorics/Graph/DartPairing.lean`.
-/

@[expose] public section

open Finset

/-- A **dart pairing** with edges `E` on the darts `D`: the fixed-point-free involution `edgePerm`
pairing the two darts of each edge, together with a labelling `edge` of the darts whose fibres are
the orbits of `edgePerm`. -/
structure DartPairing (E D : Type*) where
  /-- The involution exchanging the two darts of each edge. -/
  edgePerm : Equiv.Perm D
  /-- The edge of a dart. -/
  edge : D → E
  edgePerm_edgePerm (d : D) : edgePerm (edgePerm d) = d
  edgePerm_ne (d : D) : edgePerm d ≠ d
  edge_eq_edge_iff (d d' : D) : edge d = edge d' ↔ d' = d ∨ d' = edgePerm d
  edge_surjective : Function.Surjective edge

namespace DartPairing

variable {E D W : Type*} (P : DartPairing E D)

lemma edge_edgePerm (d : D) : P.edge (P.edgePerm d) = P.edge d :=
  ((P.edge_eq_edge_iff _ _).mpr (.inr rfl)).symm

/-! ### The graph of a labelling of the darts -/

/-- The multigraph whose vertices are the labels `lab` of the darts and whose edges are those of
the pairing, the edge of a dart `d` joining the label of `d` to the label of the other dart of its
edge. -/
def labelGraph (lab : D → W) : Graph W E where
  vertexSet := Set.univ
  IsLink e x y := ∃ d, P.edge d = e ∧ lab d = x ∧ lab (P.edgePerm d) = y
  edgeSet := Set.univ
  isLink_symm _ _ := ⟨fun _ _ ⟨d, hd, hx, hy⟩ ↦
    ⟨P.edgePerm d, (P.edge_edgePerm d).trans hd, hy,
      (congrArg lab (P.edgePerm_edgePerm d)).trans hx⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e x y v w ⟨d, rfl, rfl, rfl⟩ ⟨d', hd', rfl, rfl⟩
    rcases (P.edge_eq_edge_iff d d').mp hd'.symm with rfl | rfl
    · exact .inl rfl
    · exact .inr (by rw [P.edgePerm_edgePerm])
  edge_mem_iff_exists_isLink e := by
    obtain ⟨d, rfl⟩ := P.edge_surjective e
    exact iff_of_true trivial ⟨_, _, d, rfl, rfl, rfl⟩
  left_mem_of_isLink _ _ _ _ := trivial

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
adjacency along the edges of `C`. Then the darts of edges of `C` carrying labels in `S` are evenly
many, since the other dart of the edge of such a dart is one too, and `edgePerm` pairs them off. -/
theorem even_card_of_forall_adj_restrict (C : Set E) {S : Set W}
    (hS : ∀ ⦃x y⦄, x ∈ S → ((P.labelGraph lab).restrict C).Adj x y → y ∈ S) :
    Even (Nat.card {d // lab d ∈ S ∧ P.edge d ∈ C}) := by
  classical
  have : Fintype D := Fintype.ofFinite D
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine even_card_of_involution_of_forall_ne (f := P.edgePerm) (fun d hd ↦ ?_)
    (fun d _ ↦ P.edgePerm_edgePerm d) fun d _ ↦ P.edgePerm_ne d
  rw [mem_filter] at hd ⊢
  refine ⟨mem_univ _, hS hd.2.1 ⟨P.edge d, hd.2.2, P.labelGraph_isLink_dart lab d⟩, ?_⟩
  rw [P.edge_edgePerm]
  exact hd.2.2

/-- **The handshake lemma.** A set of labels closed under adjacency in `labelGraph lab`, a union
of connected components, carries an even number of darts: the degrees of its vertices add up to
twice the number of its edges. -/
theorem even_card_of_forall_adj {S : Set W}
    (hS : ∀ ⦃x y⦄, x ∈ S → (P.labelGraph lab).Adj x y → y ∈ S) :
    Even (Nat.card {d // lab d ∈ S}) := by
  simpa only [Set.mem_univ, and_true] using
    P.even_card_of_forall_adj_restrict lab Set.univ fun _ _ hx ⟨e, _, he⟩ ↦ hS hx ⟨e, he⟩

/-- **A vertex of odd degree is joined to another one.** A label carried by an odd number of darts
is joined by a chain of edges of `labelGraph lab` to a different label carried by an odd number of
darts: by the handshake lemma, the labels it reaches carry evenly many darts in all. -/
theorem exists_ne_reflTransGen_of_odd {x : W} (hx : Odd (Nat.card {d // lab d = x})) :
    ∃ y ≠ x, Relation.ReflTransGen (P.labelGraph lab).Adj x y ∧
      Odd (Nat.card {d // lab d = y}) := by
  classical
  have : Fintype D := Fintype.ofFinite D
  by_contra! h
  have heven := P.even_card_of_forall_adj lab
    (S := {y | Relation.ReflTransGen (P.labelGraph lab).Adj x y}) fun _ _ hy hyz ↦ hy.tail hyz
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Set.mem_ofPred_eq] at hx heven h
  set s : Finset D := {d | Relation.ReflTransGen (P.labelGraph lab).Adj x (lab d)}
  -- The labels reached from `x` that carry darts, and the darts carrying each of them.
  have hfib : ∀ y ∈ s.image lab, ({d ∈ s | lab d = y} : Finset D) = ({d | lab d = y} : Finset D) ∧
      Relation.ReflTransGen (P.labelGraph lab).Adj x y := by
    intro y hy
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hy
    refine ⟨?_, (mem_filter.mp hd).2⟩
    ext d'
    simp only [s, mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    intro hd'
    rw [hd']
    exact (mem_filter.mp hd).2
  obtain ⟨d₀, hd₀⟩ := card_pos.mp hx.pos
  have hx' : x ∈ s.image lab :=
    mem_image.mpr ⟨d₀, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hd₀).2 ▸ .refl⟩,
      (mem_filter.mp hd₀).2⟩
  rw [card_eq_sum_card_image lab s, ← add_sum_erase _ _ hx', (hfib x hx').1] at heven
  refine Nat.not_even_iff_odd.mpr (hx.add_even (even_sum _ fun y hy ↦ ?_)) heven
  obtain ⟨hy₁, hy₂⟩ := hfib y (mem_of_mem_erase hy)
  rw [hy₁]
  exact Nat.not_odd_iff_even.mp (h y (ne_of_mem_erase hy) hy₂)

end Handshake

end DartPairing
