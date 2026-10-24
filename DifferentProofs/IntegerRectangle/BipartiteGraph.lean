module

public import DifferentProofs.IntegerRectangle.Tiling.CornerCount
public import DifferentProofsForMathlib.Combinatorics.Graph.Bipartite

/-!
# The integer-rectangle theorem via a bipartite graph

Wagon's eighth proof, his variation on Paterson's Eulerian-path proof. Place `R` in standard
position, let `S` be the set of corners of tiles having both coordinates integers, and let `T` be
the set of tiles. Form a bipartite graph on `S ∪ T` by joining each point of `S` to all the tiles
of which it is a corner. There is an even number of edges, since a tile with an integer side has
`0`, `2` or `4` corners in `S`. But each point of `S` that is not a corner of `R` lies on `2` or `4`
tiles, while the lower-left corner of `R`, which is in `S`, lies on only one; so another point of
`S` lies on an odd number of tiles. That can only be another corner of `R`, and then the width or
the height of `R` is an integer.

The graph is `bipartiteGraph`, a mathlib multigraph. Its vertices are the points of `S`, as
`Sum.inl`, and the tiles, as `Sum.inr`, and its edges are the incidences of the tiles with their
corners: the edge `(i, b)` joins the tile `T i` to its corner `b`, and is an edge of the graph when
that corner is in `S`. The edges at a vertex form its incidence set, and the count of all the
edges from either side is `Graph.IsBipartiteWith.sum_ncard_incidenceSet_eq`. That a point lies on
exactly one tile at a corner of `R`, and on none, two or four tiles anywhere else, is the local
picture of `IsTiling.sum_cornerCount_eq`.

Instead of moving `R` into standard position, `S` is cut out by the lattice through the lower-left
corner of `R` (`OnLattice`).

## Main result

- `IntegerRectangleTheorem_BipartiteGraph`: the bipartite-graph proof of the integer-rectangle
  theorem.
-/

@[expose] public section

open Finset

namespace IntegerRectangle.BipartiteGraph

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-! ### The bipartite graph -/

/-- A point is *on the lattice* of `R` when both of its coordinates differ from those of the
lower-left corner of `R` by integers. Measuring from that corner replaces Wagon's "place `R` in
standard position". -/
def OnLattice (R : Rectangle) (z : ℝ × ℝ) : Prop :=
  (∃ m : ℤ, z.1 - R.x₀ = m) ∧ ∃ n : ℤ, z.2 - R.y₀ = n

/-- Being on the lattice is decided classically, so that `S` can be cut out by a filter. -/
noncomputable instance : DecidablePred (OnLattice R) := Classical.decPred _

/-- Wagon's set `S`: the corners of the tiles lying on the lattice. -/
noncomputable def latticeCorners (R : Rectangle) (T : ι → Rectangle) : Finset (ℝ × ℝ) :=
  {z ∈ univ.image fun d : ι × Bool × Bool ↦ (T d.1).corner d.2 | OnLattice R z}

/-- The points of `S` are on the lattice. -/
lemma onLattice_of_mem {z : ℝ × ℝ} (hz : z ∈ latticeCorners R T) : OnLattice R z :=
  (mem_filter.mp hz).2

/-- A corner of a tile on the lattice is in `S`. -/
lemma corner_mem_latticeCorners {d : ι × Bool × Bool} (h : OnLattice R ((T d.1).corner d.2)) :
    (T d.1).corner d.2 ∈ latticeCorners R T :=
  mem_filter.mpr ⟨mem_image_of_mem _ (mem_univ d), h⟩

/-- **Wagon's bipartite graph** on `S ∪ T`. The edge `(i, b)` joins the corner `b` of the tile
`T i` to the tile, when that corner is on the lattice. -/
def bipartiteGraph (R : Rectangle) (T : ι → Rectangle) :
    Graph ((ℝ × ℝ) ⊕ ι) (ι × Bool × Bool) where
  vertexSet := Sum.inl '' ↑(latticeCorners R T) ∪ Set.range Sum.inr
  IsLink d x y := OnLattice R ((T d.1).corner d.2) ∧
    (x = .inl ((T d.1).corner d.2) ∧ y = .inr d.1 ∨ x = .inr d.1 ∧ y = .inl ((T d.1).corner d.2))
  isLink_symm _ _ := ⟨by grind⟩
  eq_or_eq_of_isLink_of_isLink := by grind
  left_mem_of_isLink _ _ _ := by
    rintro ⟨h, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
    exacts [.inl ⟨_, corner_mem_latticeCorners h, rfl⟩, .inr ⟨_, rfl⟩]

/-- The bipartite graph is bipartite, with the points of `S` on one side and the tiles on the
other. -/
lemma bipartiteGraph_isBipartiteWith : (bipartiteGraph R T).IsBipartiteWith
    ↑((latticeCorners R T).map (.inl (β := ι))) ↑(univ.map (.inr (α := ℝ × ℝ) (β := ι))) :=
  ⟨disjoint_coe.mpr (disjoint_map_inl_map_inr _ _), fun _ _ _ ⟨h, hxy⟩ ↦ by
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [.inl ⟨mem_map_of_mem _ (corner_mem_latticeCorners h), mem_map_of_mem _ (mem_univ _)⟩,
      .inr ⟨mem_map_of_mem _ (mem_univ _), mem_map_of_mem _ (corner_mem_latticeCorners h)⟩]⟩

/-! ### Counting the edges at a tile -/

/-- The edges at a tile are its corners on the lattice. -/
lemma ncard_incidenceSet_inr (i : ι) :
    ((bipartiteGraph R T).incidenceSet (.inr i)).ncard = #{b | OnLattice R ((T i).corner b)} := by
  have : (bipartiteGraph R T).incidenceSet (.inr i) =
      Prod.mk i '' {b | OnLattice R ((T i).corner b)} := by
    ext d
    simp only [Graph.incidenceSet, Graph.Inc, bipartiteGraph, Set.mem_ofPred_eq]
    grind
  rw [this, Set.ncard_image_of_injective _ (Prod.mk_right_injective i),
    Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]

/-- **A tile with an integer side has `0`, `2` or `4` corners on the lattice**, so evenly many
edges: the two ends of a side of integer length have coordinates with the same fractional parts,
so they are on the lattice together or not at all. -/
theorem even_ncard_incidenceSet_inr {i : ι} (h : (T i).HasIntegerSide) :
    Even ((bipartiteGraph R T).incidenceSet (.inr i)).ncard := by
  rcases h with h | h <;> simp only [ncard_incidenceSet_inr, OnLattice, Rectangle.corner,
    ← Int.fract_eq_fract, card_filter, Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte,
    Bool.false_eq_true, Int.fract_eq_fract.mpr h, Nat.even_add]

/-! ### Counting the edges at a point -/

/-- The edges at a point of `S` are the incidences of the tiles with it, so their number is the
number of corners the tiles have there. -/
theorem ncard_incidenceSet_inl {z : ℝ × ℝ} (hz : z ∈ latticeCorners R T) :
    ((bipartiteGraph R T).incidenceSet (.inl z)).ncard = ∑ i, cornerCount (T i) z.1 z.2 := by
  have : (bipartiteGraph R T).incidenceSet (.inl z) = {d | (T d.1).corner d.2 = z} := by
    ext d
    simp only [Graph.incidenceSet, Graph.Inc, bipartiteGraph, Set.mem_ofPred_eq]
    grind [onLattice_of_mem hz]
  simp only [this, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, card_filter,
    Fintype.sum_prod_type, ← card_corner_eq, Prod.mk.eta]

/-- **The lower-left corner of `R` lies on exactly one tile**, and is therefore in `S`. -/
theorem corner_mem (hT : IsTiling R T) :
    (R.x₀, R.y₀) ∈ latticeCorners R T ∧ ∑ i, cornerCount (T i) R.x₀ R.y₀ = 1 := by
  have hsum : ∑ i, cornerCount (T i) R.x₀ R.y₀ = 1 := by
    grind [hT.sum_cornerCount_eq R.x₀ R.y₀, cornerCount, xCount, yCount, hT.x₀_lt_x₁, hT.y₀_lt_y₁]
  obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero (hsum.trans_ne one_ne_zero)
  obtain ⟨b, -, hb⟩ := filter_nonempty_iff.mp (card_ne_zero.mp ((card_corner_eq _ _ _).trans_ne hi))
  exact ⟨hb ▸ corner_mem_latticeCorners (d := (i, b))
    (hb ▸ by simp only [OnLattice, ← Int.fract_eq_fract, and_self]), hsum⟩

/-! ### The proof -/

/-- **Another point of `S` lies on an odd number of tiles.** Counted from the side of the tiles,
the edges of the bipartite graph are evenly many. Counted from the side of `S` they are the
numbers of tiles the points of `S` lie on, and the lower-left corner of `R` lies on only one. -/
theorem exists_odd (hT : IsTiling R T) (hsides : ∀ i, (T i).HasIntegerSide) :
    ∃ z ∈ latticeCorners R T, z ≠ (R.x₀, R.y₀) ∧ Odd (∑ i, cornerCount (T i) z.1 z.2) := by
  obtain ⟨hmem, hone⟩ := corner_mem hT
  have h := bipartiteGraph_isBipartiteWith.sum_ncard_incidenceSet_eq
    (Set.toFinite (bipartiteGraph R T).edgeSet)
  simp only [sum_map, Function.Embedding.inl_apply, Function.Embedding.inr_apply] at h
  rw [sum_congr rfl fun z hz ↦ ncard_incidenceSet_inl hz, ← sum_erase_add _ _ hmem, hone] at h
  by_contra! h'
  exact Nat.even_add_one.mp (h ▸ even_sum _ fun i _ ↦ even_ncard_incidenceSet_inr (hsides i))
    (even_sum _ fun z hz ↦ by grind)

end IntegerRectangle.BipartiteGraph

open IntegerRectangle IntegerRectangle.BipartiteGraph in
/-- **Bipartite-graph proof** (Wagon's variation on Paterson's Eulerian-path proof) of the
integer-rectangle tiling theorem. Another point of `S` lies on an odd number of tiles
(`exists_odd`); a point that is not a corner of `R` lies on none, two or four, so it is another
corner of `R`, and being on the lattice it makes a side of `R` an integer. -/
theorem IntegerRectangleTheorem_BipartiteGraph : IntegerRectangleTheorem := fun _ _ hT hsides ↦ by
  obtain ⟨z, hz, h⟩ := exists_odd hT hsides
  grind [onLattice_of_mem hz, OnLattice, hT.sum_cornerCount_eq z.1 z.2, cornerCount, xCount,
    yCount, Rectangle.HasIntegerSide, Rectangle.width, Rectangle.height]
