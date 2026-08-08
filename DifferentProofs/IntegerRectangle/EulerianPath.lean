module

public import DifferentProofs.IntegerRectangle.CornerCount
public import DifferentProofsForMathlib.Algebra.Order.Floor.Ring

/-!
# The integer-rectangle theorem by an Eulerian path

Wagon's seventh proof, due to Michael S. Paterson. Let `Γ` be the graph whose vertices are the
corners of the tiles, two of them joined whenever they are the two ends of a horizontal side of a
tile of integer width, or of a vertical side of a tile of integer height (`IsSide`, `Adj`). A tile
having a vertex as a corner contributes exactly one edge there, so the degree of a vertex is the
number of tiles having it as a corner: `2` or `4` away from the corners of `R`, by the local
picture of how tiles fit together, and `1` at a corner of `R`. A walk that starts at a corner of
`R` and repeats no edge can therefore not stop before it reaches another corner of `R`. Every edge
of `Γ` is a segment of integer length parallel to an axis, so the ends of the walk differ by a
vector with integer entries, and that is an integer side of `R`.

Both ingredients survive here. The walk is `Reachable`, the reflexive-transitive closure of `Adj`;
it preserves the pair of fractional parts of a point (`fracts_eq_of_reachable`), which is the
integrality of the edges. The vertex degrees are used only through their parity, and that parity
is the corner parity of `CornerCount`, so the trail is not built step by step: the corners of the
tiles in the connected component of the lower-left corner of `R` are evenly many, because every
edge of `Γ` has both or neither of its ends in the component, hence so are the corners of `R`
there (`IsTiling.even_sum_cornerCount`). One of them is the lower-left corner itself, so there is
a second one — a corner of `R` reached by a walk (`exists_reachable_corner`).

## Main result

- `IntegerRectangleTheorem_EulerianPath`: Paterson's Eulerian-path proof of the integer-rectangle
  theorem.
-/

@[expose] public section

open Finset

namespace IntegerRectangle.EulerianPath

/-! ### Paterson's graph -/

variable {ι : Type*} {R : Rectangle} {T : ι → Rectangle} {p q : ℝ × ℝ}

/-- `IsSide S p q` says that `p` and `q` are the two ends of one of the two sides of `S` that
Paterson's graph uses: the horizontal sides of `S` when its width is an integer, the vertical
sides when its height is. -/
def IsSide (S : Rectangle) (p q : ℝ × ℝ) : Prop :=
  ((∃ n : ℤ, S.width = n) ∧
      ((p = (S.x₀, S.y₀) ∧ q = (S.x₁, S.y₀)) ∨ (p = (S.x₀, S.y₁) ∧ q = (S.x₁, S.y₁)))) ∨
    ((∃ n : ℤ, S.height = n) ∧
      ((p = (S.x₀, S.y₀) ∧ q = (S.x₀, S.y₁)) ∨ (p = (S.x₁, S.y₀) ∧ q = (S.x₁, S.y₁))))

/-- Adjacency in Paterson's graph `Γ`: two corners of a tile joined by a side of it that `Γ`
uses. -/
def Adj (T : ι → Rectangle) (p q : ℝ × ℝ) : Prop := ∃ i, IsSide (T i) p q ∨ IsSide (T i) q p

/-- There is a walk in `Γ` from `p` to `q`: a chain of points in which consecutive ones are the
ends of a side of a tile that `Γ` uses. -/
def Reachable (T : ι → Rectangle) : ℝ × ℝ → ℝ × ℝ → Prop := Relation.ReflTransGen (Adj T)

private lemma Adj.symm (h : Adj T p q) : Adj T q p := h.imp fun _ ↦ Or.symm

/-! ### The edges of `Γ` have integer length -/

/-- The pair of fractional parts of a point of the plane. Two points share it exactly when they
differ by a vector with integer entries. -/
noncomputable def fracts (p : ℝ × ℝ) : ℝ × ℝ := (Int.fract p.1, Int.fract p.2)

private lemma fracts_eq_of_isSide {S : Rectangle} (h : IsSide S p q) : fracts p = fracts q := by
  obtain ⟨h', ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨h', ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h <;>
    simp [fracts, Int.fract_eq_fract'.mpr h']

private lemma fracts_eq_of_adj (h : Adj T p q) : fracts p = fracts q :=
  h.elim fun _ h ↦ h.elim fracts_eq_of_isSide fun h ↦ (fracts_eq_of_isSide h).symm

/-- **A walk in `Γ` moves by a vector with integer entries.** Each of its edges is a side of a
tile whose length is an integer, and which is parallel to an axis. -/
theorem fracts_eq_of_reachable (h : Reachable T p q) : fracts p = fracts q :=
  Relation.reflTransGen_le_of_equivalence_of_le (r := fun p q ↦ fracts p = fracts q)
    ⟨fun _ ↦ rfl, Eq.symm, Eq.trans⟩ (fun _ _ ↦ fracts_eq_of_adj) p q h

/-! ### The component of the lower-left corner -/

variable [Fintype ι]

open scoped Classical in
/-- The four corners of a rectangle. -/
noncomputable def cornerFinset (S : Rectangle) : Finset (ℝ × ℝ) :=
  {(S.x₀, S.y₀), (S.x₁, S.y₀), (S.x₀, S.y₁), (S.x₁, S.y₁)}

open scoped Classical in
/-- The vertices of `Γ`: the corners of the tiles, together with those of `R`. -/
noncomputable def vertices (R : Rectangle) (T : ι → Rectangle) : Finset (ℝ × ℝ) :=
  cornerFinset R ∪ univ.biUnion fun i ↦ cornerFinset (T i)

open scoped Classical in
/-- The connected component of the lower-left corner of `R` in `Γ`: the vertices that a walk
starting there reaches. -/
noncomputable def component (R : Rectangle) (T : ι → Rectangle) : Finset (ℝ × ℝ) :=
  (vertices R T).filter (Reachable T (R.x₀, R.y₀))

private lemma corner_mem_vertices {i : ι} (hp : p ∈ cornerFinset (T i)) : p ∈ vertices R T :=
  mem_union_right _ (mem_biUnion.mpr ⟨i, mem_univ i, hp⟩)

private lemma mem_component_iff (h : Adj T p q) (hp : p ∈ vertices R T) (hq : q ∈ vertices R T) :
    p ∈ component R T ↔ q ∈ component R T := by
  simp only [component, mem_filter, hp, hq, true_and]
  exact ⟨fun hr ↦ hr.tail h, fun hr ↦ hr.tail h.symm⟩

/-- **Both or neither end of an edge of `Γ` lies in the component**, so a tile has an even number
of corners there: the two ends of each of the sides it contributes to `Γ` go together. -/
private lemma even_sum_cornerCount_tile (hsides : ∀ i, (T i).HasIntegerSide) (i : ι) :
    Even (∑ z ∈ component R T, cornerCount (T i) z.1 z.2) := by
  have key : ∀ {p q : ℝ × ℝ}, IsSide (T i) p q → p ∈ cornerFinset (T i) →
      q ∈ cornerFinset (T i) → (p ∈ component R T ↔ q ∈ component R T) :=
    fun h hp hq ↦ mem_component_iff ⟨i, Or.inl h⟩ (corner_mem_vertices hp) (corner_mem_vertices hq)
  refine even_sum_cornerCount_of_sides _ ((hsides i).imp (fun h ↦ ⟨?_, ?_⟩) fun h ↦ ⟨?_, ?_⟩) <;>
    exact key (by simp [IsSide, h]) (by simp [cornerFinset]) (by simp [cornerFinset])

/-! ### The proof -/

/-- **The walk of Paterson's proof.** A walk in `Γ` leads from the lower-left corner of `R` to
another of its corners. The lower-left corner lies in its own component, so `R` has an odd number
of corners there unless a second one does too; but the tiles have an even number of corners in the
component, and by corner parity so has `R`. -/
theorem exists_reachable_corner (hT : IsTiling R T) (hsides : ∀ i, (T i).HasIntegerSide) :
    Reachable T (R.x₀, R.y₀) (R.x₁, R.y₀) ∨ Reachable T (R.x₀, R.y₀) (R.x₀, R.y₁) ∨
      Reachable T (R.x₀, R.y₀) (R.x₁, R.y₁) := by
  classical
  by_contra! hcon
  have hmem : (R.x₀, R.y₀) ∈ component R T :=
    mem_filter.mpr ⟨mem_union_left _ (by simp [cornerFinset]), .refl⟩
  have hnot : ∀ {z : ℝ × ℝ}, ¬Reachable T (R.x₀, R.y₀) z → z ∉ component R T :=
    fun hz h ↦ hz (mem_filter.mp h).2
  have key := hT.even_sum_cornerCount (even_sum_cornerCount_tile (R := R) hsides)
  rw [sum_cornerCount_eq, if_pos hmem, if_neg (hnot hcon.1), if_neg (hnot hcon.2.1),
    if_neg (hnot hcon.2.2)] at key
  simp at key

/-- **Eulerian-path proof** (Paterson) of the integer-rectangle tiling theorem. A walk in `Γ`
joins the lower-left corner of `R` to another of its corners, and moves by a vector with integer
entries; whichever corner it reaches, that is an integer side of `R`. -/
theorem IntegerRectangleTheorem_EulerianPath : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  obtain h | h | h := exists_reachable_corner hT hsides
  · exact .inl (Int.fract_eq_fract'.mp (congrArg Prod.fst (fracts_eq_of_reachable h)))
  · exact .inr (Int.fract_eq_fract'.mp (congrArg Prod.snd (fracts_eq_of_reachable h)))
  · exact .inl (Int.fract_eq_fract'.mp (congrArg Prod.fst (fracts_eq_of_reachable h)))

end IntegerRectangle.EulerianPath
