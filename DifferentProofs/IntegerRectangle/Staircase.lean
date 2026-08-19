module

public import DifferentProofs.IntegerRectangle.Walks
public import DifferentProofs.IntegerRectangle.GridRefinement

/-!
# The integer-rectangle theorem by induction on the number of H-tiles

Robinson's ninth proof. Call a tile an *H-tile* if it is designated by its integer width and a
*V-tile* if it is designated by its integer height. Splitting each tile along its designated side
normalizes the tiling: every H-tile then has width exactly `1` and every V-tile height exactly `1`
(`Normalized`, `exists_normalized`). Robinson's induction runs on the number of H-tiles of a
normalized tiling. If there are none, every tile has integer height and so does `R`. Otherwise
pick an H-tile and grow a vertical strip of width `1` from it, upwards and downwards: the strip
runs straight up through V-tiles until an H-tile blocks it, at which point it steps sideways onto
that H-tile and continues. Deleting the strip and sliding what is to its right one unit leftwards
tiles a rectangle one unit narrower with fewer H-tiles, and the induction applies to it.
-/

@[expose] public section

namespace IntegerRectangle.Staircase

variable {ι : Type} [Fintype ι] {R S : Rectangle} {T : ι → Rectangle} {H : ι → Prop}

/-! ### Normalized tilings -/

/-- A tiling is *normalized*, with `H` designating its H-tiles, when it is proper, every H-tile
has width exactly `1`, and every other tile — every V-tile — has height exactly `1`. -/
structure Normalized (R : Rectangle) (T : ι → Rectangle) (H : ι → Prop) : Prop where
  /-- The tiles tile `R`. -/
  tiling : IsTiling R T
  /-- No tile is degenerate. -/
  proper : Proper T
  /-- H-tiles are one unit wide. -/
  width_one : ∀ i, H i → (T i).width = 1
  /-- V-tiles are one unit tall. -/
  height_one : ∀ i, ¬ H i → (T i).height = 1

/-- A tiled rectangle is nondegenerate vertically, since its tiles are. -/
lemma Normalized.pos_height (hn : Normalized R T H) : R.y₀ < R.y₁ :=
  have ⟨i⟩ := hn.tiling.nonempty_index
  lt_of_le_of_lt (hn.tiling.le_tile_y₀ i) ((hn.proper i).2.trans_le (hn.tiling.tile_y₁_le i))

/-- A tile is cut along its width when that is an integer, and along its height otherwise. -/
def CutsWidth (S : Rectangle) : Prop := ∃ m : ℤ, S.width = m

open scoped Classical in
/-- The number of unit pieces a tile is cut into: its width if that is an integer, and its height
otherwise. -/
noncomputable def pieceCount (S : Rectangle) : ℕ :=
  if CutsWidth S then ⌊S.width⌋₊ else ⌊S.height⌋₊

open scoped Classical in
/-- The `j`-th unit piece of a tile, counted from its lower left corner along the side it is cut
along. -/
noncomputable def piece (S : Rectangle) (j : ℕ) : Rectangle :=
  if CutsWidth S then
    { x₀ := S.x₀ + j, x₁ := S.x₀ + j + 1, y₀ := S.y₀, y₁ := S.y₁, hx := by linarith, hy := S.hy }
  else
    { x₀ := S.x₀, x₁ := S.x₁, y₀ := S.y₀ + j, y₁ := S.y₀ + j + 1, hx := S.hx, hy := by linarith }

/-- An interval whose length is a whole number is exhausted by that many unit steps. -/
private lemma add_floor_sub {a b : ℝ} (hab : a < b) (h : ∃ m : ℤ, b - a = m) :
    a + ⌊b - a⌋₊ = b := by
  obtain ⟨m, hm⟩ := h
  have hm0 : (0 : ℤ) ≤ m := by exact_mod_cast hm ▸ sub_nonneg.mpr hab.le
  have hcast : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hm0
  rw [hm, ← hcast, Nat.floor_natCast, hcast]
  linarith

/-- The pieces of a tile cut along its width exhaust that width. -/
lemma add_pieceCount_width (h : CutsWidth S) (hx : S.x₀ < S.x₁) :
    S.x₀ + pieceCount S = S.x₁ := by
  classical
  rw [pieceCount, if_pos h]
  exact add_floor_sub hx h

/-- The pieces of a tile cut along its height exhaust that height. -/
lemma add_pieceCount_height (hS : S.HasIntegerSide) (h : ¬ CutsWidth S) (hy : S.y₀ < S.y₁) :
    S.y₀ + pieceCount S = S.y₁ := by
  classical
  rw [pieceCount, if_neg h]
  exact add_floor_sub hy (hS.resolve_left h)

lemma piece_width_of_cutsWidth (h : CutsWidth S) (j : ℕ) : (piece S j).width = 1 := by
  simp only [piece, if_pos h, Rectangle.width]
  ring

lemma piece_height_of_not_cutsWidth (h : ¬ CutsWidth S) (j : ℕ) : (piece S j).height = 1 := by
  simp only [piece, if_neg h, Rectangle.height]
  ring

/-- Each piece is proper: it is one unit long along the side it is cut from, and keeps the other
side of the tile it comes from. -/
lemma piece_proper (hx : S.x₀ < S.x₁) (hy : S.y₀ < S.y₁) (j : ℕ) :
    (piece S j).x₀ < (piece S j).x₁ ∧ (piece S j).y₀ < (piece S j).y₁ := by
  classical
  rw [piece]
  split_ifs
  · exact ⟨by simp, hy⟩
  · exact ⟨hx, by simp⟩

/-- A piece with a legitimate index sits inside the tile it comes from. -/
lemma piece_le (hS : S.HasIntegerSide) (hx : S.x₀ < S.x₁) (hy : S.y₀ < S.y₁) {j : ℕ}
    (hj : j < pieceCount S) :
    S.x₀ ≤ (piece S j).x₀ ∧ (piece S j).x₁ ≤ S.x₁ ∧ S.y₀ ≤ (piece S j).y₀ ∧
      (piece S j).y₁ ≤ S.y₁ := by
  classical
  have hj' : (j : ℝ) + 1 ≤ pieceCount S := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  rw [piece]
  split_ifs with h
  · have := add_pieceCount_width h hx
    exact ⟨by simp [hj0], by simp; linarith, le_rfl, le_rfl⟩
  · have := add_pieceCount_height hS h hy
    exact ⟨le_rfl, le_rfl, by simp [hj0], by simp; linarith⟩

lemma piece_subset (hS : S.HasIntegerSide) (hx : S.x₀ < S.x₁) (hy : S.y₀ < S.y₁) {j : ℕ}
    (hj : j < pieceCount S) : (piece S j).toSet ⊆ S.toSet := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := piece_le hS hx hy hj
  rintro ⟨a, b⟩ ⟨⟨k₁, k₂⟩, k₃, k₄⟩
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

lemma piece_subset_toSetIoc (hS : S.HasIntegerSide) (hx : S.x₀ < S.x₁) (hy : S.y₀ < S.y₁) {j : ℕ}
    (hj : j < pieceCount S) : (piece S j).toSetIoc ⊆ S.toSetIoc := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := piece_le hS hx hy hj
  rintro ⟨a, b⟩ ⟨⟨k₁, k₂⟩, k₃, k₄⟩
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- The index of the piece containing a point: the ceiling of its distance from the cut side. -/
private lemma exists_index {a b t : ℝ} (hat : a < t) (htb : t ≤ b) {n : ℕ} (hn : a + n = b) :
    ∃ j : ℕ, j < n ∧ a + j < t ∧ t ≤ a + j + 1 := by
  have h1 : 1 ≤ ⌈t - a⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hcast : ((⌈t - a⌉₊ - 1 : ℕ) : ℝ) = (⌈t - a⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_one]
  refine ⟨⌈t - a⌉₊ - 1, ?_, ?_, ?_⟩
  · have : ⌈t - a⌉₊ ≤ n := Nat.ceil_le.mpr (by linarith)
    lia
  · rw [hcast]
    linarith [Nat.ceil_lt_add_one (show (0 : ℝ) ≤ t - a by linarith)]
  · rw [hcast]
    linarith [Nat.le_ceil (t - a)]

/-- Every point of a tile lies in the half-open cell of one of its pieces. -/
lemma exists_mem_piece (hS : S.HasIntegerSide) (hx : S.x₀ < S.x₁) (hy : S.y₀ < S.y₁) {x y : ℝ}
    (hz : ((x, y) : ℝ × ℝ) ∈ S.toSetIoc) :
    ∃ j : ℕ, j < pieceCount S ∧ ((x, y) : ℝ × ℝ) ∈ (piece S j).toSetIoc := by
  classical
  obtain ⟨⟨h₁, h₂⟩, h₃, h₄⟩ := hz
  by_cases h : CutsWidth S
  · obtain ⟨j, hj, hj₁, hj₂⟩ := exists_index h₁ h₂ (add_pieceCount_width h hx)
    exact ⟨j, hj, ⟨by rw [piece, if_pos h]; exact hj₁, by rw [piece, if_pos h]; exact hj₂⟩,
      by rw [piece, if_pos h]; exact h₃, by rw [piece, if_pos h]; exact h₄⟩
  · obtain ⟨j, hj, hj₁, hj₂⟩ := exists_index h₃ h₄ (add_pieceCount_height hS h hy)
    exact ⟨j, hj, ⟨by rw [piece, if_neg h]; exact h₁, by rw [piece, if_neg h]; exact h₂⟩,
      by rw [piece, if_neg h]; exact hj₁, by rw [piece, if_neg h]; exact hj₂⟩

/-- Distinct pieces of a tile have disjoint half-open cells. -/
lemma piece_disjoint {j j' : ℕ} (hjj : j ≠ j') :
    Disjoint (piece S j).toSetIoc (piece S j').toSetIoc := by
  classical
  rw [Set.disjoint_left]
  rintro ⟨x, y⟩ hj hj'
  have hne : ∀ {a b : ℕ}, a < b → (a : ℝ) + 1 ≤ b := fun h ↦ by exact_mod_cast h
  rw [piece] at hj hj'
  split_ifs at hj hj' with h <;> simp only [Rectangle.mem_toSetIoc] at hj hj' <;>
    rcases lt_or_gt_of_ne hjj with hlt | hlt
  · linarith [hj.1.2, hj'.1.1, hne hlt]
  · linarith [hj'.1.2, hj.1.1, hne hlt]
  · linarith [hj.2.2, hj'.2.1, hne hlt]
  · linarith [hj'.2.2, hj.2.1, hne hlt]

/-- **Every tiling by tiles with an integer side refines to a normalized one**, by cutting each
tile into unit pieces along its integer side. -/
theorem exists_normalized (hT : IsTiling R T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁)
    (hsides : ∀ i, (T i).HasIntegerSide) :
    ∃ (ι' : Type) (_ : Fintype ι') (T' : ι' → Rectangle) (H' : ι' → Prop), Normalized R T' H' := by
  classical
  set ι₁ := {i : ι // (T i).x₀ < (T i).x₁ ∧ (T i).y₀ < (T i).y₁} with hι₁
  have hT₁ : IsTiling R fun i : ι₁ ↦ T i.1 := isTiling_proper hT hx hy
  have hs : ∀ i : ι₁, (T i.1).HasIntegerSide := fun i ↦ hsides i.1
  refine ⟨Σ i : ι₁, Fin (pieceCount (T i.1)), inferInstance, fun p ↦ piece (T p.1.1) p.2,
    fun p ↦ CutsWidth (T p.1.1), ?_, ?_, ?_, ?_⟩
  · refine isTiling_of_toSetIoc hx hy
      (fun p ↦ (piece_subset (hs p.1) p.1.2.1 p.1.2.2 p.2.2).trans (hT₁.tile_subset p.1))
      (fun p q hpq ↦ ?_) fun z hz ↦ ?_
    · obtain ⟨p₁, p₂⟩ := p
      obtain ⟨q₁, q₂⟩ := q
      rw [Function.onFun]
      rcases eq_or_ne p₁ q₁ with heq | hne
      · subst heq
        exact piece_disjoint fun hcon ↦ hpq (congrArg _ (Fin.val_injective hcon))
      · exact (hT₁.pairwiseDisjoint_toSetIoc hne).mono
          (piece_subset_toSetIoc (hs p₁) p₁.2.1 p₁.2.2 p₂.2)
          (piece_subset_toSetIoc (hs q₁) q₁.2.1 q₁.2.2 q₂.2)
    · obtain ⟨x, y⟩ := z
      obtain ⟨i, hi, -⟩ := hT₁.existsUnique_toSetIoc hz
      obtain ⟨j, hj, hmem⟩ := exists_mem_piece (hs i) i.2.1 i.2.2 hi
      exact Set.mem_iUnion.mpr ⟨⟨i, ⟨j, hj⟩⟩, hmem⟩
  · exact fun p ↦ piece_proper p.1.2.1 p.1.2.2 p.2
  · exact fun p hp ↦ piece_width_of_cutsWidth hp p.2
  · exact fun p hp ↦ piece_height_of_not_cutsWidth hp p.2

/-! ### Cutting a tiling along a staircase strip -/

/-- The part of a tile to the left of the strip of width `1` with left edge at `c`. It is
degenerate exactly when the tile does not reach past `c`. -/
def cutLeft (S : Rectangle) (c : ℝ) : Rectangle where
  x₀ := min S.x₀ c
  x₁ := min S.x₁ c
  y₀ := S.y₀
  y₁ := S.y₁
  hx := min_le_min S.hx le_rfl
  hy := S.hy

/-- The part of a tile to the right of the strip of width `1` with left edge at `c`, slid one unit
leftwards. It is degenerate exactly when the tile does not reach past `c + 1`. -/
def cutRight (S : Rectangle) (c : ℝ) : Rectangle where
  x₀ := max S.x₀ (c + 1) - 1
  x₁ := max S.x₁ (c + 1) - 1
  y₀ := S.y₀
  y₁ := S.y₁
  hx := by have := max_le_max S.hx (le_refl (c + 1)); linarith
  hy := S.hy

/-- The two pieces a tile is cut into by the strip of width `1` with left edge at `c`. A tile
lying inside the strip is cut into two degenerate pieces, and so disappears. -/
def cutPiece (S : Rectangle) (c : ℝ) : Bool → Rectangle
  | false => cutLeft S c
  | true => cutRight S c

@[simp] lemma cutPiece_y₀ (S : Rectangle) (c : ℝ) (b : Bool) : (cutPiece S c b).y₀ = S.y₀ := by
  cases b <;> rfl

@[simp] lemma cutPiece_y₁ (S : Rectangle) (c : ℝ) (b : Bool) : (cutPiece S c b).y₁ = S.y₁ := by
  cases b <;> rfl

/-- The rectangle left over when a strip of width `1` is cut out of `R`. -/
def cutRect (R : Rectangle) (h : R.x₀ + 1 ≤ R.x₁) : Rectangle where
  x₀ := R.x₀
  x₁ := R.x₁ - 1
  y₀ := R.y₀
  y₁ := R.y₁
  hx := by linarith
  hy := R.hy

lemma mem_cutLeft {S : Rectangle} {c x y : ℝ} (h : ((x, y) : ℝ × ℝ) ∈ (cutLeft S c).toSetIoc) :
    ((x, y) : ℝ × ℝ) ∈ S.toSetIoc ∧ x ≤ c := by
  simp only [Rectangle.mem_toSetIoc', cutLeft] at h ⊢
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h
  refine ⟨⟨⟨?_, h₂.trans (min_le_left _ _)⟩, h₃⟩, h₂.trans (min_le_right _ _)⟩
  rcases min_cases S.x₀ c with ⟨heq, -⟩ | ⟨heq, -⟩ <;> rw [heq] at h₁ <;>
    linarith [h₂.trans (min_le_right S.x₁ c)]

lemma mem_cutRight {S : Rectangle} {c x y : ℝ} (h : ((x, y) : ℝ × ℝ) ∈ (cutRight S c).toSetIoc) :
    ((x + 1, y) : ℝ × ℝ) ∈ S.toSetIoc ∧ c < x := by
  simp only [Rectangle.mem_toSetIoc', cutRight] at h ⊢
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h
  have hc : c < x := by linarith [le_max_right S.x₀ (c + 1)]
  refine ⟨⟨⟨by linarith [le_max_left S.x₀ (c + 1)], ?_⟩, h₃⟩, hc⟩
  rcases max_cases S.x₁ (c + 1) with ⟨heq, -⟩ | ⟨heq, -⟩ <;> rw [heq] at h₂ <;> linarith

lemma mem_cutLeft' {S : Rectangle} {c x y : ℝ} (h : ((x, y) : ℝ × ℝ) ∈ S.toSetIoc) (hc : x ≤ c) :
    ((x, y) : ℝ × ℝ) ∈ (cutLeft S c).toSetIoc := by
  simp only [Rectangle.mem_toSetIoc', cutLeft] at h ⊢
  exact ⟨⟨lt_of_le_of_lt (min_le_left _ _) h.1.1, le_min h.1.2 hc⟩, h.2⟩

lemma mem_cutRight' {S : Rectangle} {c x y : ℝ} (h : ((x + 1, y) : ℝ × ℝ) ∈ S.toSetIoc)
    (hc : c < x) : ((x, y) : ℝ × ℝ) ∈ (cutRight S c).toSetIoc := by
  simp only [Rectangle.mem_toSetIoc', cutRight] at h ⊢
  refine ⟨⟨?_, by linarith [le_max_left S.x₁ (c + 1), h.1.2]⟩, h.2⟩
  rcases max_cases S.x₀ (c + 1) with ⟨heq, -⟩ | ⟨heq, -⟩ <;> rw [heq] <;> linarith [h.1.1]

/-- A *staircase strip* for a tiling: `c y` is the left edge of a strip of width `1` at height
`y`, defined for the heights in `(a, b]`. Each tile of the tiling lies to the left of the strip at
each of its heights, or to its right, or inside it; a tile inside the strip meets no other column
of the staircase, and if it is an H-tile it fills the strip exactly. No tile lies to the left of
the strip at one of its heights and to the right of it at another: the staircase is a wall. -/
structure Strip (R : Rectangle) (T : ι → Rectangle) (H : ι → Prop) (a b : ℝ) (c : ℝ → ℝ) :
    Prop where
  /-- The strip stays inside `R`. -/
  mem : ∀ y, a < y → y ≤ b → R.x₀ ≤ c y ∧ c y + 1 ≤ R.x₁
  /-- At each of its heights a tile is left of, right of, or inside the strip. -/
  side : ∀ (j : ι) (y : ℝ), a < y → y ≤ b → (T j).y₀ < y → y ≤ (T j).y₁ →
      (T j).x₁ ≤ c y ∨ c y + 1 ≤ (T j).x₀ ∨
        (a ≤ (T j).y₀ ∧ (T j).y₁ ≤ b ∧ (∀ t, (T j).y₀ < t → t ≤ (T j).y₁ → c t = c y) ∧
          (H j → (T j).x₀ = c y ∧ (T j).x₁ = c y + 1))
  /-- No tile is left of the strip at one height and right of it at another. -/
  consistent : ∀ (j : ι) (y y' : ℝ), a < y → y ≤ b → a < y' → y' ≤ b → (T j).y₀ < y →
      y ≤ (T j).y₁ → (T j).y₀ < y' → y' ≤ (T j).y₁ → (T j).x₁ ≤ c y → c y' + 1 ≤ (T j).x₀ → False

open scoped Classical in
/-- The abscissa at which the strip cuts a tile: its right edge if the tile is left of the strip,
its left edge less one if it is right of the strip, and the left edge of the strip if the tile
lies inside it. -/
noncomputable def cutAt (T : ι → Rectangle) (c : ℝ → ℝ) (j : ι) : ℝ :=
  if (T j).x₁ ≤ c (T j).y₁ then (T j).x₁
  else if c (T j).y₁ + 1 ≤ (T j).x₀ then (T j).x₀ - 1 else c (T j).y₁

variable {c : ℝ → ℝ}

/-- **A tile is cut at the same abscissa at every one of its heights.** The three cases are the
three alternatives of `Strip.side`, and it is consistency of the strip that keeps a tile in the
same case throughout. -/
lemma cutAt_spec (hn : Normalized R T H) (hs : Strip R T H R.y₀ R.y₁ c) (j : ι) {y : ℝ}
    (h₀ : (T j).y₀ < y) (h₁ : y ≤ (T j).y₁) :
    (cutAt T c j = (T j).x₁ ∧ (T j).x₁ ≤ c y) ∨
      (cutAt T c j = (T j).x₀ - 1 ∧ c y + 1 ≤ (T j).x₀) ∨
      (cutAt T c j = c y ∧ (H j → (T j).x₀ = c y ∧ (T j).x₁ = c y + 1)) := by
  classical
  have hjy : (T j).y₀ < (T j).y₁ := (hn.proper j).2
  have hY₀ : R.y₀ < (T j).y₁ := lt_of_le_of_lt (hn.tiling.le_tile_y₀ j) hjy
  have hY₁ : (T j).y₁ ≤ R.y₁ := hn.tiling.tile_y₁_le j
  have hy₀ : R.y₀ < y := lt_of_le_of_lt (hn.tiling.le_tile_y₀ j) h₀
  have hy₁ : y ≤ R.y₁ := h₁.trans hY₁
  -- the strip has the same abscissa at `y` as at the top edge of the tile in the third case
  have hside := hs.side j y hy₀ hy₁ h₀ h₁
  by_cases hL : (T j).x₁ ≤ c (T j).y₁
  · refine Or.inl ⟨by rw [cutAt, if_pos hL], ?_⟩
    rcases hside with h | h | ⟨-, -, hconst, -⟩
    · exact h
    · exact (hs.consistent j (T j).y₁ y hY₀ hY₁ hy₀ hy₁ hjy le_rfl h₀ h₁ hL h).elim
    · rw [hconst (T j).y₁ hjy le_rfl] at hL
      exact hL
  by_cases hR : c (T j).y₁ + 1 ≤ (T j).x₀
  · refine Or.inr (Or.inl ⟨by rw [cutAt, if_neg hL, if_pos hR], ?_⟩)
    rcases hside with h | h | ⟨-, -, hconst, -⟩
    · exact (hs.consistent j y (T j).y₁ hy₀ hy₁ hY₀ hY₁ h₀ h₁ hjy le_rfl h hR).elim
    · exact h
    · rw [hconst (T j).y₁ hjy le_rfl] at hR
      exact hR
  · -- the tile meets the strip at its top edge, so it lies inside it and follows it
    refine Or.inr (Or.inr ?_)
    rw [cutAt, if_neg hL, if_neg hR]
    rcases hs.side j (T j).y₁ hY₀ hY₁ hjy le_rfl with h | h | ⟨-, -, hconst, halign⟩
    · exact absurd h hL
    · exact absurd h hR
    · refine ⟨(hconst y h₀ h₁).symm, fun hj ↦ ?_⟩
      rw [hconst y h₀ h₁]
      exact halign hj

/-- The cut abscissa of a tile stays inside the horizontal extent of the shrunken rectangle. -/
lemma cutAt_mem (hn : Normalized R T H) (hs : Strip R T H R.y₀ R.y₁ c) (j : ι) :
    R.x₀ ≤ cutAt T c j ∧ cutAt T c j ≤ R.x₁ - 1 := by
  have hjy : (T j).y₀ < (T j).y₁ := (hn.proper j).2
  have hy₀ : R.y₀ < (T j).y₁ := lt_of_le_of_lt (hn.tiling.le_tile_y₀ j) hjy
  have hy₁ : (T j).y₁ ≤ R.y₁ := hn.tiling.tile_y₁_le j
  obtain ⟨hm₀, hm₁⟩ := hs.mem (T j).y₁ hy₀ hy₁
  have hx₀ := hn.tiling.le_tile_x₀ j
  have hx₁ := hn.tiling.tile_x₁_le j
  rcases cutAt_spec hn hs j hjy le_rfl with ⟨he, hle⟩ | ⟨he, hle⟩ | ⟨he, -⟩ <;> rw [he] <;>
    constructor <;> linarith [(hn.proper j).1]

/-- The left piece of a tile lies in the tile, to the left of the strip. -/
lemma mem_cut_left (hn : Normalized R T H) (hs : Strip R T H R.y₀ R.y₁ c) {j : ι} {u v : ℝ}
    (h : ((u, v) : ℝ × ℝ) ∈ (cutPiece (T j) (cutAt T c j) false).toSetIoc) :
    ((u, v) : ℝ × ℝ) ∈ (T j).toSetIoc ∧ u ≤ c v := by
  obtain ⟨hmem, hle⟩ := mem_cutLeft h
  refine ⟨hmem, ?_⟩
  rcases cutAt_spec hn hs j hmem.2.1 hmem.2.2 with ⟨he, hx⟩ | ⟨he, hx⟩ | ⟨he, -⟩ <;> rw [he] at hle
  · linarith
  · linarith [hmem.1.1]
  · linarith

/-- The right piece of a tile lies, once slid back, in the tile, to the right of the strip. -/
lemma mem_cut_right (hn : Normalized R T H) (hs : Strip R T H R.y₀ R.y₁ c) {j : ι} {u v : ℝ}
    (h : ((u, v) : ℝ × ℝ) ∈ (cutPiece (T j) (cutAt T c j) true).toSetIoc) :
    ((u + 1, v) : ℝ × ℝ) ∈ (T j).toSetIoc ∧ c v < u := by
  obtain ⟨hmem, hlt⟩ := mem_cutRight h
  refine ⟨hmem, ?_⟩
  rcases cutAt_spec hn hs j hmem.2.1 hmem.2.2 with ⟨he, hx⟩ | ⟨he, hx⟩ | ⟨he, -⟩ <;> rw [he] at hlt
  · linarith [hmem.1.2]
  · linarith
  · linarith

/-- A point of a tile to the left of the strip lies in the left piece of the tile. -/
lemma mem_cut_left' (hn : Normalized R T H) (hs : Strip R T H R.y₀ R.y₁ c) {j : ι} {u v : ℝ}
    (h : ((u, v) : ℝ × ℝ) ∈ (T j).toSetIoc) (hc : u ≤ c v) :
    ((u, v) : ℝ × ℝ) ∈ (cutPiece (T j) (cutAt T c j) false).toSetIoc := by
  refine mem_cutLeft' h ?_
  rcases cutAt_spec hn hs j h.2.1 h.2.2 with ⟨he, hx⟩ | ⟨he, hx⟩ | ⟨he, -⟩ <;> rw [he]
  · linarith [h.1.2]
  · linarith [h.1.1]
  · linarith

/-- A point whose translate lies in a tile to the right of the strip lies in the right piece of
that tile. -/
lemma mem_cut_right' (hn : Normalized R T H) (hs : Strip R T H R.y₀ R.y₁ c) {j : ι} {u v : ℝ}
    (h : ((u + 1, v) : ℝ × ℝ) ∈ (T j).toSetIoc) (hc : c v < u) :
    ((u, v) : ℝ × ℝ) ∈ (cutPiece (T j) (cutAt T c j) true).toSetIoc := by
  refine mem_cutRight' h ?_
  rcases cutAt_spec hn hs j h.2.1 h.2.2 with ⟨he, hx⟩ | ⟨he, hx⟩ | ⟨he, -⟩ <;> rw [he]
  · linarith
  · linarith [h.1.1]
  · linarith

/-- **Cutting a tiling along a staircase strip tiles the rectangle one unit narrower.** The strip
of width `1` that is deleted is exactly the gap that closes when everything to its right slides
one unit leftwards, so the half-open cells still partition the shrunken rectangle. -/
theorem isTiling_cut (hn : Normalized R T H) (hs : Strip R T H R.y₀ R.y₁ c)
    (hRx : R.x₀ + 1 < R.x₁) :
    IsTiling (cutRect R hRx.le) fun p : ι × Bool ↦ cutPiece (T p.1) (cutAt T c p.1) p.2 := by
  have hRy := hn.pos_height
  refine isTiling_of_toSetIoc (by simp only [cutRect]; linarith) (by simpa only [cutRect] using hRy)
    (fun p ↦ ?_) (fun p q hpq ↦ ?_) fun z hz ↦ ?_
  · obtain ⟨j, b⟩ := p
    obtain ⟨hκ₀, hκ₁⟩ := cutAt_mem hn hs j
    have hx₀ := hn.tiling.le_tile_x₀ j
    have hx₁ := hn.tiling.tile_x₁_le j
    have hy₀ := hn.tiling.le_tile_y₀ j
    have hy₁ := hn.tiling.tile_y₁_le j
    rintro ⟨u, v⟩ ⟨⟨k₁, k₂⟩, k₃, k₄⟩
    cases b <;> simp only [cutPiece, cutLeft, cutRight, cutRect] at k₁ k₂ k₃ k₄ ⊢
    · exact ⟨⟨(le_min hx₀ hκ₀).trans k₁, k₂.trans ((min_le_right _ _).trans hκ₁)⟩,
        hy₀.trans k₃, k₄.trans hy₁⟩
    · refine ⟨⟨by linarith [le_max_right (T j).x₀ (cutAt T c j + 1)], ?_⟩, hy₀.trans k₃,
        k₄.trans hy₁⟩
      linarith [max_le hx₁ (show cutAt T c j + 1 ≤ R.x₁ by linarith)]
  · obtain ⟨j, b⟩ := p
    obtain ⟨j', b'⟩ := q
    rw [Function.onFun, Set.disjoint_left]
    rintro ⟨u, v⟩ hmem hmem'
    cases b <;> cases b'
    · obtain ⟨h, -⟩ := mem_cut_left hn hs hmem
      obtain ⟨h', -⟩ := mem_cut_left hn hs hmem'
      exact hpq (Prod.ext (hn.tiling.eq_of_mem_cell (sx := true) (sy := true) h h') rfl)
    · obtain ⟨-, h⟩ := mem_cut_left hn hs hmem
      obtain ⟨-, h'⟩ := mem_cut_right hn hs hmem'
      linarith
    · obtain ⟨-, h⟩ := mem_cut_right hn hs hmem
      obtain ⟨-, h'⟩ := mem_cut_left hn hs hmem'
      linarith
    · obtain ⟨h, -⟩ := mem_cut_right hn hs hmem
      obtain ⟨h', -⟩ := mem_cut_right hn hs hmem'
      exact hpq (Prod.ext (hn.tiling.eq_of_mem_cell (sx := true) (sy := true) h h') rfl)
  · obtain ⟨u, v⟩ := z
    obtain ⟨⟨hu₀, hu₁⟩, hv₀, hv₁⟩ := hz
    simp only [cutRect] at hu₀ hu₁ hv₀ hv₁
    by_cases hc : u ≤ c v
    · obtain ⟨j, hj, -⟩ := hn.tiling.existsUnique_toSetIoc
        (show ((u, v) : ℝ × ℝ) ∈ R.toSetIoc from ⟨⟨hu₀, by linarith⟩, hv₀, hv₁⟩)
      exact Set.mem_iUnion.mpr ⟨(j, false), mem_cut_left' hn hs hj hc⟩
    · push Not at hc
      obtain ⟨j, hj, -⟩ := hn.tiling.existsUnique_toSetIoc
        (show ((u + 1, v) : ℝ × ℝ) ∈ R.toSetIoc from ⟨⟨by linarith, by linarith⟩, hv₀, hv₁⟩)
      exact Set.mem_iUnion.mpr ⟨(j, true), mem_cut_right' hn hs hj hc⟩

/-! ### One step of the induction -/

/-- **An H-tile survives the cut in one piece, or not at all.** It is one unit wide, so the strip
either misses it, and it is carried over whole in one of the two pieces, or the strip covers it
exactly and both pieces are empty. -/
lemma width_cutPiece_of_H (hn : Normalized R T H) (hs : Strip R T H R.y₀ R.y₁ c) {j : ι}
    (hj : H j) :
    ((cutPiece (T j) (cutAt T c j) false).width = 1 ∧
        (cutPiece (T j) (cutAt T c j) true).width = 0) ∨
      ((cutPiece (T j) (cutAt T c j) false).width = 0 ∧
        (cutPiece (T j) (cutAt T c j) true).width = 1) ∨
      ((cutPiece (T j) (cutAt T c j) false).width = 0 ∧
        (cutPiece (T j) (cutAt T c j) true).width = 0) := by
  have hw : (T j).x₁ = (T j).x₀ + 1 := by
    have := hn.width_one j hj
    simp only [Rectangle.width] at this
    linarith
  rcases cutAt_spec hn hs j (hn.proper j).2 le_rfl with ⟨he, -⟩ | ⟨he, -⟩ | ⟨he, halign⟩
  · exact Or.inl (by constructor <;>
      simp only [cutPiece, cutLeft, cutRight, Rectangle.width, he, min_def, max_def] <;>
      split_ifs <;> linarith)
  · exact Or.inr (Or.inl (by constructor <;>
      simp only [cutPiece, cutLeft, cutRight, Rectangle.width, he, min_def, max_def] <;>
      split_ifs <;> linarith))
  · obtain ⟨h₀, h₁⟩ := halign hj
    exact Or.inr (Or.inr (by constructor <;>
      simp only [cutPiece, cutLeft, cutRight, Rectangle.width, he, h₀, h₁, min_def, max_def] <;>
      split_ifs <;> linarith))

/-- A tile that fills the strip at its own height leaves nothing behind. -/
lemma width_cutPiece_of_mem_strip (hn : Normalized R T H) {k : ι} (hk : H k)
    (hkc : (T k).x₀ = c (T k).y₁) (b : Bool) : (cutPiece (T k) (cutAt T c k) b).width = 0 := by
  classical
  have hw : (T k).x₁ = (T k).x₀ + 1 := by
    have := hn.width_one k hk
    simp only [Rectangle.width] at this
    linarith
  have he : cutAt T c k = c (T k).y₁ := by
    rw [cutAt, if_neg (by rw [hw, hkc]; linarith), if_neg (by rw [hkc]; linarith)]
  cases b <;>
    simp only [cutPiece, cutLeft, cutRight, Rectangle.width, he, ← hkc, hw, min_def, max_def] <;>
    split_ifs <;> linarith

/-- A piece is nondegenerate exactly when it has positive width. -/
private lemma width_ne_zero_iff {S : Rectangle} : S.x₀ < S.x₁ ↔ S.width ≠ 0 := by
  simp only [Rectangle.width, sub_ne_zero]
  exact ⟨fun h ↦ h.ne', fun h ↦ lt_of_le_of_ne S.hx (Ne.symm h)⟩

/-- **One step of Robinson's induction.** Cutting a normalized tiling along a staircase strip
grown from an H-tile leaves a normalized tiling of a rectangle one unit narrower: heights never
change, so V-tiles stay V-tiles, and an H-tile is either carried over whole or swallowed by the
strip — and the H-tile the strip is grown from is swallowed. -/
theorem exists_normalized_cut (hn : Normalized R T H) (hs : Strip R T H R.y₀ R.y₁ c)
    (hRx : R.x₀ + 1 < R.x₁) {k : ι} (hk : H k) (hkc : (T k).x₀ = c (T k).y₁) :
    ∃ (ι' : Type) (_ : Fintype ι') (T' : ι' → Rectangle) (H' : ι' → Prop),
      Normalized (cutRect R hRx.le) T' H' ∧ Nat.card {p // H' p} < Nat.card {i // H i} := by
  classical
  have hcut : IsTiling (cutRect R hRx.le) fun p : ι × Bool ↦ cutPiece (T p.1) (cutAt T c p.1) p.2 :=
    isTiling_cut hn hs hRx
  refine ⟨{p : ι × Bool // (cutPiece (T p.1) (cutAt T c p.1) p.2).x₀ <
      (cutPiece (T p.1) (cutAt T c p.1) p.2).x₁ ∧ (cutPiece (T p.1) (cutAt T c p.1) p.2).y₀ <
      (cutPiece (T p.1) (cutAt T c p.1) p.2).y₁}, inferInstance,
    fun p ↦ cutPiece (T p.1.1) (cutAt T c p.1.1) p.1.2, fun p ↦ H p.1.1,
    ⟨isTiling_proper hcut (by simp only [cutRect]; linarith) hn.pos_height, fun p ↦ p.2, ?_, ?_⟩,
    ?_⟩
  · rintro ⟨⟨j, b⟩, hprop⟩ hj
    have hne := width_ne_zero_iff.mp hprop.1
    rcases width_cutPiece_of_H hn hs hj with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ <;> cases b <;>
      first
        | exact h₀
        | exact h₁
        | exact absurd h₀ hne
        | exact absurd h₁ hne
  · rintro ⟨⟨j, b⟩, hprop⟩ hj
    simpa only [Rectangle.height, cutPiece_y₀, cutPiece_y₁] using hn.height_one j hj
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    refine Fintype.card_lt_of_injective_of_notMem
      (fun p ↦ (⟨p.1.1.1, p.2⟩ : {i // H i})) (fun p q hpq ↦ ?_) (b := ⟨k, hk⟩) ?_
    · obtain ⟨⟨⟨j, b⟩, hprop⟩, hH⟩ := p
      obtain ⟨⟨⟨j', b'⟩, hprop'⟩, hH'⟩ := q
      have hjj : j = j' := congrArg Subtype.val hpq
      subst hjj
      have hne := width_ne_zero_iff.mp hprop.1
      have hne' := width_ne_zero_iff.mp hprop'.1
      have hbb : b = b' := by
        rcases width_cutPiece_of_H hn hs hH with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ <;>
          cases b <;> cases b' <;>
          first
            | rfl
            | exact absurd h₀ hne
            | exact absurd h₁ hne
            | exact absurd h₀ hne'
            | exact absurd h₁ hne'
      subst hbb
      rfl
    · rintro ⟨⟨⟨⟨j, b⟩, hprop⟩, hH⟩, hmem⟩
      have hjk : j = k := congrArg Subtype.val hmem
      subst hjk
      exact absurd (width_cutPiece_of_mem_strip hn hH hkc b) (width_ne_zero_iff.mp hprop.1)

end IntegerRectangle.Staircase
