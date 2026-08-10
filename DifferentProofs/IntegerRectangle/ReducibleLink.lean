module

public import DifferentProofs.IntegerRectangle.Cells

/-!
# The integer-rectangle theorem by induction on reducible links

Wagon's tenth proof, the variation on Robinson's induction due to Richard Bishop and Wagon. Call a
tile an *H-tile* if it is designated by its integer width and a *V-tile* if it is designated by
its integer height. A *V-link* is a maximal vertical segment of the tiling whose interior is
crossed by no horizontal segment, and an *H-link* is its horizontal counterpart. A link is
*reducible* if it is a V-link with only H-tiles along one of its sides, or an H-link with only
V-tiles along one of its sides. Given a reducible V-link with only H-tiles on its right, let `w`
be the width of the narrowest of them and push the tiles on its left `w` units rightwards: heights
never change, so V-tiles stay V-tiles, and widths change by the integer `w`, so H-tiles stay
H-tiles — while the narrowest tile on the right is squeezed away and the tiling loses a tile.
Induction on the number of tiles then reduces everything to the claim that a reducible link always
exists, and if none did there would be a chain of H-tiles running from the bottom of `R` to its
top and a chain of V-tiles running from its left to its right, and those two chains would have to
cross.
-/

@[expose] public section

open Set

namespace IntegerRectangle.ReducibleLink

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-- A family of rectangles is *proper* when each of its members has positive width and positive
height. Degenerate tiles are harmless but carry no information, and every tiling can be pruned
down to a proper one (`exists_proper`). -/
def Proper (T : ι → Rectangle) : Prop := ∀ i, (T i).x₀ < (T i).x₁ ∧ (T i).y₀ < (T i).y₁

/-- The height `y` is *blocked* on the vertical line `x = c` when that line is not a free stretch
of the tiling there: either a tile crosses the line at height `y`, or a horizontal edge of the
tiling arrives at the line at height `y` from both sides. The unblocked heights are those
interior to a V-link. -/
def Blocked (T : ι → Rectangle) (c y : ℝ) : Prop :=
  (∃ i, (T i).x₀ < c ∧ c < (T i).x₁ ∧ (T i).y₀ ≤ y ∧ y ≤ (T i).y₁) ∨
    ((∃ i, (T i).x₀ < c ∧ c ≤ (T i).x₁ ∧ ((T i).y₀ = y ∨ (T i).y₁ = y)) ∧
      ∃ i, (T i).x₀ ≤ c ∧ c < (T i).x₁ ∧ ((T i).y₀ = y ∨ (T i).y₁ = y))

/-- A **V-link** of a tiling: a stretch `{c} × [lo, hi]` of a vertical line, interior to the tiled
rectangle in the horizontal direction, whose interior heights are unblocked and whose two ends are
blocked or on the boundary of `R`. Wagon's H-links are the V-links of the transposed tiling. -/
structure Link (R : Rectangle) (T : ι → Rectangle) where
  /-- The abscissa of the vertical line carrying the link. -/
  c : ℝ
  /-- The height of the lower end of the link. -/
  lo : ℝ
  /-- The height of the upper end of the link. -/
  hi : ℝ
  /-- The link is to the right of the left edge of `R`. -/
  x₀_lt : R.x₀ < c
  /-- The link is to the left of the right edge of `R`. -/
  lt_x₁ : c < R.x₁
  /-- The link is not a single point. -/
  lo_lt_hi : lo < hi
  /-- The link starts inside `R`. -/
  y₀_le : R.y₀ ≤ lo
  /-- The link ends inside `R`. -/
  le_y₁ : hi ≤ R.y₁
  /-- No interior height of the link is blocked. -/
  free : ∀ y, lo < y → y < hi → ¬ Blocked T c y
  /-- The link is maximal downwards. -/
  bot : lo = R.y₀ ∨ Blocked T c lo
  /-- The link is maximal upwards. -/
  top : hi = R.y₁ ∨ Blocked T c hi

/-- Two tiles whose lower-left cells contain a common point are equal — the form in which
uniqueness of the tile in a quadrant is used below. -/
private lemma eq_of_cell (hT : IsTiling R T) {c t : ℝ} {i j : ι}
    (hi : ((T i).x₀ < c ∧ c ≤ (T i).x₁) ∧ (T i).y₀ < t ∧ t ≤ (T i).y₁)
    (hj : ((T j).x₀ < c ∧ c ≤ (T j).x₁) ∧ (T j).y₀ < t ∧ t ≤ (T j).y₁) : i = j :=
  hT.eq_of_mem_cell (sx := true) (sy := true) (x := c) (y := t) hi hj

/-- A tile crossing the line of a link whose height range overlaps the link blocks an interior
height of the link, which is impossible. -/
private lemma Link.not_straddle (l : Link R T) {j : ι} (h₀ : (T j).x₀ < l.c) (h₁ : l.c < (T j).x₁)
    (h : max (T j).y₀ l.lo < min (T j).y₁ l.hi) : False := by
  have ha₁ : (T j).y₀ ≤ max (T j).y₀ l.lo := le_max_left _ _
  have ha₂ : l.lo ≤ max (T j).y₀ l.lo := le_max_right _ _
  have hb₁ : min (T j).y₁ l.hi ≤ (T j).y₁ := min_le_left _ _
  have hb₂ : min (T j).y₁ l.hi ≤ l.hi := min_le_right _ _
  exact l.free ((max (T j).y₀ l.lo + min (T j).y₁ l.hi) / 2) (by linarith) (by linarith)
    (Or.inl ⟨j, h₀, h₁, by linarith, by linarith⟩)

/-- **The tile abutting a V-link on the left at a given height.** At every height of the link
there is a tile whose right edge lies on the link, and it sticks out past neither end of the
link: those tiles cut the link into consecutive pieces. -/
theorem Link.exists_left (hT : IsTiling R T) (hp : Proper T) (l : Link R T) {y : ℝ}
    (hy₀ : l.lo < y) (hy₁ : y ≤ l.hi) :
    ∃ i, (T i).x₀ < l.c ∧ (T i).x₁ = l.c ∧ l.lo ≤ (T i).y₀ ∧ (T i).y₁ ≤ l.hi ∧
      (T i).y₀ < y ∧ y ≤ (T i).y₁ := by
  obtain ⟨i, ⟨⟨hx₀, hx₁⟩, hb, ht⟩, -⟩ := hT.existsUnique_cell' true true (x := l.c) (y := y)
    ⟨⟨l.x₀_lt, l.lt_x₁.le⟩, l.y₀_le.trans_lt hy₀, hy₁.trans l.le_y₁⟩
  have hmin : y ≤ min (T i).y₁ l.hi := le_min ht hy₁
  have hxeq : (T i).x₁ = l.c :=
    (hx₁.eq_or_lt.resolve_right fun h ↦
      l.not_straddle hx₀ h (max_lt (hb.trans_le hmin) (hy₀.trans_le hmin))).symm
  have hcelli : ∀ t : ℝ, (T i).y₀ < t → t ≤ (T i).y₁ →
      ((T i).x₀ < l.c ∧ l.c ≤ (T i).x₁) ∧ (T i).y₀ < t ∧ t ≤ (T i).y₁ :=
    fun t h₁ h₂ ↦ ⟨⟨hx₀, hxeq.ge⟩, h₁, h₂⟩
  have hup : (T i).y₁ ≤ l.hi := by
    refine not_lt.mp fun h ↦ ?_
    obtain heq | hbl := l.top
    · have := hT.tile_y₁_le i
      rw [← heq] at this
      linarith
    obtain ⟨j, hj₀, hj₁, hj₂, hj₃⟩ | ⟨⟨j, hj₀, hj₁, hj₂⟩, -⟩ := hbl
    · rcases hj₂.lt_or_eq with hlt | heq
      · exact l.not_straddle hj₀ hj₁
          (by rw [min_eq_right hj₃]; exact max_lt hlt l.lo_lt_hi)
      · have hjy : l.hi < (T j).y₁ := heq ▸ (hp j).2
        have hlt : l.hi < min (T i).y₁ (T j).y₁ := lt_min h hjy
        have h₁ : min (T i).y₁ (T j).y₁ ≤ (T i).y₁ := min_le_left _ _
        have h₂ : min (T i).y₁ (T j).y₁ ≤ (T j).y₁ := min_le_right _ _
        have hij := eq_of_cell hT (hcelli ((l.hi + min (T i).y₁ (T j).y₁) / 2)
            (by linarith) (by linarith))
          (j := j) ⟨⟨hj₀, hj₁.le⟩, by rw [← heq] at hlt ⊢; linarith, by linarith⟩
        rw [hij] at hxeq
        linarith
    · rcases hj₂ with heq | heq
      · have hjy : l.hi < (T j).y₁ := heq ▸ (hp j).2
        have hlt : l.hi < min (T i).y₁ (T j).y₁ := lt_min h hjy
        have h₁ : min (T i).y₁ (T j).y₁ ≤ (T i).y₁ := min_le_left _ _
        have h₂ : min (T i).y₁ (T j).y₁ ≤ (T j).y₁ := min_le_right _ _
        have hij := eq_of_cell hT (hcelli ((l.hi + min (T i).y₁ (T j).y₁) / 2)
            (by linarith) (by linarith))
          (j := j) ⟨⟨hj₀, hj₁⟩, by rw [heq]; linarith, by linarith⟩
        rw [← hij] at heq
        linarith
      · have hij := eq_of_cell hT (hcelli l.hi (by linarith) h.le)
          (j := j) ⟨⟨hj₀, hj₁⟩, by have := (hp j).2; linarith, heq.ge⟩
        rw [← hij] at heq
        linarith
  have hdn : l.lo ≤ (T i).y₀ := by
    refine not_lt.mp fun h ↦ ?_
    obtain heq | hbl := l.bot
    · have := hT.le_tile_y₀ i
      rw [← heq] at this
      linarith
    obtain ⟨j, hj₀, hj₁, hj₂, hj₃⟩ | ⟨⟨j, hj₀, hj₁, hj₂⟩, -⟩ := hbl
    · rcases hj₃.eq_or_lt with heq | hlt
      · have hij := eq_of_cell hT (hcelli l.lo h (by linarith))
          (j := j) ⟨⟨hj₀, hj₁.le⟩, by have := (hp j).2; linarith, heq.le⟩
        rw [hij] at hxeq
        linarith
      · exact l.not_straddle hj₀ hj₁
          (by rw [max_eq_right hj₂]; exact lt_min hlt l.lo_lt_hi)
    · rcases hj₂ with heq | heq
      · have hjy : (T j).y₀ < (T j).y₁ := (hp j).2
        have hlt : l.lo < min (T i).y₁ (T j).y₁ := lt_min (by linarith) (by linarith)
        have h₁ : min (T i).y₁ (T j).y₁ ≤ (T i).y₁ := min_le_left _ _
        have h₂ : min (T i).y₁ (T j).y₁ ≤ (T j).y₁ := min_le_right _ _
        have hij := eq_of_cell hT (hcelli ((l.lo + min (T i).y₁ (T j).y₁) / 2)
            (by linarith) (by linarith))
          (j := j) ⟨⟨hj₀, hj₁⟩, by rw [heq]; linarith, by linarith⟩
        rw [← hij] at heq
        linarith
      · have hij := eq_of_cell hT (hcelli l.lo h (by linarith))
          (j := j) ⟨⟨hj₀, hj₁⟩, by have := (hp j).2; linarith, heq.ge⟩
        rw [← hij] at heq
        linarith
  exact ⟨i, hxeq ▸ (hp i).1, hxeq, hdn, hup, hb, ht⟩

/-! ### The two sides of a link -/

/-- Reflecting the plane in the vertical axis exchanges the two sides of a vertical line, so it
preserves being blocked. -/
lemma blocked_reflectX (T : ι → Rectangle) (c y : ℝ) :
    Blocked (fun i ↦ (T i).reflectX) (-c) y ↔ Blocked T c y := by
  simp only [Blocked, Rectangle.reflectX, neg_lt_neg_iff, neg_le_neg_iff]
  constructor <;> rintro (⟨i, h₁, h₂, h₃, h₄⟩ | ⟨⟨i, h₁, h₂, h₃⟩, j, h₄, h₅, h₆⟩)
  · exact Or.inl ⟨i, h₂, h₁, h₃, h₄⟩
  · exact Or.inr ⟨⟨j, h₅, h₄, h₆⟩, i, h₂, h₁, h₃⟩
  · exact Or.inl ⟨i, h₂, h₁, h₃, h₄⟩
  · exact Or.inr ⟨⟨j, h₅, h₄, h₆⟩, i, h₂, h₁, h₃⟩

/-- Reflecting the plane in the vertical axis carries a V-link to a V-link. -/
def Link.reflectX (l : Link R T) : Link R.reflectX fun i ↦ (T i).reflectX where
  c := -l.c
  lo := l.lo
  hi := l.hi
  x₀_lt := by simpa [Rectangle.reflectX] using l.lt_x₁
  lt_x₁ := by simpa [Rectangle.reflectX] using l.x₀_lt
  lo_lt_hi := l.lo_lt_hi
  y₀_le := l.y₀_le
  le_y₁ := l.le_y₁
  free y h₁ h₂ := (blocked_reflectX T l.c y).not.mpr (l.free y h₁ h₂)
  bot := l.bot.imp id (blocked_reflectX T l.c l.lo).mpr
  top := l.top.imp id (blocked_reflectX T l.c l.hi).mpr

/-- **The tile abutting a V-link on the right at a given height**, the mirror image of
`Link.exists_left`. -/
theorem Link.exists_right (hT : IsTiling R T) (hp : Proper T) (l : Link R T) {y : ℝ}
    (hy₀ : l.lo < y) (hy₁ : y ≤ l.hi) :
    ∃ i, l.c < (T i).x₁ ∧ (T i).x₀ = l.c ∧ l.lo ≤ (T i).y₀ ∧ (T i).y₁ ≤ l.hi ∧
      (T i).y₀ < y ∧ y ≤ (T i).y₁ := by
  obtain ⟨i, h₁, h₂, h₃, h₄, h₅, h₆⟩ := Link.exists_left hT.reflectX
    (fun i ↦ ⟨by simpa [Rectangle.reflectX] using (hp i).1, (hp i).2⟩) l.reflectX hy₀ hy₁
  simp only [Rectangle.reflectX, Link.reflectX] at h₁ h₂
  exact ⟨i, by linarith, by linarith, h₃, h₄, h₅, h₆⟩

/-- Tile `i` abuts the link on the left: its right edge lies on the link. -/
def IsLeft (l : Link R T) (i : ι) : Prop := (T i).x₁ = l.c ∧ l.lo ≤ (T i).y₀ ∧ (T i).y₁ ≤ l.hi

/-- Tile `i` abuts the link on the right: its left edge lies on the link. -/
def IsRight (l : Link R T) (i : ι) : Prop := (T i).x₀ = l.c ∧ l.lo ≤ (T i).y₀ ∧ (T i).y₁ ≤ l.hi

lemma not_isLeft_isRight (hp : Proper T) {l : Link R T} {i : ι} (h : IsLeft l i)
    (h' : IsRight l i) : False := by
  have := (hp i).1
  rw [h.1, h'.1] at this
  exact lt_irrefl _ this

/-- **The tiles on the left of a link cover it.** -/
theorem exists_isLeft (hT : IsTiling R T) (hp : Proper T) (l : Link R T) {y : ℝ}
    (hy₀ : l.lo < y) (hy₁ : y ≤ l.hi) : ∃ i, IsLeft l i ∧ (T i).y₀ < y ∧ y ≤ (T i).y₁ := by
  obtain ⟨i, -, h₁, h₂, h₃, h₄, h₅⟩ := l.exists_left hT hp hy₀ hy₁
  exact ⟨i, ⟨h₁, h₂, h₃⟩, h₄, h₅⟩

/-- **The tiles on the right of a link cover it.** -/
theorem exists_isRight (hT : IsTiling R T) (hp : Proper T) (l : Link R T) {y : ℝ}
    (hy₀ : l.lo < y) (hy₁ : y ≤ l.hi) : ∃ i, IsRight l i ∧ (T i).y₀ < y ∧ y ≤ (T i).y₁ := by
  obtain ⟨i, -, h₁, h₂, h₃, h₄, h₅⟩ := l.exists_right hT hp hy₀ hy₁
  exact ⟨i, ⟨h₁, h₂, h₃⟩, h₄, h₅⟩

/-- **The tiles on the left of a link meet it in disjoint stretches.** -/
theorem isLeft_unique (hT : IsTiling R T) (hp : Proper T) {l : Link R T} {i j : ι} {y : ℝ}
    (hi : IsLeft l i) (hj : IsLeft l j) (hyi : (T i).y₀ < y ∧ y ≤ (T i).y₁)
    (hyj : (T j).y₀ < y ∧ y ≤ (T j).y₁) : i = j :=
  eq_of_cell hT (c := l.c) ⟨⟨by have := (hp i).1; rw [hi.1] at this; exact this, hi.1.ge⟩, hyi⟩
    ⟨⟨by have := (hp j).1; rw [hj.1] at this; exact this, hj.1.ge⟩, hyj⟩

/-! ### Pushing the tiles on the left of a link rightwards -/

open scoped Classical in
/-- The family obtained from `T` by pushing every tile on the left of the link `w` units
rightwards and paring every tile on its right back by the same amount. -/
noncomputable def push (l : Link R T) (w : ℝ) (hw : 0 ≤ w)
    (hR : ∀ i, IsRight l i → l.c + w ≤ (T i).x₁) (i : ι) : Rectangle :=
  if h : IsLeft l i then
    { x₀ := (T i).x₀, x₁ := l.c + w, y₀ := (T i).y₀, y₁ := (T i).y₁
      hx := by
        have h₁ := (T i).hx
        rw [h.1] at h₁
        linarith
      hy := (T i).hy }
  else if h' : IsRight l i then
    { x₀ := l.c + w, x₁ := (T i).x₁, y₀ := (T i).y₀, y₁ := (T i).y₁
      hx := hR i h'
      hy := (T i).hy }
  else T i

variable {l : Link R T} {w : ℝ} {hw : 0 ≤ w} {hR : ∀ i, IsRight l i → l.c + w ≤ (T i).x₁}

@[simp] lemma push_y₀ (i : ι) : (push l w hw hR i).y₀ = (T i).y₀ := by
  unfold push; split_ifs <;> rfl

@[simp] lemma push_y₁ (i : ι) : (push l w hw hR i).y₁ = (T i).y₁ := by
  unfold push; split_ifs <;> rfl

lemma push_x₀_of_isLeft {i : ι} (h : IsLeft l i) : (push l w hw hR i).x₀ = (T i).x₀ := by
  unfold push; rw [dif_pos h]

lemma push_x₁_of_isLeft {i : ι} (h : IsLeft l i) : (push l w hw hR i).x₁ = l.c + w := by
  unfold push; rw [dif_pos h]

lemma push_x₀_of_isRight (hp : Proper T) {i : ι} (h : IsRight l i) :
    (push l w hw hR i).x₀ = l.c + w := by
  unfold push; rw [dif_neg fun h' ↦ not_isLeft_isRight hp h' h, dif_pos h]

lemma push_x₁_of_isRight (hp : Proper T) {i : ι} (h : IsRight l i) :
    (push l w hw hR i).x₁ = (T i).x₁ := by
  unfold push; rw [dif_neg fun h' ↦ not_isLeft_isRight hp h' h, dif_pos h]

lemma push_of_not {i : ι} (h : ¬ IsLeft l i) (h' : ¬ IsRight l i) : push l w hw hR i = T i := by
  unfold push; rw [dif_neg h, dif_neg h']

private lemma mem_toSetIoc' {S : Rectangle} {x y : ℝ} :
    ((x, y) : ℝ × ℝ) ∈ S.toSetIoc ↔ (S.x₀ < x ∧ x ≤ S.x₁) ∧ S.y₀ < y ∧ y ≤ S.y₁ := Iff.rfl

/-- **Pushing the tiles on the left of a link rightwards again tiles the same rectangle.** The
strip `(c, c + w] × (lo, hi]` that the tiles on the left sweep out is exactly the strip that the
tiles on the right vacate, so the cells still partition `R`. -/
theorem isTiling_push (hT : IsTiling R T) (hp : Proper T) (hRx : R.x₀ < R.x₁) (hRy : R.y₀ < R.y₁)
    {l : Link R T} {w : ℝ} (hw0 : 0 < w) (hR : ∀ i, IsRight l i → l.c + w ≤ (T i).x₁) :
    IsTiling R (push l w hw0.le hR) := by
  obtain ⟨k₀, hk₀, -, -⟩ := exists_isRight hT hp l l.lo_lt_hi le_rfl
  have hcw : l.c + w ≤ R.x₁ := (hR k₀ hk₀).trans (hT.tile_x₁_le k₀)
  -- Every point of the swept strip lies in the cell of a tile on the right of the link.
  have hstrip : ∀ x y : ℝ, l.c < x → x ≤ l.c + w → l.lo < y → y ≤ l.hi →
      ∃ k, IsRight l k ∧ ((x, y) : ℝ × ℝ) ∈ (T k).toSetIoc := by
    intro x y h₁ h₂ h₃ h₄
    obtain ⟨k, hk, hy₀, hy₁⟩ := exists_isRight hT hp l h₃ h₄
    exact ⟨k, hk, ⟨by rw [hk.1]; exact h₁, h₂.trans (hR k hk)⟩, hy₀, hy₁⟩
  -- A pushed cell either stays inside the old cell or reaches into the swept strip.
  have hnew : ∀ (i : ι) (x y : ℝ), ((x, y) : ℝ × ℝ) ∈ (push l w hw0.le hR i).toSetIoc →
      ((x, y) : ℝ × ℝ) ∈ (T i).toSetIoc ∨ ((l.c < x ∧ x ≤ l.c + w) ∧ l.lo < y ∧ y ≤ l.hi) := by
    intro i x y hmem
    by_cases hL : IsLeft l i
    · simp only [mem_toSetIoc', push_x₀_of_isLeft hL, push_x₁_of_isLeft hL, push_y₀,
        push_y₁] at hmem
      rcases le_or_gt x l.c with h | h
      · exact Or.inl ⟨⟨hmem.1.1, by rw [hL.1]; exact h⟩, hmem.2⟩
      · exact Or.inr ⟨⟨h, hmem.1.2⟩, hL.2.1.trans_lt hmem.2.1, hmem.2.2.trans hL.2.2⟩
    by_cases hRi : IsRight l i
    · simp only [mem_toSetIoc', push_x₀_of_isRight hp hRi, push_x₁_of_isRight hp hRi, push_y₀,
        push_y₁] at hmem
      exact Or.inl ⟨⟨by rw [hRi.1]; linarith [hmem.1.1], hmem.1.2⟩, hmem.2⟩
    · rw [push_of_not hL hRi] at hmem
      exact Or.inl hmem
  -- Only a tile on the left of the link reaches into the swept strip.
  have hkey : ∀ (i : ι) (x y : ℝ), ((x, y) : ℝ × ℝ) ∈ (push l w hw0.le hR i).toSetIoc →
      l.c < x → x ≤ l.c + w → l.lo < y → y ≤ l.hi → IsLeft l i := by
    intro i x y hmem h₁ h₂ h₃ h₄
    by_cases hL : IsLeft l i
    · exact hL
    by_cases hRi : IsRight l i
    · rw [mem_toSetIoc', push_x₀_of_isRight hp hRi] at hmem
      exact absurd hmem.1.1 (not_lt.mpr h₂)
    · rw [push_of_not hL hRi] at hmem
      obtain ⟨k, hk, hkmem⟩ := hstrip x y h₁ h₂ h₃ h₄
      have : i = k := hT.eq_of_mem_cell (sx := true) (sy := true) hmem hkmem
      subst this
      exact absurd hk hRi
  have hbounds : ∀ i : ι,
      R.x₀ ≤ (push l w hw0.le hR i).x₀ ∧ (push l w hw0.le hR i).x₁ ≤ R.x₁ := by
    intro i
    by_cases hL : IsLeft l i
    · rw [push_x₀_of_isLeft hL, push_x₁_of_isLeft hL]
      exact ⟨hT.le_tile_x₀ i, hcw⟩
    by_cases hRi : IsRight l i
    · rw [push_x₀_of_isRight hp hRi, push_x₁_of_isRight hp hRi]
      exact ⟨by have := l.x₀_lt; linarith, hT.tile_x₁_le i⟩
    · rw [push_of_not hL hRi]
      exact ⟨hT.le_tile_x₀ i, hT.tile_x₁_le i⟩
  refine isTiling_of_toSetIoc hRx hRy (fun i ↦ ?_) (fun i j hij ↦ ?_) (fun z hz ↦ ?_)
  · rintro ⟨a, b⟩ ⟨⟨h₁, h₂⟩, h₃, h₄⟩
    obtain ⟨hb₁, hb₂⟩ := hbounds i
    rw [push_y₀] at h₃
    rw [push_y₁] at h₄
    exact ⟨⟨by linarith, by linarith⟩, by linarith [hT.le_tile_y₀ i],
      by linarith [hT.tile_y₁_le i]⟩
  · rw [Function.onFun, Set.disjoint_left]
    rintro ⟨x, y⟩ hi hj
    by_cases hs : (l.c < x ∧ x ≤ l.c + w) ∧ l.lo < y ∧ y ≤ l.hi
    · have hLi := hkey i x y hi hs.1.1 hs.1.2 hs.2.1 hs.2.2
      have hLj := hkey j x y hj hs.1.1 hs.1.2 hs.2.1 hs.2.2
      simp only [mem_toSetIoc', push_y₀, push_y₁] at hi hj
      exact hij (isLeft_unique hT hp hLi hLj hi.2 hj.2)
    · rcases hnew i x y hi with hi' | hi'
      · rcases hnew j x y hj with hj' | hj'
        · exact hij (hT.eq_of_mem_cell (sx := true) (sy := true) hi' hj')
        · exact hs hj'
      · exact hs hi'
  · obtain ⟨x, y⟩ := z
    obtain ⟨i, hi, -⟩ := hT.existsUnique_toSetIoc hz
    rw [mem_toSetIoc'] at hi
    by_cases hRi : IsRight l i
    · rcases le_or_gt x (l.c + w) with hx | hx
      · obtain ⟨j, hLj, hj₀, hj₁⟩ := exists_isLeft hT hp l (hRi.2.1.trans_lt hi.2.1)
          (hi.2.2.trans hRi.2.2)
        refine Set.mem_iUnion.mpr ⟨j, ?_⟩
        simp only [mem_toSetIoc', push_x₀_of_isLeft hLj, push_x₁_of_isLeft hLj, push_y₀, push_y₁]
        refine ⟨⟨?_, hx⟩, hj₀, hj₁⟩
        have h₁ := (hp j).1
        rw [hLj.1] at h₁
        rw [hRi.1] at hi
        linarith [hi.1.1]
      · refine Set.mem_iUnion.mpr ⟨i, ?_⟩
        simp only [mem_toSetIoc', push_x₀_of_isRight hp hRi, push_x₁_of_isRight hp hRi, push_y₀,
          push_y₁]
        exact ⟨⟨hx, hi.1.2⟩, hi.2⟩
    · by_cases hL : IsLeft l i
      · refine Set.mem_iUnion.mpr ⟨i, ?_⟩
        simp only [mem_toSetIoc', push_x₀_of_isLeft hL, push_x₁_of_isLeft hL, push_y₀, push_y₁]
        rw [hL.1] at hi
        exact ⟨⟨hi.1.1, by linarith [hi.1.2]⟩, hi.2⟩
      · exact Set.mem_iUnion.mpr ⟨i, by rw [push_of_not hL hRi, mem_toSetIoc']; exact hi⟩

/-! ### Every interior vertical tile edge lies on a link -/

open scoped Classical in
/-- The heights at which a tile, or the tiled rectangle, has a horizontal edge. The ends of a link
are among them. -/
noncomputable def edgeHeights (R : Rectangle) (T : ι → Rectangle) : Finset ℝ :=
  insert R.y₀ (insert R.y₁ ((Finset.univ.image fun i ↦ (T i).y₀) ∪
    Finset.univ.image fun i ↦ (T i).y₁))

lemma y₀_mem_edgeHeights (i : ι) : (T i).y₀ ∈ edgeHeights R T := by simp [edgeHeights]

lemma y₁_mem_edgeHeights (i : ι) : (T i).y₁ ∈ edgeHeights R T := by simp [edgeHeights]

/-- **Every vertical tile edge interior to `R` carries a V-link straddling that edge.** -/
theorem exists_link (hT : IsTiling R T) (hp : Proper T) {k : ι} (hlt : (T k).x₁ < R.x₁) :
    ∃ l : Link R T, l.c = (T k).x₁ ∧ l.lo ≤ (T k).y₀ ∧ (T k).y₁ ≤ l.hi := by
  classical
  set c := (T k).x₁ with hc
  have hkx : (T k).x₀ < c := (hp k).1
  have hky : (T k).y₀ < (T k).y₁ := (hp k).2
  -- A tile crossing the line `x = c` at a height inside `T k` would overlap `T k`.
  have hconf : ∀ j : ι, (T j).x₀ < c → c < (T j).x₁ →
      max (T j).y₀ (T k).y₀ < min (T j).y₁ (T k).y₁ → False := by
    intro j h₁ h₂ h₃
    have ha₁ : (T j).y₀ ≤ max (T j).y₀ (T k).y₀ := le_max_left _ _
    have ha₂ : (T k).y₀ ≤ max (T j).y₀ (T k).y₀ := le_max_right _ _
    have hb₁ : min (T j).y₁ (T k).y₁ ≤ (T j).y₁ := min_le_left _ _
    have hb₂ : min (T j).y₁ (T k).y₁ ≤ (T k).y₁ := min_le_right _ _
    have hjk : j = k := hT.eq_of_mem_cell (sx := true) (sy := true) (x := c)
      (y := (max (T j).y₀ (T k).y₀ + min (T j).y₁ (T k).y₁) / 2)
      ⟨⟨h₁, h₂.le⟩, by linarith, by linarith⟩ ⟨⟨hkx, le_rfl⟩, by linarith, by linarith⟩
    rw [hjk] at h₂
    exact absurd h₂ (lt_irrefl _)
  -- No height strictly inside `T k` is blocked on the line `x = c`.
  have hfree : ∀ y, (T k).y₀ < y → y < (T k).y₁ → ¬ Blocked T c y := by
    rintro y h₁ h₂ (⟨j, hj₁, hj₂, hj₃, hj₄⟩ | ⟨⟨j, hj₁, hj₂, hj₃⟩, -⟩)
    · rcases hj₃.lt_or_eq with h | h
      · exact hconf j hj₁ hj₂ ((max_lt h h₁).trans_le (le_min hj₄ h₂.le))
      · refine hconf j hj₁ hj₂ ?_
        rw [max_eq_left (by linarith : (T k).y₀ ≤ (T j).y₀)]
        exact lt_min (hp j).2 (by linarith)
    · have hjy := (hp j).2
      have hm₁ : min (T j).y₁ (T k).y₁ ≤ (T j).y₁ := min_le_left _ _
      have hm₂ : min (T j).y₁ (T k).y₁ ≤ (T k).y₁ := min_le_right _ _
      rcases hj₃ with h | h
      · have hym : y < min (T j).y₁ (T k).y₁ := lt_min (by linarith) h₂
        have hjk : j = k := hT.eq_of_mem_cell (sx := true) (sy := true) (x := c)
          (y := (y + min (T j).y₁ (T k).y₁) / 2)
          ⟨⟨hj₁, hj₂⟩, by rw [h]; linarith, by linarith⟩
          ⟨⟨hkx, le_rfl⟩, by linarith, by linarith⟩
        rw [hjk] at h
        linarith
      · have hjk : j = k := hT.eq_of_mem_cell (sx := true) (sy := true) (x := c) (y := y)
          ⟨⟨hj₁, hj₂⟩, by linarith, h.ge⟩ ⟨⟨hkx, le_rfl⟩, h₁, h₂.le⟩
        rw [hjk] at h
        linarith
  -- The lower end of the link.
  set Slo := insert R.y₀ ((edgeHeights R T).filter fun a ↦ a ≤ (T k).y₀ ∧ Blocked T c a) with hSlo
  have hSloNe : Slo.Nonempty := ⟨R.y₀, Finset.mem_insert_self _ _⟩
  set lo := Slo.max' hSloNe with hlodef
  have hlo_le : lo ≤ (T k).y₀ := by
    rcases Finset.mem_insert.mp (Slo.max'_mem hSloNe) with h | h
    · rw [hlodef, h]; exact hT.le_tile_y₀ k
    · rw [hlodef]; exact (Finset.mem_filter.mp h).2.1
  have hlo_ge : R.y₀ ≤ lo := Slo.le_max' _ (Finset.mem_insert_self _ _)
  have hlo_spec : lo = R.y₀ ∨ Blocked T c lo :=
    (Finset.mem_insert.mp (Slo.max'_mem hSloNe)).imp id fun h ↦ (Finset.mem_filter.mp h).2.2
  have hlo_max : ∀ a : ℝ, a ∈ edgeHeights R T → a ≤ (T k).y₀ → Blocked T c a → a ≤ lo :=
    fun a h₁ h₂ h₃ ↦ Slo.le_max' a (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h₁, h₂, h₃⟩))
  -- The upper end of the link.
  set Shi := insert R.y₁ ((edgeHeights R T).filter fun a ↦ (T k).y₁ ≤ a ∧ Blocked T c a) with hShi
  have hShiNe : Shi.Nonempty := ⟨R.y₁, Finset.mem_insert_self _ _⟩
  set hi := Shi.min' hShiNe with hhidef
  have hhi_ge : (T k).y₁ ≤ hi := by
    rcases Finset.mem_insert.mp (Shi.min'_mem hShiNe) with h | h
    · rw [hhidef, h]; exact hT.tile_y₁_le k
    · rw [hhidef]; exact (Finset.mem_filter.mp h).2.1
  have hhi_le : hi ≤ R.y₁ := Shi.min'_le _ (Finset.mem_insert_self _ _)
  have hhi_spec : hi = R.y₁ ∨ Blocked T c hi :=
    (Finset.mem_insert.mp (Shi.min'_mem hShiNe)).imp id fun h ↦ (Finset.mem_filter.mp h).2.2
  have hhi_min : ∀ a : ℝ, a ∈ edgeHeights R T → (T k).y₁ ≤ a → Blocked T c a → hi ≤ a :=
    fun a h₁ h₂ h₃ ↦ Shi.min'_le a (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h₁, h₂, h₃⟩))
  refine ⟨⟨c, lo, hi, (hT.le_tile_x₀ k).trans_lt hkx, hlt, by linarith, hlo_ge, hhi_le,
    fun y h₁ h₂ hb ↦ ?_, hlo_spec, hhi_spec⟩, rfl, hlo_le, hhi_ge⟩
  by_cases hA : y ≤ (T k).y₀
  · have hb' := hb
    rcases hb with ⟨j, hj₁, hj₂, hj₃, hj₄⟩ | ⟨⟨j, hj₁, hj₂, hj₃⟩, -⟩
    · by_cases hj : (T j).y₁ ≤ (T k).y₀
      · have := hlo_max _ (y₁_mem_edgeHeights j) hj (Or.inl ⟨j, hj₁, hj₂, (hp j).2.le, le_rfl⟩)
        linarith
      · refine hconf j hj₁ hj₂ ?_
        rw [max_eq_right (by linarith : (T j).y₀ ≤ (T k).y₀)]
        exact lt_min (not_le.mp hj) hky
    · have hy : y ∈ edgeHeights R T := by
        rcases hj₃ with h | h
        · exact h ▸ y₀_mem_edgeHeights j
        · exact h ▸ y₁_mem_edgeHeights j
      linarith [hlo_max y hy hA hb']
  by_cases hB : (T k).y₁ ≤ y
  · have hb' := hb
    rcases hb with ⟨j, hj₁, hj₂, hj₃, hj₄⟩ | ⟨⟨j, hj₁, hj₂, hj₃⟩, -⟩
    · by_cases hj : (T k).y₁ ≤ (T j).y₀
      · have := hhi_min _ (y₀_mem_edgeHeights j) hj (Or.inl ⟨j, hj₁, hj₂, le_rfl, (hp j).2.le⟩)
        linarith
      · refine hconf j hj₁ hj₂ ?_
        rw [min_eq_right (by linarith : (T k).y₁ ≤ (T j).y₁)]
        exact max_lt (not_le.mp hj) hky
    · have hy : y ∈ edgeHeights R T := by
        rcases hj₃ with h | h
        · exact h ▸ y₀_mem_edgeHeights j
        · exact h ▸ y₁_mem_edgeHeights j
      linarith [hhi_min y hy hB hb']
  · exact hfree y (not_le.mp hA) (not_le.mp hB) hb

end IntegerRectangle.ReducibleLink
