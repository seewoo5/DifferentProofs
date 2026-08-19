module

public import DifferentProofs.IntegerRectangle.Cells

/-!
# Walking along the tiles of a tiling

The inductive proofs of the integer-rectangle theorem all travel through a tiling one tile at a
time: up a stack of tiles resting on one another, or sideways across a row. Such a walk stops
because every tile edge sits at one of the finitely many coordinates carrying an edge of the
tiling (`edgeHeights` horizontally, `edgeAbscissae` vertically) and each step uses one of them up.
The four walks below package that termination argument once and for all: given a family `P` of
tiles and a rule for stepping from a tile of `P` to the next one in a given direction, they return
the tiles of `P` met along the way, up to the edge of the tiled rectangle.
-/

@[expose] public section

namespace IntegerRectangle

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-! ### The coordinates carrying an edge of the tiling -/

open scoped Classical in
/-- The heights at which a tile, or the tiled rectangle, has a horizontal edge. The ends of a link
are among them. -/
noncomputable def edgeHeights (R : Rectangle) (T : ι → Rectangle) : Finset ℝ :=
  insert R.y₀ (insert R.y₁ ((Finset.univ.image fun i ↦ (T i).y₀) ∪
    Finset.univ.image fun i ↦ (T i).y₁))

lemma y₀_mem_edgeHeights (i : ι) : (T i).y₀ ∈ edgeHeights R T := by simp [edgeHeights]

lemma y₁_mem_edgeHeights (i : ι) : (T i).y₁ ∈ edgeHeights R T := by simp [edgeHeights]

open scoped Classical in
/-- The abscissae at which a tile, or the tiled rectangle, has a vertical edge. -/
noncomputable def edgeAbscissae (R : Rectangle) (T : ι → Rectangle) : Finset ℝ :=
  insert R.x₀ (insert R.x₁ ((Finset.univ.image fun i ↦ (T i).x₀) ∪
    Finset.univ.image fun i ↦ (T i).x₁))

lemma x₀_mem_edgeAbscissae (i : ι) : (T i).x₀ ∈ edgeAbscissae R T := by simp [edgeAbscissae]

lemma x₁_mem_edgeAbscissae (i : ι) : (T i).x₁ ∈ edgeAbscissae R T := by simp [edgeAbscissae]

/-- **Walking up a stack of tiles.** If from every tile of the family `P` whose top edge is below
`top` one can step to a tile of `P` sitting directly on it, then every height up to `top` above a
tile of `P` is met by a tile of `P`. The walk terminates because each step raises the top edge to
a strictly higher one of the finitely many edge heights. -/
theorem walk_up {P : ι → Prop} {top : ℝ}
    (hstep : ∀ s, P s → (T s).y₁ < top →
      ∃ s', P s' ∧ (T s').y₀ = (T s).y₁ ∧ (T s).y₁ < (T s').y₁) :
    ∀ n : ℕ, ∀ s, P s → ((edgeHeights R T).filter fun a ↦ (T s).y₁ < a ∧ a ≤ top).card ≤ n →
      ∀ y, (T s).y₀ < y → y ≤ top → ∃ s', P s' ∧ (T s').y₀ < y ∧ y ≤ (T s').y₁ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs hcard y hy₀ hy₁
    by_cases hcase : y ≤ (T s).y₁
    · exact ⟨s, hs, hy₀, hcase⟩
    push Not at hcase
    obtain ⟨s', hs', hy, hgt⟩ := hstep s hs (hcase.trans_le hy₁)
    by_cases hover : top < (T s').y₁
    · exact ⟨s', hs', by rw [hy]; exact hcase, hy₁.trans hover.le⟩
    push Not at hover
    refine ih _ (lt_of_lt_of_le (Finset.card_lt_card ⟨fun a ha ↦ ?_, fun hcon ↦ ?_⟩) hcard) s' hs'
      le_rfl y (by rw [hy]; exact hcase) hy₁
    · obtain ⟨h₁, h₂, h₃⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨h₁, hgt.trans h₂, h₃⟩
    · exact absurd (Finset.mem_filter.mp (hcon (Finset.mem_filter.mpr
        ⟨y₁_mem_edgeHeights s', hgt, hover⟩))).2.1 (lt_irrefl _)

/-- **Walking down a stack of tiles**, the mirror image of `walk_up`. -/
theorem walk_down {P : ι → Prop} {bot : ℝ}
    (hstep : ∀ s, P s → bot < (T s).y₀ →
      ∃ s', P s' ∧ (T s').y₁ = (T s).y₀ ∧ (T s').y₀ < (T s).y₀) :
    ∀ n : ℕ, ∀ s, P s → ((edgeHeights R T).filter fun a ↦ bot ≤ a ∧ a < (T s).y₀).card ≤ n →
      ∀ y, bot < y → y ≤ (T s).y₁ → ∃ s', P s' ∧ (T s').y₀ < y ∧ y ≤ (T s').y₁ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs hcard y hy₀ hy₁
    by_cases hcase : (T s).y₀ < y
    · exact ⟨s, hs, hcase, hy₁⟩
    push Not at hcase
    obtain ⟨s', hs', hy, hlt⟩ := hstep s hs (hy₀.trans_le hcase)
    by_cases hunder : (T s').y₀ < bot
    · exact ⟨s', hs', hunder.trans hy₀, by rw [hy]; exact hcase⟩
    push Not at hunder
    refine ih _ (lt_of_lt_of_le (Finset.card_lt_card ⟨fun a ha ↦ ?_, fun hcon ↦ ?_⟩) hcard) s' hs'
      le_rfl y hy₀ (by rw [hy]; exact hcase)
    · obtain ⟨h₁, h₂, h₃⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨h₁, h₂, h₃.trans hlt⟩
    · exact absurd (Finset.mem_filter.mp (hcon (Finset.mem_filter.mpr
        ⟨y₀_mem_edgeHeights s', hunder, hlt⟩))).2.2 (lt_irrefl _)

/-- **Walking rightwards to the right-hand edge.** If from every tile of the family `P` not
reaching the right edge of `R` one can step to a tile of `P` reaching further right, then some
tile of `P` has its right edge on that of `R`. -/
theorem walk_right (hT : IsTiling R T) {P : ι → Prop}
    (hstep : ∀ i, P i → (T i).x₁ < R.x₁ → ∃ j, P j ∧ (T i).x₁ < (T j).x₁) :
    ∀ n : ℕ, ∀ i, P i → ((edgeAbscissae R T).filter fun a ↦ (T i).x₁ < a ∧ a ≤ R.x₁).card ≤ n →
      ∃ u, P u ∧ (T u).x₁ = R.x₁ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi hcard
    rcases (hT.tile_x₁_le i).lt_or_eq with hlt | heq
    · obtain ⟨j, hj, hgt⟩ := hstep i hi hlt
      refine ih _ (lt_of_lt_of_le (Finset.card_lt_card ⟨fun a ha ↦ ?_, fun hcon ↦ ?_⟩) hcard) j hj
        le_rfl
      · obtain ⟨h₁, h₂, h₃⟩ := Finset.mem_filter.mp ha
        exact Finset.mem_filter.mpr ⟨h₁, hgt.trans h₂, h₃⟩
      · exact absurd (Finset.mem_filter.mp (hcon (Finset.mem_filter.mpr
          ⟨x₁_mem_edgeAbscissae j, hgt, hT.tile_x₁_le j⟩))).2.1 (lt_irrefl _)
    · exact ⟨i, hi, heq⟩

/-- **Walking leftwards to the left-hand edge**, the mirror image of `walk_right`. -/
theorem walk_left (hT : IsTiling R T) {P : ι → Prop}
    (hstep : ∀ i, P i → R.x₀ < (T i).x₀ → ∃ j, P j ∧ (T j).x₀ < (T i).x₀) :
    ∀ n : ℕ, ∀ i, P i → ((edgeAbscissae R T).filter fun a ↦ R.x₀ ≤ a ∧ a < (T i).x₀).card ≤ n →
      ∃ u, P u ∧ (T u).x₀ = R.x₀ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi hcard
    rcases (hT.le_tile_x₀ i).lt_or_eq with hlt | heq
    · obtain ⟨j, hj, hlt'⟩ := hstep i hi hlt
      refine ih _ (lt_of_lt_of_le (Finset.card_lt_card ⟨fun a ha ↦ ?_, fun hcon ↦ ?_⟩) hcard) j hj
        le_rfl
      · obtain ⟨h₁, h₂, h₃⟩ := Finset.mem_filter.mp ha
        exact Finset.mem_filter.mpr ⟨h₁, h₂, h₃.trans hlt'⟩
      · exact absurd (Finset.mem_filter.mp (hcon (Finset.mem_filter.mpr
          ⟨x₀_mem_edgeAbscissae j, hT.le_tile_x₀ j, hlt'⟩))).2.2 (lt_irrefl _)
    · exact ⟨i, hi, heq.symm⟩

/-- **Walking down until a goal is reached.** If from every tile of the family `P` that has not
reached the goal one can step to a tile of `P` sitting strictly lower, then some tile of `P` has
reached it. The walk terminates because each step lowers the bottom edge to a strictly lower one
of the finitely many edge heights. -/
theorem walk_down_until {P Goal : ι → Prop}
    (hstep : ∀ s, P s → ¬ Goal s → ∃ s', P s' ∧ (T s').y₀ < (T s).y₀) :
    ∀ n : ℕ, ∀ s, P s → ((edgeHeights R T).filter fun a ↦ a < (T s).y₀).card ≤ n →
      ∃ u, P u ∧ Goal u := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs hcard
    by_cases hgoal : Goal s
    · exact ⟨s, hs, hgoal⟩
    obtain ⟨s', hs', hlt⟩ := hstep s hs hgoal
    refine ih _ (lt_of_lt_of_le (Finset.card_lt_card ⟨fun a ha ↦ ?_, fun hcon ↦ ?_⟩) hcard) s' hs'
      le_rfl
    · obtain ⟨h₁, h₂⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨h₁, h₂.trans hlt⟩
    · exact absurd (Finset.mem_filter.mp (hcon (Finset.mem_filter.mpr
        ⟨y₀_mem_edgeHeights s', hlt⟩))).2 (lt_irrefl _)

end IntegerRectangle
