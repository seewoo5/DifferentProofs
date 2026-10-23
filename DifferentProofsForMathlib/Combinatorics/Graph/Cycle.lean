/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Combinatorics.Graph.Basic

/-!
# Cycles of multigraphs

A cycle of a multigraph `G : Graph α β` is recorded by its set of edges: `G.IsCycle C` says that
the edges of `C` can be listed cyclically, without repetition, each joining the vertex before it
to the vertex after it, all these vertices distinct. Loops are cycles of length one and pairs of
parallel edges cycles of length two.

Mathlib's multigraphs have no walks yet, so the cycle is given by its two cyclic sequences
indexed by `Fin (n + 1)`, whose addition wraps around. This file is intended for a future
`Mathlib/Combinatorics/Graph/Walk/Cycle.lean`, where the definition would be restated as the
edge set of a closed walk that repeats no vertex.
-/

@[expose] public section

namespace Graph

variable {α β : Type*}

/-- `C` is the edge set of a **cycle** of `G`: its edges can be listed without repetition as
`e 0, …, e n`, with `e k` joining `v k` to `v (k + 1)` for distinct vertices `v 0, …, v n`,
indices read modulo `n + 1`. -/
def IsCycle (G : Graph α β) (C : Set β) : Prop :=
  ∃ (n : ℕ) (v : Fin (n + 1) → α) (e : Fin (n + 1) → β), Function.Injective v ∧
    Function.Injective e ∧ (∀ k, G.IsLink (e k) (v k) (v (k + 1))) ∧ Set.range e = C

end Graph
