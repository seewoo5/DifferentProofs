/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Combinatorics.Graph.Basic

/-!
# Connected multigraphs

A multigraph `G : Graph α β` is connected when it has a vertex and any two of its vertices are
joined by a chain of edges. Mathlib's multigraphs have no walks yet, so
`Relation.ReflTransGen G.Adj` stands in for reachability. This file is intended for
`Mathlib/Combinatorics/Graph/Connected/Basic.lean`.
-/

@[expose] public section

namespace Graph

variable {α β : Type*}

/-- A multigraph is **connected** when it has a vertex and any two of its vertices are joined by
a chain of edges. -/
def Connected (G : Graph α β) : Prop :=
  V(G).Nonempty ∧ ∀ ⦃x⦄, x ∈ V(G) → ∀ ⦃y⦄, y ∈ V(G) → Relation.ReflTransGen G.Adj x y

end Graph
