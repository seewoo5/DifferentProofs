/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Almost-everywhere disjointness of closed intervals

Two closed intervals differ from the corresponding open intervals only in their endpoints, which
are null for an atomless measure. So closed intervals with disjoint interiors — intervals that
overlap in at most a shared endpoint — are almost everywhere disjoint.

This complements the interval almost-everywhere equalities such as `MeasureTheory.Ioo_ae_eq_Icc`
in `Mathlib/MeasureTheory/Measure/Typeclasses/NoAtoms.lean`, which is where it is intended to live;
`MeasureTheory.AEDisjoint` is already available there.
-/

public section

namespace MeasureTheory

open Set

variable {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α} [NullSingletonClass μ]
  [PartialOrder α] {a b c d : α}

/-- Closed intervals whose open counterparts are disjoint are almost everywhere disjoint: they can
meet only in endpoints, and an atomless measure gives those no mass. -/
theorem aedisjoint_Icc_of_disjoint_Ioo (h : Disjoint (Ioo a b) (Ioo c d)) :
    AEDisjoint μ (Icc a b) (Icc c d) :=
  h.aedisjoint.congr Ioo_ae_eq_Icc.symm Ioo_ae_eq_Icc.symm

end MeasureTheory
