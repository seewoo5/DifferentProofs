/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.CoprodI

/-!
# The coproduct of a `Bool`-indexed family of monoids

The binary coproduct `M ∗ N` (`Monoid.Coprod`) and the coproduct of a family `Monoid.CoprodI` are
defined independently in mathlib. This file proves that the coproduct of a family `M : Bool → Type*`
is the binary coproduct of its two members (`Monoid.CoprodI.boolEquivCoprod`), so that results
proved for `Monoid.CoprodI`, such as the ping-pong lemma
`Monoid.CoprodI.lift_injective_of_ping_pong`, can be transferred to `M ∗ N`.

This is one of the two comparisons listed as a TODO in `Mathlib/GroupTheory/Coprod/Basic.lean`.
That file does not import `Mathlib/GroupTheory/CoprodI.lean`, so in mathlib this would be a new
file importing both.
-/

@[expose] public section

open scoped Monoid.Coprod

namespace Monoid.CoprodI

variable {M : Bool → Type*} [∀ i, Monoid (M i)]

/-- The coproduct of a family of monoids indexed by `Bool` is the binary coproduct of its two
members. -/
def boolEquivCoprod : CoprodI M ≃* M false ∗ M true :=
  MonoidHom.toMulEquiv (lift fun | false => Coprod.inl | true => Coprod.inr)
    (Coprod.lift of of) (by ext (_ | _) <;> simp) (by ext <;> simp)

@[simp]
theorem boolEquivCoprod_of_false (x : M false) : boolEquivCoprod (of x) = Coprod.inl x := by
  simp [boolEquivCoprod]

@[simp]
theorem boolEquivCoprod_of_true (x : M true) : boolEquivCoprod (of x) = Coprod.inr x := by
  simp [boolEquivCoprod]

@[simp]
theorem boolEquivCoprod_symm_inl (x : M false) : boolEquivCoprod.symm (Coprod.inl x) = of x := by
  simp [boolEquivCoprod]

@[simp]
theorem boolEquivCoprod_symm_inr (x : M true) : boolEquivCoprod.symm (Coprod.inr x) = of x := by
  simp [boolEquivCoprod]

end Monoid.CoprodI
