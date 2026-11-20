module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Comparator challenge: the modular group is a free product

Each theorem below records the statement that the correspondingly named declaration in
`DifferentProofs.ModularGroup.*` is required to prove. See `README.md` for what the Comparator check
guarantees and how to run it.
-/

@[expose] public section

open scoped MatrixGroups Monoid.Coprod

/-- **The modular group is a free product**: `PSL(2, ℤ) = SL(2, ℤ) / {±1}` is isomorphic to the
free product of a cyclic group of order two and a cyclic group of order three. -/
def ModularGroupFreeProduct : Prop :=
  Nonempty (PSL(2, ℤ) ≃* Multiplicative (ZMod 2) ∗ Multiplicative (ZMod 3))

theorem ModularGroupFreeProduct_Alperin : ModularGroupFreeProduct := sorry
