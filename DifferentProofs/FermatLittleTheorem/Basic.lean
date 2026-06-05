module

public import DifferentProofs.FermatLittleTheorem.Defs
public import Mathlib.Data.ZMod.Basic

@[expose] public section

theorem FermatLittleTheoremNat_impl_FermatLittleTheorem :
    FermatLittleTheoremNat → FermatLittleTheorem := by
  intro hN p a hp
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [← ZMod.natCast_zmod_val (a : ZMod p), ← Nat.cast_pow]
  exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hN p _ hp)
