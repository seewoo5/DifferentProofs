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
  set b : ℕ := (a : ZMod p).val with hb
  have hN_b : b ^ p ≡ b [MOD p] := hN p b hp
  rw [show (a : ZMod p) = (b : ZMod p) from (ZMod.natCast_zmod_val _).symm,
      show ((b : ZMod p))^p = ((b^p : ℕ) : ZMod p) by push_cast; rfl]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hN_b
