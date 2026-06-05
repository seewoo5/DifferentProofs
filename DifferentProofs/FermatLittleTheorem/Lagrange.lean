module

public import DifferentProofs.FermatLittleTheorem.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

theorem FermatLittleTheorem_Lagrange : FermatLittleTheorem := by
  intro p a hp
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  by_cases ha : (a : ZMod p) = 0
  · rw [ha, zero_pow hp.ne_zero]
  · have h_pow : (a : ZMod p) ^ (p - 1) = 1 := by
      have hu : (Units.mk0 ((a : ℤ) : ZMod p) ha) ^ Fintype.card (ZMod p)ˣ = 1 := pow_card_eq_one
      rw [ZMod.card_units] at hu
      simpa [Units.val_pow_eq_pow_val] using congr_arg Units.val hu
    rw [← pow_sub_one_mul hp.ne_zero, h_pow, one_mul]
