module

public import DifferentProofs.FermatLittleTheorem.Defs
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Data.ZMod.Basic

@[expose] public section

theorem FermatLittleTheorem_Binomial : FermatLittleTheorem := by
  intro p a hp
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [← ZMod.natCast_zmod_val (a : ZMod p)]
  induction (a : ZMod p).val with
  | zero => simp [zero_pow hp.ne_zero]
  | succ k ih => rw [Nat.cast_succ, add_pow_expChar, ih, one_pow]
