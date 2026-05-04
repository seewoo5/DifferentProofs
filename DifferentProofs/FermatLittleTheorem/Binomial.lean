module

public import DifferentProofs.FermatLittleTheorem.Defs
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-- **Fermat's Little Theorem using the Binomial theorem**

Use Freshmen's dream: $(a + b)^p = a^p + b^p$ in characteristic $p$.
Then $(a + 1)^p \equiv a^p + 1 \pmod{p}$, and the result follows by induction on $a$.
-/
theorem FermatLittleTheorem_Binomial : FermatLittleTheorem := by
  intro p a hp
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  suffices h : ∀ x : ZMod p, x ^ p = x from h _
  have h_nat : ∀ n : ℕ, (n : ZMod p) ^ p = n := by
    intro n
    induction n with
    | zero => simp [zero_pow hp.ne_zero]
    | succ k ih => rw [Nat.cast_succ, add_pow_expChar, ih, one_pow]
  intro x
  rw [← ZMod.natCast_zmod_val x]
  exact h_nat x.val
