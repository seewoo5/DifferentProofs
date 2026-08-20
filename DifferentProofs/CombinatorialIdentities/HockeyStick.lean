module

public import DifferentProofs.CombinatorialIdentities.Defs

@[expose] public section

theorem HockeyStickIdentity_induction : HockeyStickIdentity := by
  rw [HockeyStickIdentity]
  intro n k
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, show n + 1 + k = n + k + 1 by ring,
      Nat.choose_succ_succ (n + k + 1)]  -- Nat.choose_succ_succ is Pascal's identity
    ring
