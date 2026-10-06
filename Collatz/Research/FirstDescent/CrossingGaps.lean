import Collatz.Research.DescentAtlas.Core

/-! Arithmetic gaps explain absent coefficient first-crossing times in the census.
These results exclude a coefficient crossing at these horizons, not eventual
integer descent. -/
namespace Collatz.Research.FirstDescent.CrossingGaps

/-- If consecutive powers of three straddle a binary interval, no power of
three lies in that interval. This applies uniformly to every odd-step count. -/
theorem no_power_between {lo hi A : Nat}
    (hl : 3 ^ A < lo) (hh : hi ≤ 3 ^ (A + 1)) :
    ∀ a : Nat, ¬ (lo ≤ 3 ^ a ∧ 3 ^ a < hi) := by
  intro a h
  by_cases ha : a ≤ A
  · have hp : 3 ^ a ≤ 3 ^ A := Nat.pow_le_pow_right (by decide) ha
    omega
  · have hp : 3 ^ (A + 1) ≤ 3 ^ a := Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-- No coefficient first crossing can use the binary interval at time 3. -/
theorem gap_3 : ∀ a : Nat, ¬ (2 ^ 2 ≤ 3 ^ a ∧ 3 ^ a < 2 ^ 3) := by
  exact no_power_between (A := 1) (by decide) (by decide)

/-- No coefficient first crossing can use the binary interval at time 6. -/
theorem gap_6 : ∀ a : Nat, ¬ (2 ^ 5 ≤ 3 ^ a ∧ 3 ^ a < 2 ^ 6) := by
  exact no_power_between (A := 3) (by decide) (by decide)

/-- No coefficient first crossing can use the binary interval at time 9. -/
theorem gap_9 : ∀ a : Nat, ¬ (2 ^ 8 ≤ 3 ^ a ∧ 3 ^ a < 2 ^ 9) := by
  exact no_power_between (A := 5) (by decide) (by decide)

/-- No coefficient first crossing can use the binary interval at time 11. -/
theorem gap_11 : ∀ a : Nat, ¬ (2 ^ 10 ≤ 3 ^ a ∧ 3 ^ a < 2 ^ 11) := by
  exact no_power_between (A := 6) (by decide) (by decide)

/-- No coefficient first crossing can use the binary interval at time 14. -/
theorem gap_14 : ∀ a : Nat, ¬ (2 ^ 13 ≤ 3 ^ a ∧ 3 ^ a < 2 ^ 14) := by
  exact no_power_between (A := 8) (by decide) (by decide)

/-- No coefficient first crossing can use the binary interval at time 17. -/
theorem gap_17 : ∀ a : Nat, ¬ (2 ^ 16 ≤ 3 ^ a ∧ 3 ^ a < 2 ^ 17) := by
  exact no_power_between (A := 10) (by decide) (by decide)

/-- No coefficient first crossing can use the binary interval at time 19. -/
theorem gap_19 : ∀ a : Nat, ¬ (2 ^ 18 ≤ 3 ^ a ∧ 3 ^ a < 2 ^ 19) := by
  exact no_power_between (A := 11) (by decide) (by decide)

end Collatz.Research.FirstDescent.CrossingGaps
