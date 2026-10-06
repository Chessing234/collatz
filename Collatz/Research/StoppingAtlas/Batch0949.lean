import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0949

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7393. -/
theorem bounds_13_7393 : exactInterval 13 7393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7393 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7393) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7393 : oddCount 7393 13 = 8 ∧ acceleratedOrbit 13 7393 = 5923 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7393 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7393) = 3 ^ 8 * m + 5923 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7393.1, data_13_7393.2]

/-- Complete interval computation for depth 13, residue 7394. -/
theorem bounds_13_7394 : exactInterval 13 7394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7394 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7394) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7394 : oddCount 7394 13 = 4 ∧ acceleratedOrbit 13 7394 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7394 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7394) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7394.1, data_13_7394.2]

/-- Complete interval computation for depth 13, residue 7395. -/
theorem bounds_13_7395 : exactInterval 13 7395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7395 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7395) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7395 : oddCount 7395 13 = 4 ∧ acceleratedOrbit 13 7395 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7395 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7395) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7395.1, data_13_7395.2]

/-- Complete interval computation for depth 13, residue 7396. -/
theorem bounds_13_7396 : exactInterval 13 7396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7396 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7396) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7396 : oddCount 7396 13 = 6 ∧ acceleratedOrbit 13 7396 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7396 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7396) = 3 ^ 6 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7396.1, data_13_7396.2]

/-- Complete interval computation for depth 13, residue 7397. -/
theorem bounds_13_7397 : exactInterval 13 7397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7397 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7397) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7397 : oddCount 7397 13 = 6 ∧ acceleratedOrbit 13 7397 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7397 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7397) = 3 ^ 6 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7397.1, data_13_7397.2]

/-- Complete interval computation for depth 13, residue 7398. -/
theorem bounds_13_7398 : exactInterval 13 7398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7398 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7398) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7398 : oddCount 7398 13 = 6 ∧ acceleratedOrbit 13 7398 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7398 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7398) = 3 ^ 6 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7398.1, data_13_7398.2]

/-- Complete interval computation for depth 13, residue 7399. -/
theorem bounds_13_7399 : exactInterval 13 7399 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7399 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7399) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7399 : oddCount 7399 13 = 8 ∧ acceleratedOrbit 13 7399 = 5927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7399 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7399) = 3 ^ 8 * m + 5927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7399.1, data_13_7399.2]

/-- Complete interval computation for depth 13, residue 7400. -/
theorem bounds_13_7400 : exactInterval 13 7400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7400 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7400) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7400 : oddCount 7400 13 = 6 ∧ acceleratedOrbit 13 7400 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7400 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7400) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7400.1, data_13_7400.2]

/-- Complete interval computation for depth 13, residue 7401. -/
theorem bounds_13_7401 : exactInterval 13 7401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7401 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7401) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7401 : oddCount 7401 13 = 8 ∧ acceleratedOrbit 13 7401 = 5930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7401 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7401) = 3 ^ 8 * m + 5930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7401.1, data_13_7401.2]

/-- Complete interval computation for depth 13, residue 7402. -/
theorem bounds_13_7402 : exactInterval 13 7402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7402 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7402) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7402 : oddCount 7402 13 = 6 ∧ acceleratedOrbit 13 7402 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7402 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7402) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7402.1, data_13_7402.2]

/-- Complete interval computation for depth 13, residue 7403. -/
theorem bounds_13_7403 : exactInterval 13 7403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7403 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7403) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7403 : oddCount 7403 13 = 10 ∧ acceleratedOrbit 13 7403 = 53378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7403 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7403) = 3 ^ 10 * m + 53378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7403.1, data_13_7403.2]

/-- Complete interval computation for depth 13, residue 7404. -/
theorem bounds_13_7404 : exactInterval 13 7404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7404 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7404) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7404 : oddCount 7404 13 = 5 ∧ acceleratedOrbit 13 7404 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7404 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7404) = 3 ^ 5 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7404.1, data_13_7404.2]

/-- Complete interval computation for depth 13, residue 7405. -/
theorem bounds_13_7405 : exactInterval 13 7405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7405 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7405) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7405 : oddCount 7405 13 = 5 ∧ acceleratedOrbit 13 7405 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7405 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7405) = 3 ^ 5 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7405.1, data_13_7405.2]

/-- Complete interval computation for depth 13, residue 7406. -/
theorem bounds_13_7406 : exactInterval 13 7406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7406 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7406) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7406 : oddCount 7406 13 = 5 ∧ acceleratedOrbit 13 7406 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7406 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7406) = 3 ^ 5 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7406.1, data_13_7406.2]

/-- Complete interval computation for depth 13, residue 7407. -/
theorem bounds_13_7407 : exactInterval 13 7407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7407 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7407) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7407 : oddCount 7407 13 = 10 ∧ acceleratedOrbit 13 7407 = 53399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7407 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7407) = 3 ^ 10 * m + 53399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7407.1, data_13_7407.2]

end Collatz.Research.StoppingAtlas.Batch0949
