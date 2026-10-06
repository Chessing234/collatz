import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch090

/-- Complete interval computation for depth 9, residue 399. -/
theorem bounds_9_399 : exactInterval 9 399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_399 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 399) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_399 : oddCount 399 9 = 5 ∧ acceleratedOrbit 9 399 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_399 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 399) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_399.1, data_9_399.2]

/-- Complete interval computation for depth 9, residue 400. -/
theorem bounds_9_400 : exactInterval 9 400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_400 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 400) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_400 : oddCount 400 9 = 3 ∧ acceleratedOrbit 9 400 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_400 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 400) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_400.1, data_9_400.2]

/-- Complete interval computation for depth 9, residue 401. -/
theorem bounds_9_401 : exactInterval 9 401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_401 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 401) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_401 : oddCount 401 9 = 4 ∧ acceleratedOrbit 9 401 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_401 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 401) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_401.1, data_9_401.2]

/-- Complete interval computation for depth 9, residue 402. -/
theorem bounds_9_402 : exactInterval 9 402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_402 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 402) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_402 : oddCount 402 9 = 4 ∧ acceleratedOrbit 9 402 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_402 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 402) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_402.1, data_9_402.2]

/-- Complete interval computation for depth 9, residue 403. -/
theorem bounds_9_403 : exactInterval 9 403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_403 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 403) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_403 : oddCount 403 9 = 4 ∧ acceleratedOrbit 9 403 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_403 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 403) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_403.1, data_9_403.2]

/-- Complete interval computation for depth 9, residue 404. -/
theorem bounds_9_404 : exactInterval 9 404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_404 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 404) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_404 : oddCount 404 9 = 3 ∧ acceleratedOrbit 9 404 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_404 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 404) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_404.1, data_9_404.2]

/-- Complete interval computation for depth 9, residue 405. -/
theorem bounds_9_405 : exactInterval 9 405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_405 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 405) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_405 : oddCount 405 9 = 3 ∧ acceleratedOrbit 9 405 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_405 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 405) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_405.1, data_9_405.2]

/-- Complete interval computation for depth 9, residue 406. -/
theorem bounds_9_406 : exactInterval 9 406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_406 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 406) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_406 : oddCount 406 9 = 4 ∧ acceleratedOrbit 9 406 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_406 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 406) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_406.1, data_9_406.2]

/-- Complete interval computation for depth 9, residue 407. -/
theorem bounds_9_407 : exactInterval 9 407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_407 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 407) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_407 : oddCount 407 9 = 4 ∧ acceleratedOrbit 9 407 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_407 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 407) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_407.1, data_9_407.2]

/-- Complete interval computation for depth 9, residue 408. -/
theorem bounds_9_408 : exactInterval 9 408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_408 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 408) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_408 : oddCount 408 9 = 3 ∧ acceleratedOrbit 9 408 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_408 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 408) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_408.1, data_9_408.2]

end Collatz.Research.DescentIntervals.Batch090
