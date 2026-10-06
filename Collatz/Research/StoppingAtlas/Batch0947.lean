import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0947

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7362. -/
theorem bounds_13_7362 : exactInterval 13 7362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7362 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7362) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7362 : oddCount 7362 13 = 6 ∧ acceleratedOrbit 13 7362 = 656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7362 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7362) = 3 ^ 6 * m + 656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7362.1, data_13_7362.2]

/-- Complete interval computation for depth 13, residue 7363. -/
theorem bounds_13_7363 : exactInterval 13 7363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7363 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7363) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7363 : oddCount 7363 13 = 6 ∧ acceleratedOrbit 13 7363 = 656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7363 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7363) = 3 ^ 6 * m + 656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7363.1, data_13_7363.2]

/-- Complete interval computation for depth 13, residue 7364. -/
theorem bounds_13_7364 : exactInterval 13 7364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7364 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7364) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7364 : oddCount 7364 13 = 4 ∧ acceleratedOrbit 13 7364 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7364 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7364) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7364.1, data_13_7364.2]

/-- Complete interval computation for depth 13, residue 7365. -/
theorem bounds_13_7365 : exactInterval 13 7365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7365 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7365) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7365 : oddCount 7365 13 = 4 ∧ acceleratedOrbit 13 7365 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7365 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7365) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7365.1, data_13_7365.2]

/-- Complete interval computation for depth 13, residue 7366. -/
theorem bounds_13_7366 : exactInterval 13 7366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7366 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7366) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7366 : oddCount 7366 13 = 4 ∧ acceleratedOrbit 13 7366 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7366 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7366) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7366.1, data_13_7366.2]

/-- Complete interval computation for depth 13, residue 7367. -/
theorem bounds_13_7367 : exactInterval 13 7367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7367 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7367) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7367 : oddCount 7367 13 = 8 ∧ acceleratedOrbit 13 7367 = 5903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7367 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7367) = 3 ^ 8 * m + 5903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7367.1, data_13_7367.2]

/-- Complete interval computation for depth 13, residue 7368. -/
theorem bounds_13_7368 : exactInterval 13 7368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7368 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7368) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7368 : oddCount 7368 13 = 4 ∧ acceleratedOrbit 13 7368 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7368 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7368) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7368.1, data_13_7368.2]

/-- Complete interval computation for depth 13, residue 7369. -/
theorem bounds_13_7369 : exactInterval 13 7369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7369 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7369) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7369 : oddCount 7369 13 = 7 ∧ acceleratedOrbit 13 7369 = 1970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7369 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7369) = 3 ^ 7 * m + 1970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7369.1, data_13_7369.2]

/-- Complete interval computation for depth 13, residue 7370. -/
theorem bounds_13_7370 : exactInterval 13 7370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7370 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7370) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7370 : oddCount 7370 13 = 4 ∧ acceleratedOrbit 13 7370 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7370 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7370) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7370.1, data_13_7370.2]

/-- Complete interval computation for depth 13, residue 7371. -/
theorem bounds_13_7371 : exactInterval 13 7371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7371 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7371) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7371 : oddCount 7371 13 = 7 ∧ acceleratedOrbit 13 7371 = 1970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7371 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7371) = 3 ^ 7 * m + 1970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7371.1, data_13_7371.2]

/-- Complete interval computation for depth 13, residue 7372. -/
theorem bounds_13_7372 : exactInterval 13 7372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7372 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7372) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7372 : oddCount 7372 13 = 4 ∧ acceleratedOrbit 13 7372 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7372 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7372) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7372.1, data_13_7372.2]

/-- Complete interval computation for depth 13, residue 7373. -/
theorem bounds_13_7373 : exactInterval 13 7373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7373 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7373) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7373 : oddCount 7373 13 = 4 ∧ acceleratedOrbit 13 7373 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7373 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7373) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7373.1, data_13_7373.2]

/-- Complete interval computation for depth 13, residue 7374. -/
theorem bounds_13_7374 : exactInterval 13 7374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7374 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7374) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7374 : oddCount 7374 13 = 8 ∧ acceleratedOrbit 13 7374 = 5908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7374 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7374) = 3 ^ 8 * m + 5908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7374.1, data_13_7374.2]

/-- Complete interval computation for depth 13, residue 7375. -/
theorem bounds_13_7375 : exactInterval 13 7375 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7375 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7375) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7375 : oddCount 7375 13 = 8 ∧ acceleratedOrbit 13 7375 = 5908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7375 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7375) = 3 ^ 8 * m + 5908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7375.1, data_13_7375.2]

/-- Complete interval computation for depth 13, residue 7376. -/
theorem bounds_13_7376 : exactInterval 13 7376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7376 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7376) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7376 : oddCount 7376 13 = 4 ∧ acceleratedOrbit 13 7376 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7376 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7376) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7376.1, data_13_7376.2]

end Collatz.Research.StoppingAtlas.Batch0947
