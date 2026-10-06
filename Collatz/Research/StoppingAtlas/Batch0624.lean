import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0624

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2401. -/
theorem bounds_13_2401 : exactInterval 13 2401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2401 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2401) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2401 : oddCount 2401 13 = 9 ∧ acceleratedOrbit 13 2401 = 5777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2401 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2401) = 3 ^ 9 * m + 5777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2401.1, data_13_2401.2]

/-- Complete interval computation for depth 13, residue 2402. -/
theorem bounds_13_2402 : exactInterval 13 2402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2402 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2402) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2402 : oddCount 2402 13 = 7 ∧ acceleratedOrbit 13 2402 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2402 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2402) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2402.1, data_13_2402.2]

/-- Complete interval computation for depth 13, residue 2403. -/
theorem bounds_13_2403 : exactInterval 13 2403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2403 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2403) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2403 : oddCount 2403 13 = 7 ∧ acceleratedOrbit 13 2403 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2403 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2403) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2403.1, data_13_2403.2]

/-- Complete interval computation for depth 13, residue 2404. -/
theorem bounds_13_2404 : exactInterval 13 2404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2404 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2404) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2404 : oddCount 2404 13 = 7 ∧ acceleratedOrbit 13 2404 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2404 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2404) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2404.1, data_13_2404.2]

/-- Complete interval computation for depth 13, residue 2405. -/
theorem bounds_13_2405 : exactInterval 13 2405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2405 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2405) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2405 : oddCount 2405 13 = 7 ∧ acceleratedOrbit 13 2405 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2405 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2405) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2405.1, data_13_2405.2]

/-- Complete interval computation for depth 13, residue 2406. -/
theorem bounds_13_2406 : exactInterval 13 2406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2406 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2406) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2406 : oddCount 2406 13 = 7 ∧ acceleratedOrbit 13 2406 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2406 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2406) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2406.1, data_13_2406.2]

/-- Complete interval computation for depth 13, residue 2407. -/
theorem bounds_13_2407 : exactInterval 13 2407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2407 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2407) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2407 : oddCount 2407 13 = 10 ∧ acceleratedOrbit 13 2407 = 17360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2407 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2407) = 3 ^ 10 * m + 17360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2407.1, data_13_2407.2]

/-- Complete interval computation for depth 13, residue 2408. -/
theorem bounds_13_2408 : exactInterval 13 2408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2408 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2408) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2408 : oddCount 2408 13 = 3 ∧ acceleratedOrbit 13 2408 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2408 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2408) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2408.1, data_13_2408.2]

/-- Complete interval computation for depth 13, residue 2409. -/
theorem bounds_13_2409 : exactInterval 13 2409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2409 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2409) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2409 : oddCount 2409 13 = 6 ∧ acceleratedOrbit 13 2409 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2409 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2409) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2409.1, data_13_2409.2]

/-- Complete interval computation for depth 13, residue 2410. -/
theorem bounds_13_2410 : exactInterval 13 2410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2410 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2410) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2410 : oddCount 2410 13 = 3 ∧ acceleratedOrbit 13 2410 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2410 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2410) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2410.1, data_13_2410.2]

/-- Complete interval computation for depth 13, residue 2411. -/
theorem bounds_13_2411 : exactInterval 13 2411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2411 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2411) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2411 : oddCount 2411 13 = 8 ∧ acceleratedOrbit 13 2411 = 1934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2411 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2411) = 3 ^ 8 * m + 1934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2411.1, data_13_2411.2]

/-- Complete interval computation for depth 13, residue 2412. -/
theorem bounds_13_2412 : exactInterval 13 2412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2412 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2412) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2412 : oddCount 2412 13 = 8 ∧ acceleratedOrbit 13 2412 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2412 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2412) = 3 ^ 8 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2412.1, data_13_2412.2]

/-- Complete interval computation for depth 13, residue 2413. -/
theorem bounds_13_2413 : exactInterval 13 2413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2413 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2413) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2413 : oddCount 2413 13 = 8 ∧ acceleratedOrbit 13 2413 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2413 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2413) = 3 ^ 8 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2413.1, data_13_2413.2]

/-- Complete interval computation for depth 13, residue 2414. -/
theorem bounds_13_2414 : exactInterval 13 2414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2414 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2414) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2414 : oddCount 2414 13 = 8 ∧ acceleratedOrbit 13 2414 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2414 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2414) = 3 ^ 8 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2414.1, data_13_2414.2]

/-- Complete interval computation for depth 13, residue 2415. -/
theorem bounds_13_2415 : exactInterval 13 2415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2415 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2415) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2415 : oddCount 2415 13 = 6 ∧ acceleratedOrbit 13 2415 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2415 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2415) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2415.1, data_13_2415.2]

end Collatz.Research.StoppingAtlas.Batch0624
