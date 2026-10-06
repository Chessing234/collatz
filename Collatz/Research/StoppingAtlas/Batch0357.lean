import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0357

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2396. -/
theorem bounds_12_2396 : exactInterval 12 2396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2396 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2396) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2396 : oddCount 2396 12 = 5 ∧ acceleratedOrbit 12 2396 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2396 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2396) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2396.1, data_12_2396.2]

/-- Complete interval computation for depth 12, residue 2397. -/
theorem bounds_12_2397 : exactInterval 12 2397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2397 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2397) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2397 : oddCount 2397 12 = 5 ∧ acceleratedOrbit 12 2397 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2397 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2397) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2397.1, data_12_2397.2]

/-- Complete interval computation for depth 12, residue 2398. -/
theorem bounds_12_2398 : exactInterval 12 2398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2398 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2398) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2398 : oddCount 2398 12 = 7 ∧ acceleratedOrbit 12 2398 = 1282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2398 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2398) = 3 ^ 7 * m + 1282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2398.1, data_12_2398.2]

/-- Complete interval computation for depth 12, residue 2399. -/
theorem bounds_12_2399 : exactInterval 12 2399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2399 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2399) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2399 : oddCount 2399 12 = 7 ∧ acceleratedOrbit 12 2399 = 1282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2399 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2399) = 3 ^ 7 * m + 1282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2399.1, data_12_2399.2]

/-- Complete interval computation for depth 12, residue 2400. -/
theorem bounds_12_2400 : exactInterval 12 2400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2400 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2400) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2400 : oddCount 2400 12 = 3 ∧ acceleratedOrbit 12 2400 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2400 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2400) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2400.1, data_12_2400.2]

/-- Complete interval computation for depth 12, residue 2401. -/
theorem bounds_12_2401 : exactInterval 12 2401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2401 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2401) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2401 : oddCount 2401 12 = 8 ∧ acceleratedOrbit 12 2401 = 3851 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2401 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2401) = 3 ^ 8 * m + 3851 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2401.1, data_12_2401.2]

/-- Complete interval computation for depth 12, residue 2402. -/
theorem bounds_12_2402 : exactInterval 12 2402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2402 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2402) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2402 : oddCount 2402 12 = 6 ∧ acceleratedOrbit 12 2402 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2402 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2402) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2402.1, data_12_2402.2]

/-- Complete interval computation for depth 12, residue 2403. -/
theorem bounds_12_2403 : exactInterval 12 2403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2403 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2403) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2403 : oddCount 2403 12 = 6 ∧ acceleratedOrbit 12 2403 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2403 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2403) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2403.1, data_12_2403.2]

/-- Complete interval computation for depth 12, residue 2404. -/
theorem bounds_12_2404 : exactInterval 12 2404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2404 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2404) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2404 : oddCount 2404 12 = 6 ∧ acceleratedOrbit 12 2404 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2404 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2404) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2404.1, data_12_2404.2]

/-- Complete interval computation for depth 12, residue 2405. -/
theorem bounds_12_2405 : exactInterval 12 2405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2405 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2405) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2405 : oddCount 2405 12 = 6 ∧ acceleratedOrbit 12 2405 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2405 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2405) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2405.1, data_12_2405.2]

/-- Complete interval computation for depth 12, residue 2406. -/
theorem bounds_12_2406 : exactInterval 12 2406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2406 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2406) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2406 : oddCount 2406 12 = 6 ∧ acceleratedOrbit 12 2406 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2406 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2406) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2406.1, data_12_2406.2]

/-- Complete interval computation for depth 12, residue 2407. -/
theorem bounds_12_2407 : exactInterval 12 2407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2407 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2407) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2407 : oddCount 2407 12 = 9 ∧ acceleratedOrbit 12 2407 = 11573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2407 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2407) = 3 ^ 9 * m + 11573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2407.1, data_12_2407.2]

/-- Complete interval computation for depth 12, residue 2408. -/
theorem bounds_12_2408 : exactInterval 12 2408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2408 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2408) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2408 : oddCount 2408 12 = 3 ∧ acceleratedOrbit 12 2408 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2408 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2408) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2408.1, data_12_2408.2]

/-- Complete interval computation for depth 12, residue 2409. -/
theorem bounds_12_2409 : exactInterval 12 2409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2409 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2409) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2409 : oddCount 2409 12 = 5 ∧ acceleratedOrbit 12 2409 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2409 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2409) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2409.1, data_12_2409.2]

/-- Complete interval computation for depth 12, residue 2410. -/
theorem bounds_12_2410 : exactInterval 12 2410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2410 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2410) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2410 : oddCount 2410 12 = 3 ∧ acceleratedOrbit 12 2410 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2410 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2410) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2410.1, data_12_2410.2]

end Collatz.Research.StoppingAtlas.Batch0357
