import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0627

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2447. -/
theorem bounds_13_2447 : exactInterval 13 2447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2447 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2447) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2447 : oddCount 2447 13 = 6 ∧ acceleratedOrbit 13 2447 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2447 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2447) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2447.1, data_13_2447.2]

/-- Complete interval computation for depth 13, residue 2448. -/
theorem bounds_13_2448 : exactInterval 13 2448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2448 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2448) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2448 : oddCount 2448 13 = 5 ∧ acceleratedOrbit 13 2448 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2448 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2448) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2448.1, data_13_2448.2]

/-- Complete interval computation for depth 13, residue 2449. -/
theorem bounds_13_2449 : exactInterval 13 2449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2449 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2449) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2449 : oddCount 2449 13 = 5 ∧ acceleratedOrbit 13 2449 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2449 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2449) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2449.1, data_13_2449.2]

/-- Complete interval computation for depth 13, residue 2450. -/
theorem bounds_13_2450 : exactInterval 13 2450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2450 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2450) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2450 : oddCount 2450 13 = 5 ∧ acceleratedOrbit 13 2450 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2450 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2450) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2450.1, data_13_2450.2]

/-- Complete interval computation for depth 13, residue 2451. -/
theorem bounds_13_2451 : exactInterval 13 2451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2451 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2451) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2451 : oddCount 2451 13 = 5 ∧ acceleratedOrbit 13 2451 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2451 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2451) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2451.1, data_13_2451.2]

/-- Complete interval computation for depth 13, residue 2452. -/
theorem bounds_13_2452 : exactInterval 13 2452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2452 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2452) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2452 : oddCount 2452 13 = 5 ∧ acceleratedOrbit 13 2452 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2452 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2452) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2452.1, data_13_2452.2]

/-- Complete interval computation for depth 13, residue 2453. -/
theorem bounds_13_2453 : exactInterval 13 2453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2453 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2453) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2453 : oddCount 2453 13 = 5 ∧ acceleratedOrbit 13 2453 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2453 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2453) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2453.1, data_13_2453.2]

/-- Complete interval computation for depth 13, residue 2454. -/
theorem bounds_13_2454 : exactInterval 13 2454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2454 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2454) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2454 : oddCount 2454 13 = 5 ∧ acceleratedOrbit 13 2454 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2454 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2454) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2454.1, data_13_2454.2]

/-- Complete interval computation for depth 13, residue 2455. -/
theorem bounds_13_2455 : exactInterval 13 2455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2455 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2455) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2455 : oddCount 2455 13 = 5 ∧ acceleratedOrbit 13 2455 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2455 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2455) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2455.1, data_13_2455.2]

/-- Complete interval computation for depth 13, residue 2456. -/
theorem bounds_13_2456 : exactInterval 13 2456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2456 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2456) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2456 : oddCount 2456 13 = 5 ∧ acceleratedOrbit 13 2456 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2456 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2456) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2456.1, data_13_2456.2]

/-- Complete interval computation for depth 13, residue 2457. -/
theorem bounds_13_2457 : exactInterval 13 2457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2457 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2457) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2457 : oddCount 2457 13 = 5 ∧ acceleratedOrbit 13 2457 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2457 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2457) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2457.1, data_13_2457.2]

/-- Complete interval computation for depth 13, residue 2458. -/
theorem bounds_13_2458 : exactInterval 13 2458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2458 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2458) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2458 : oddCount 2458 13 = 5 ∧ acceleratedOrbit 13 2458 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2458 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2458) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2458.1, data_13_2458.2]

/-- Complete interval computation for depth 13, residue 2459. -/
theorem bounds_13_2459 : exactInterval 13 2459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2459 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2459) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2459 : oddCount 2459 13 = 10 ∧ acceleratedOrbit 13 2459 = 17738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2459 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2459) = 3 ^ 10 * m + 17738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2459.1, data_13_2459.2]

/-- Complete interval computation for depth 13, residue 2460. -/
theorem bounds_13_2460 : exactInterval 13 2460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2460 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2460) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2460 : oddCount 2460 13 = 7 ∧ acceleratedOrbit 13 2460 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2460 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2460) = 3 ^ 7 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2460.1, data_13_2460.2]

/-- Complete interval computation for depth 13, residue 2461. -/
theorem bounds_13_2461 : exactInterval 13 2461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2461 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2461) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2461 : oddCount 2461 13 = 7 ∧ acceleratedOrbit 13 2461 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2461 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2461) = 3 ^ 7 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2461.1, data_13_2461.2]

end Collatz.Research.StoppingAtlas.Batch0627
