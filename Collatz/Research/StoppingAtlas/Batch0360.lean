import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0360

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2442. -/
theorem bounds_12_2442 : exactInterval 12 2442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2442 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2442) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2442 : oddCount 2442 12 = 4 ∧ acceleratedOrbit 12 2442 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2442 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2442) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2442.1, data_12_2442.2]

/-- Complete interval computation for depth 12, residue 2443. -/
theorem bounds_12_2443 : exactInterval 12 2443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2443 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2443) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2443 : oddCount 2443 12 = 7 ∧ acceleratedOrbit 12 2443 = 1306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2443 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2443) = 3 ^ 7 * m + 1306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2443.1, data_12_2443.2]

/-- Complete interval computation for depth 12, residue 2444. -/
theorem bounds_12_2444 : exactInterval 12 2444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2444 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2444) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2444 : oddCount 2444 12 = 4 ∧ acceleratedOrbit 12 2444 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2444 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2444) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2444.1, data_12_2444.2]

/-- Complete interval computation for depth 12, residue 2445. -/
theorem bounds_12_2445 : exactInterval 12 2445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2445 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2445) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2445 : oddCount 2445 12 = 4 ∧ acceleratedOrbit 12 2445 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2445 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2445) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2445.1, data_12_2445.2]

/-- Complete interval computation for depth 12, residue 2446. -/
theorem bounds_12_2446 : exactInterval 12 2446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2446 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2446) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2446 : oddCount 2446 12 = 6 ∧ acceleratedOrbit 12 2446 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2446 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2446) = 3 ^ 6 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2446.1, data_12_2446.2]

/-- Complete interval computation for depth 12, residue 2447. -/
theorem bounds_12_2447 : exactInterval 12 2447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2447 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2447) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2447 : oddCount 2447 12 = 6 ∧ acceleratedOrbit 12 2447 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2447 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2447) = 3 ^ 6 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2447.1, data_12_2447.2]

/-- Complete interval computation for depth 12, residue 2448. -/
theorem bounds_12_2448 : exactInterval 12 2448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2448 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2448) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2448 : oddCount 2448 12 = 4 ∧ acceleratedOrbit 12 2448 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2448 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2448) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2448.1, data_12_2448.2]

/-- Complete interval computation for depth 12, residue 2449. -/
theorem bounds_12_2449 : exactInterval 12 2449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2449 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2449) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2449 : oddCount 2449 12 = 5 ∧ acceleratedOrbit 12 2449 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2449 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2449) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2449.1, data_12_2449.2]

/-- Complete interval computation for depth 12, residue 2450. -/
theorem bounds_12_2450 : exactInterval 12 2450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2450 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2450) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2450 : oddCount 2450 12 = 5 ∧ acceleratedOrbit 12 2450 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2450 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2450) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2450.1, data_12_2450.2]

/-- Complete interval computation for depth 12, residue 2451. -/
theorem bounds_12_2451 : exactInterval 12 2451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2451 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2451) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2451 : oddCount 2451 12 = 5 ∧ acceleratedOrbit 12 2451 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2451 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2451) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2451.1, data_12_2451.2]

/-- Complete interval computation for depth 12, residue 2452. -/
theorem bounds_12_2452 : exactInterval 12 2452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2452 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2452) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2452 : oddCount 2452 12 = 4 ∧ acceleratedOrbit 12 2452 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2452 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2452) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2452.1, data_12_2452.2]

/-- Complete interval computation for depth 12, residue 2453. -/
theorem bounds_12_2453 : exactInterval 12 2453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2453 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2453) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2453 : oddCount 2453 12 = 4 ∧ acceleratedOrbit 12 2453 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2453 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2453) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2453.1, data_12_2453.2]

/-- Complete interval computation for depth 12, residue 2454. -/
theorem bounds_12_2454 : exactInterval 12 2454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2454 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2454) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2454 : oddCount 2454 12 = 5 ∧ acceleratedOrbit 12 2454 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2454 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2454) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2454.1, data_12_2454.2]

/-- Complete interval computation for depth 12, residue 2455. -/
theorem bounds_12_2455 : exactInterval 12 2455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2455 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2455) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2455 : oddCount 2455 12 = 5 ∧ acceleratedOrbit 12 2455 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2455 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2455) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2455.1, data_12_2455.2]

/-- Complete interval computation for depth 12, residue 2456. -/
theorem bounds_12_2456 : exactInterval 12 2456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2456 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2456) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2456 : oddCount 2456 12 = 4 ∧ acceleratedOrbit 12 2456 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2456 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2456) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2456.1, data_12_2456.2]

end Collatz.Research.StoppingAtlas.Batch0360
