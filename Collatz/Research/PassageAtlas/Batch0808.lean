import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0808

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26443. -/
theorem bounds_15_26443 : exactInterval 15 26443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26443 : oddCount 26443 15 = 6 ∧ acceleratedOrbit 15 26443 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26443) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26443.1, data_15_26443.2]

/-- Complete interval computation for depth 15, residue 26444. -/
theorem bounds_15_26444 : exactInterval 15 26444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26444 : oddCount 26444 15 = 7 ∧ acceleratedOrbit 15 26444 = 1766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26444) = 3 ^ 7 * m + 1766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26444.1, data_15_26444.2]

/-- Complete interval computation for depth 15, residue 26445. -/
theorem bounds_15_26445 : exactInterval 15 26445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26445 : oddCount 26445 15 = 7 ∧ acceleratedOrbit 15 26445 = 1766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26445) = 3 ^ 7 * m + 1766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26445.1, data_15_26445.2]

/-- Complete interval computation for depth 15, residue 26446. -/
theorem bounds_15_26446 : exactInterval 15 26446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26446 : oddCount 26446 15 = 8 ∧ acceleratedOrbit 15 26446 = 5296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26446) = 3 ^ 8 * m + 5296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26446.1, data_15_26446.2]

/-- Complete interval computation for depth 15, residue 26447. -/
theorem bounds_15_26447 : exactInterval 15 26447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26447 : oddCount 26447 15 = 8 ∧ acceleratedOrbit 15 26447 = 5296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26447) = 3 ^ 8 * m + 5296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26447.1, data_15_26447.2]

/-- Complete interval computation for depth 15, residue 26448. -/
theorem bounds_15_26448 : exactInterval 15 26448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26448 : oddCount 26448 15 = 6 ∧ acceleratedOrbit 15 26448 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26448) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26448.1, data_15_26448.2]

/-- Complete interval computation for depth 15, residue 26449. -/
theorem bounds_15_26449 : exactInterval 15 26449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26449 : oddCount 26449 15 = 7 ∧ acceleratedOrbit 15 26449 = 1766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26449) = 3 ^ 7 * m + 1766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26449.1, data_15_26449.2]

/-- Complete interval computation for depth 15, residue 26450. -/
theorem bounds_15_26450 : exactInterval 15 26450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26450 : oddCount 26450 15 = 9 ∧ acceleratedOrbit 15 26450 = 15890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26450) = 3 ^ 9 * m + 15890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26450.1, data_15_26450.2]

/-- Complete interval computation for depth 15, residue 26451. -/
theorem bounds_15_26451 : exactInterval 15 26451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26451 : oddCount 26451 15 = 9 ∧ acceleratedOrbit 15 26451 = 15890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26451) = 3 ^ 9 * m + 15890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26451.1, data_15_26451.2]

/-- Complete interval computation for depth 15, residue 26452. -/
theorem bounds_15_26452 : exactInterval 15 26452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26452 : oddCount 26452 15 = 6 ∧ acceleratedOrbit 15 26452 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26452) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26452.1, data_15_26452.2]

/-- Complete interval computation for depth 15, residue 26453. -/
theorem bounds_15_26453 : exactInterval 15 26453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26453 : oddCount 26453 15 = 6 ∧ acceleratedOrbit 15 26453 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26453) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26453.1, data_15_26453.2]

/-- Complete interval computation for depth 15, residue 26454. -/
theorem bounds_15_26454 : exactInterval 15 26454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26454 : oddCount 26454 15 = 7 ∧ acceleratedOrbit 15 26454 = 1766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26454) = 3 ^ 7 * m + 1766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26454.1, data_15_26454.2]

/-- Complete interval computation for depth 15, residue 26455. -/
theorem bounds_15_26455 : exactInterval 15 26455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26455 : oddCount 26455 15 = 7 ∧ acceleratedOrbit 15 26455 = 1766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26455) = 3 ^ 7 * m + 1766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26455.1, data_15_26455.2]

/-- Complete interval computation for depth 15, residue 26456. -/
theorem bounds_15_26456 : exactInterval 15 26456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26456 : oddCount 26456 15 = 9 ∧ acceleratedOrbit 15 26456 = 15902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26456) = 3 ^ 9 * m + 15902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26456.1, data_15_26456.2]

/-- Complete interval computation for depth 15, residue 26457. -/
theorem bounds_15_26457 : exactInterval 15 26457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26457 : oddCount 26457 15 = 6 ∧ acceleratedOrbit 15 26457 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26457) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26457.1, data_15_26457.2]

/-- Complete interval computation for depth 15, residue 26458. -/
theorem bounds_15_26458 : exactInterval 15 26458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26458 : oddCount 26458 15 = 9 ∧ acceleratedOrbit 15 26458 = 15902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26458) = 3 ^ 9 * m + 15902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26458.1, data_15_26458.2]

/-- Complete interval computation for depth 15, residue 26459. -/
theorem bounds_15_26459 : exactInterval 15 26459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26459 : oddCount 26459 15 = 10 ∧ acceleratedOrbit 15 26459 = 47684 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26459) = 3 ^ 10 * m + 47684 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26459.1, data_15_26459.2]

/-- Complete interval computation for depth 15, residue 26460. -/
theorem bounds_15_26460 : exactInterval 15 26460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26460 : oddCount 26460 15 = 9 ∧ acceleratedOrbit 15 26460 = 15902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26460) = 3 ^ 9 * m + 15902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26460.1, data_15_26460.2]

/-- Complete interval computation for depth 15, residue 26461. -/
theorem bounds_15_26461 : exactInterval 15 26461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26461 : oddCount 26461 15 = 9 ∧ acceleratedOrbit 15 26461 = 15902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26461) = 3 ^ 9 * m + 15902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26461.1, data_15_26461.2]

/-- Complete interval computation for depth 15, residue 26462. -/
theorem bounds_15_26462 : exactInterval 15 26462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26462 : oddCount 26462 15 = 6 ∧ acceleratedOrbit 15 26462 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26462) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26462.1, data_15_26462.2]

/-- Complete interval computation for depth 15, residue 26463. -/
theorem bounds_15_26463 : exactInterval 15 26463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26463 : oddCount 26463 15 = 6 ∧ acceleratedOrbit 15 26463 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26463) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26463.1, data_15_26463.2]

/-- Complete interval computation for depth 15, residue 26464. -/
theorem bounds_15_26464 : exactInterval 15 26464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26464 : oddCount 26464 15 = 5 ∧ acceleratedOrbit 15 26464 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26464) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26464.1, data_15_26464.2]

/-- Complete interval computation for depth 15, residue 26465. -/
theorem bounds_15_26465 : exactInterval 15 26465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26465 : oddCount 26465 15 = 8 ∧ acceleratedOrbit 15 26465 = 5300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26465) = 3 ^ 8 * m + 5300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26465.1, data_15_26465.2]

/-- Complete interval computation for depth 15, residue 26466. -/
theorem bounds_15_26466 : exactInterval 15 26466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26466 : oddCount 26466 15 = 5 ∧ acceleratedOrbit 15 26466 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26466) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26466.1, data_15_26466.2]

/-- Complete interval computation for depth 15, residue 26467. -/
theorem bounds_15_26467 : exactInterval 15 26467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26467 : oddCount 26467 15 = 5 ∧ acceleratedOrbit 15 26467 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26467) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26467.1, data_15_26467.2]

/-- Complete interval computation for depth 15, residue 26468. -/
theorem bounds_15_26468 : exactInterval 15 26468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26468 : oddCount 26468 15 = 5 ∧ acceleratedOrbit 15 26468 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26468) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26468.1, data_15_26468.2]

/-- Complete interval computation for depth 15, residue 26469. -/
theorem bounds_15_26469 : exactInterval 15 26469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26469 : oddCount 26469 15 = 5 ∧ acceleratedOrbit 15 26469 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26469) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26469.1, data_15_26469.2]

/-- Complete interval computation for depth 15, residue 26470. -/
theorem bounds_15_26470 : exactInterval 15 26470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26470 : oddCount 26470 15 = 5 ∧ acceleratedOrbit 15 26470 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26470) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26470.1, data_15_26470.2]

/-- Complete interval computation for depth 15, residue 26471. -/
theorem bounds_15_26471 : exactInterval 15 26471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26471 : oddCount 26471 15 = 13 ∧ acceleratedOrbit 15 26471 = 1288007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26471) = 3 ^ 13 * m + 1288007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26471.1, data_15_26471.2]

/-- Complete interval computation for depth 15, residue 26472. -/
theorem bounds_15_26472 : exactInterval 15 26472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26472 : oddCount 26472 15 = 5 ∧ acceleratedOrbit 15 26472 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26472) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26472.1, data_15_26472.2]

/-- Complete interval computation for depth 15, residue 26473. -/
theorem bounds_15_26473 : exactInterval 15 26473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26473 : oddCount 26473 15 = 6 ∧ acceleratedOrbit 15 26473 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26473) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26473.1, data_15_26473.2]

/-- Complete interval computation for depth 15, residue 26474. -/
theorem bounds_15_26474 : exactInterval 15 26474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26474 : oddCount 26474 15 = 5 ∧ acceleratedOrbit 15 26474 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26474) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26474.1, data_15_26474.2]

/-- Complete interval computation for depth 15, residue 26475. -/
theorem bounds_15_26475 : exactInterval 15 26475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26475 : oddCount 26475 15 = 8 ∧ acceleratedOrbit 15 26475 = 5302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26475) = 3 ^ 8 * m + 5302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26475.1, data_15_26475.2]

end Collatz.Research.PassageAtlas.Batch0808
