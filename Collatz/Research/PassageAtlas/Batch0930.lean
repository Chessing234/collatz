import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0930

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30441. -/
theorem bounds_15_30441 : exactInterval 15 30441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30441 : oddCount 30441 15 = 9 ∧ acceleratedOrbit 15 30441 = 18287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30441) = 3 ^ 9 * m + 18287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30441.1, data_15_30441.2]

/-- Complete interval computation for depth 15, residue 30442. -/
theorem bounds_15_30442 : exactInterval 15 30442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30442 : oddCount 30442 15 = 5 ∧ acceleratedOrbit 15 30442 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30442) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30442.1, data_15_30442.2]

/-- Complete interval computation for depth 15, residue 30443. -/
theorem bounds_15_30443 : exactInterval 15 30443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30443 : oddCount 30443 15 = 7 ∧ acceleratedOrbit 15 30443 = 2032 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30443) = 3 ^ 7 * m + 2032 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30443.1, data_15_30443.2]

/-- Complete interval computation for depth 15, residue 30444. -/
theorem bounds_15_30444 : exactInterval 15 30444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30444 : oddCount 30444 15 = 7 ∧ acceleratedOrbit 15 30444 = 2033 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30444) = 3 ^ 7 * m + 2033 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30444.1, data_15_30444.2]

/-- Complete interval computation for depth 15, residue 30445. -/
theorem bounds_15_30445 : exactInterval 15 30445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30445 : oddCount 30445 15 = 7 ∧ acceleratedOrbit 15 30445 = 2033 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30445) = 3 ^ 7 * m + 2033 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30445.1, data_15_30445.2]

/-- Complete interval computation for depth 15, residue 30446. -/
theorem bounds_15_30446 : exactInterval 15 30446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30446 : oddCount 30446 15 = 7 ∧ acceleratedOrbit 15 30446 = 2033 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30446) = 3 ^ 7 * m + 2033 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30446.1, data_15_30446.2]

/-- Complete interval computation for depth 15, residue 30447. -/
theorem bounds_15_30447 : exactInterval 15 30447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30447 : oddCount 30447 15 = 9 ∧ acceleratedOrbit 15 30447 = 18290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30447) = 3 ^ 9 * m + 18290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30447.1, data_15_30447.2]

/-- Complete interval computation for depth 15, residue 30448. -/
theorem bounds_15_30448 : exactInterval 15 30448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30448 : oddCount 30448 15 = 8 ∧ acceleratedOrbit 15 30448 = 6101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30448) = 3 ^ 8 * m + 6101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30448.1, data_15_30448.2]

/-- Complete interval computation for depth 15, residue 30449. -/
theorem bounds_15_30449 : exactInterval 15 30449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30449 : oddCount 30449 15 = 5 ∧ acceleratedOrbit 15 30449 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30449) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30449.1, data_15_30449.2]

/-- Complete interval computation for depth 15, residue 30450. -/
theorem bounds_15_30450 : exactInterval 15 30450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30450 : oddCount 30450 15 = 10 ∧ acceleratedOrbit 15 30450 = 54881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30450) = 3 ^ 10 * m + 54881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30450.1, data_15_30450.2]

/-- Complete interval computation for depth 15, residue 30451. -/
theorem bounds_15_30451 : exactInterval 15 30451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30451 : oddCount 30451 15 = 10 ∧ acceleratedOrbit 15 30451 = 54881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30451) = 3 ^ 10 * m + 54881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30451.1, data_15_30451.2]

/-- Complete interval computation for depth 15, residue 30452. -/
theorem bounds_15_30452 : exactInterval 15 30452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30452 : oddCount 30452 15 = 8 ∧ acceleratedOrbit 15 30452 = 6101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30452) = 3 ^ 8 * m + 6101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30452.1, data_15_30452.2]

/-- Complete interval computation for depth 15, residue 30453. -/
theorem bounds_15_30453 : exactInterval 15 30453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30453 : oddCount 30453 15 = 8 ∧ acceleratedOrbit 15 30453 = 6101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30453) = 3 ^ 8 * m + 6101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30453.1, data_15_30453.2]

/-- Complete interval computation for depth 15, residue 30454. -/
theorem bounds_15_30454 : exactInterval 15 30454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30454 : oddCount 30454 15 = 9 ∧ acceleratedOrbit 15 30454 = 18296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30454) = 3 ^ 9 * m + 18296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30454.1, data_15_30454.2]

/-- Complete interval computation for depth 15, residue 30455. -/
theorem bounds_15_30455 : exactInterval 15 30455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30455 : oddCount 30455 15 = 9 ∧ acceleratedOrbit 15 30455 = 18296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30455) = 3 ^ 9 * m + 18296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30455.1, data_15_30455.2]

/-- Complete interval computation for depth 15, residue 30456. -/
theorem bounds_15_30456 : exactInterval 15 30456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30456 : oddCount 30456 15 = 8 ∧ acceleratedOrbit 15 30456 = 6101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30456) = 3 ^ 8 * m + 6101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30456.1, data_15_30456.2]

/-- Complete interval computation for depth 15, residue 30457. -/
theorem bounds_15_30457 : exactInterval 15 30457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30457 : oddCount 30457 15 = 8 ∧ acceleratedOrbit 15 30457 = 6101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30457) = 3 ^ 8 * m + 6101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30457.1, data_15_30457.2]

/-- Complete interval computation for depth 15, residue 30458. -/
theorem bounds_15_30458 : exactInterval 15 30458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30458 : oddCount 30458 15 = 8 ∧ acceleratedOrbit 15 30458 = 6101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30458) = 3 ^ 8 * m + 6101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30458.1, data_15_30458.2]

/-- Complete interval computation for depth 15, residue 30459. -/
theorem bounds_15_30459 : exactInterval 15 30459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30459 : oddCount 30459 15 = 7 ∧ acceleratedOrbit 15 30459 = 2033 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30459) = 3 ^ 7 * m + 2033 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30459.1, data_15_30459.2]

/-- Complete interval computation for depth 15, residue 30460. -/
theorem bounds_15_30460 : exactInterval 15 30460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30460 : oddCount 30460 15 = 11 ∧ acceleratedOrbit 15 30460 = 164693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30460) = 3 ^ 11 * m + 164693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30460.1, data_15_30460.2]

/-- Complete interval computation for depth 15, residue 30461. -/
theorem bounds_15_30461 : exactInterval 15 30461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30461 : oddCount 30461 15 = 11 ∧ acceleratedOrbit 15 30461 = 164693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30461) = 3 ^ 11 * m + 164693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30461.1, data_15_30461.2]

/-- Complete interval computation for depth 15, residue 30462. -/
theorem bounds_15_30462 : exactInterval 15 30462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30462 : oddCount 30462 15 = 11 ∧ acceleratedOrbit 15 30462 = 164693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30462) = 3 ^ 11 * m + 164693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30462.1, data_15_30462.2]

/-- Complete interval computation for depth 15, residue 30463. -/
theorem bounds_15_30463 : exactInterval 15 30463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30463 : oddCount 30463 15 = 12 ∧ acceleratedOrbit 15 30463 = 494075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30463) = 3 ^ 12 * m + 494075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30463.1, data_15_30463.2]

/-- Complete interval computation for depth 15, residue 30464. -/
theorem bounds_15_30464 : exactInterval 15 30464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30464 : oddCount 30464 15 = 4 ∧ acceleratedOrbit 15 30464 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30464) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30464.1, data_15_30464.2]

/-- Complete interval computation for depth 15, residue 30465. -/
theorem bounds_15_30465 : exactInterval 15 30465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30465 : oddCount 30465 15 = 5 ∧ acceleratedOrbit 15 30465 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30465) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30465.1, data_15_30465.2]

/-- Complete interval computation for depth 15, residue 30466. -/
theorem bounds_15_30466 : exactInterval 15 30466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30466 : oddCount 30466 15 = 10 ∧ acceleratedOrbit 15 30466 = 54917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30466) = 3 ^ 10 * m + 54917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30466.1, data_15_30466.2]

/-- Complete interval computation for depth 15, residue 30467. -/
theorem bounds_15_30467 : exactInterval 15 30467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30467 : oddCount 30467 15 = 10 ∧ acceleratedOrbit 15 30467 = 54917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30467) = 3 ^ 10 * m + 54917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30467.1, data_15_30467.2]

/-- Complete interval computation for depth 15, residue 30468. -/
theorem bounds_15_30468 : exactInterval 15 30468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30468 : oddCount 30468 15 = 7 ∧ acceleratedOrbit 15 30468 = 2035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30468) = 3 ^ 7 * m + 2035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30468.1, data_15_30468.2]

/-- Complete interval computation for depth 15, residue 30469. -/
theorem bounds_15_30469 : exactInterval 15 30469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30469 : oddCount 30469 15 = 7 ∧ acceleratedOrbit 15 30469 = 2035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30469) = 3 ^ 7 * m + 2035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30469.1, data_15_30469.2]

/-- Complete interval computation for depth 15, residue 30470. -/
theorem bounds_15_30470 : exactInterval 15 30470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30470 : oddCount 30470 15 = 7 ∧ acceleratedOrbit 15 30470 = 2035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30470) = 3 ^ 7 * m + 2035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30470.1, data_15_30470.2]

/-- Complete interval computation for depth 15, residue 30471. -/
theorem bounds_15_30471 : exactInterval 15 30471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30471 : oddCount 30471 15 = 10 ∧ acceleratedOrbit 15 30471 = 54917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30471) = 3 ^ 10 * m + 54917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30471.1, data_15_30471.2]

/-- Complete interval computation for depth 15, residue 30472. -/
theorem bounds_15_30472 : exactInterval 15 30472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30472 : oddCount 30472 15 = 7 ∧ acceleratedOrbit 15 30472 = 2035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30472) = 3 ^ 7 * m + 2035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30472.1, data_15_30472.2]

/-- Complete interval computation for depth 15, residue 30473. -/
theorem bounds_15_30473 : exactInterval 15 30473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30473 : oddCount 30473 15 = 12 ∧ acceleratedOrbit 15 30473 = 494261 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30473) = 3 ^ 12 * m + 494261 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30473.1, data_15_30473.2]

end Collatz.Research.PassageAtlas.Batch0930
