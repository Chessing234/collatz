import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0869

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28442. -/
theorem bounds_15_28442 : exactInterval 15 28442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28442 : oddCount 28442 15 = 4 ∧ acceleratedOrbit 15 28442 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28442) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28442.1, data_15_28442.2]

/-- Complete interval computation for depth 15, residue 28443. -/
theorem bounds_15_28443 : exactInterval 15 28443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28443 : oddCount 28443 15 = 12 ∧ acceleratedOrbit 15 28443 = 461321 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28443) = 3 ^ 12 * m + 461321 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28443.1, data_15_28443.2]

/-- Complete interval computation for depth 15, residue 28444. -/
theorem bounds_15_28444 : exactInterval 15 28444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28444 : oddCount 28444 15 = 10 ∧ acceleratedOrbit 15 28444 = 51272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28444) = 3 ^ 10 * m + 51272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28444.1, data_15_28444.2]

/-- Complete interval computation for depth 15, residue 28445. -/
theorem bounds_15_28445 : exactInterval 15 28445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28445 : oddCount 28445 15 = 10 ∧ acceleratedOrbit 15 28445 = 51272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28445) = 3 ^ 10 * m + 51272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28445.1, data_15_28445.2]

/-- Complete interval computation for depth 15, residue 28446. -/
theorem bounds_15_28446 : exactInterval 15 28446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28446 : oddCount 28446 15 = 10 ∧ acceleratedOrbit 15 28446 = 51272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28446) = 3 ^ 10 * m + 51272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28446.1, data_15_28446.2]

/-- Complete interval computation for depth 15, residue 28447. -/
theorem bounds_15_28447 : exactInterval 15 28447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28447 : oddCount 28447 15 = 10 ∧ acceleratedOrbit 15 28447 = 51266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28447) = 3 ^ 10 * m + 51266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28447.1, data_15_28447.2]

/-- Complete interval computation for depth 15, residue 28448. -/
theorem bounds_15_28448 : exactInterval 15 28448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28448 : oddCount 28448 15 = 7 ∧ acceleratedOrbit 15 28448 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28448) = 3 ^ 7 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28448.1, data_15_28448.2]

/-- Complete interval computation for depth 15, residue 28449. -/
theorem bounds_15_28449 : exactInterval 15 28449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28449 : oddCount 28449 15 = 5 ∧ acceleratedOrbit 15 28449 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28449) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28449.1, data_15_28449.2]

/-- Complete interval computation for depth 15, residue 28450. -/
theorem bounds_15_28450 : exactInterval 15 28450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28450 : oddCount 28450 15 = 7 ∧ acceleratedOrbit 15 28450 = 1900 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28450) = 3 ^ 7 * m + 1900 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28450.1, data_15_28450.2]

/-- Complete interval computation for depth 15, residue 28451. -/
theorem bounds_15_28451 : exactInterval 15 28451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28451 : oddCount 28451 15 = 7 ∧ acceleratedOrbit 15 28451 = 1900 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28451) = 3 ^ 7 * m + 1900 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28451.1, data_15_28451.2]

/-- Complete interval computation for depth 15, residue 28452. -/
theorem bounds_15_28452 : exactInterval 15 28452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28452 : oddCount 28452 15 = 7 ∧ acceleratedOrbit 15 28452 = 1900 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28452) = 3 ^ 7 * m + 1900 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28452.1, data_15_28452.2]

/-- Complete interval computation for depth 15, residue 28453. -/
theorem bounds_15_28453 : exactInterval 15 28453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28453 : oddCount 28453 15 = 7 ∧ acceleratedOrbit 15 28453 = 1900 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28453) = 3 ^ 7 * m + 1900 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28453.1, data_15_28453.2]

/-- Complete interval computation for depth 15, residue 28454. -/
theorem bounds_15_28454 : exactInterval 15 28454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28454 : oddCount 28454 15 = 7 ∧ acceleratedOrbit 15 28454 = 1900 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28454) = 3 ^ 7 * m + 1900 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28454.1, data_15_28454.2]

/-- Complete interval computation for depth 15, residue 28455. -/
theorem bounds_15_28455 : exactInterval 15 28455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28455 : oddCount 28455 15 = 8 ∧ acceleratedOrbit 15 28455 = 5698 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28455) = 3 ^ 8 * m + 5698 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28455.1, data_15_28455.2]

/-- Complete interval computation for depth 15, residue 28456. -/
theorem bounds_15_28456 : exactInterval 15 28456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28456 : oddCount 28456 15 = 7 ∧ acceleratedOrbit 15 28456 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28456) = 3 ^ 7 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28456.1, data_15_28456.2]

/-- Complete interval computation for depth 15, residue 28457. -/
theorem bounds_15_28457 : exactInterval 15 28457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28457 : oddCount 28457 15 = 8 ∧ acceleratedOrbit 15 28457 = 5699 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28457) = 3 ^ 8 * m + 5699 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28457.1, data_15_28457.2]

/-- Complete interval computation for depth 15, residue 28458. -/
theorem bounds_15_28458 : exactInterval 15 28458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28458 : oddCount 28458 15 = 7 ∧ acceleratedOrbit 15 28458 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28458) = 3 ^ 7 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28458.1, data_15_28458.2]

/-- Complete interval computation for depth 15, residue 28459. -/
theorem bounds_15_28459 : exactInterval 15 28459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28459 : oddCount 28459 15 = 7 ∧ acceleratedOrbit 15 28459 = 1900 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28459) = 3 ^ 7 * m + 1900 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28459.1, data_15_28459.2]

/-- Complete interval computation for depth 15, residue 28460. -/
theorem bounds_15_28460 : exactInterval 15 28460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28460 : oddCount 28460 15 = 6 ∧ acceleratedOrbit 15 28460 = 634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28460) = 3 ^ 6 * m + 634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28460.1, data_15_28460.2]

/-- Complete interval computation for depth 15, residue 28461. -/
theorem bounds_15_28461 : exactInterval 15 28461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28461 : oddCount 28461 15 = 6 ∧ acceleratedOrbit 15 28461 = 634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28461) = 3 ^ 6 * m + 634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28461.1, data_15_28461.2]

/-- Complete interval computation for depth 15, residue 28462. -/
theorem bounds_15_28462 : exactInterval 15 28462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28462 : oddCount 28462 15 = 6 ∧ acceleratedOrbit 15 28462 = 634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28462) = 3 ^ 6 * m + 634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28462.1, data_15_28462.2]

/-- Complete interval computation for depth 15, residue 28463. -/
theorem bounds_15_28463 : exactInterval 15 28463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28463 : oddCount 28463 15 = 7 ∧ acceleratedOrbit 15 28463 = 1900 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28463) = 3 ^ 7 * m + 1900 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28463.1, data_15_28463.2]

/-- Complete interval computation for depth 15, residue 28464. -/
theorem bounds_15_28464 : exactInterval 15 28464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28464 : oddCount 28464 15 = 7 ∧ acceleratedOrbit 15 28464 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28464) = 3 ^ 7 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28464.1, data_15_28464.2]

/-- Complete interval computation for depth 15, residue 28465. -/
theorem bounds_15_28465 : exactInterval 15 28465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28465 : oddCount 28465 15 = 6 ∧ acceleratedOrbit 15 28465 = 634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28465) = 3 ^ 6 * m + 634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28465.1, data_15_28465.2]

/-- Complete interval computation for depth 15, residue 28466. -/
theorem bounds_15_28466 : exactInterval 15 28466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28466 : oddCount 28466 15 = 6 ∧ acceleratedOrbit 15 28466 = 634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28466) = 3 ^ 6 * m + 634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28466.1, data_15_28466.2]

/-- Complete interval computation for depth 15, residue 28467. -/
theorem bounds_15_28467 : exactInterval 15 28467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28467 : oddCount 28467 15 = 6 ∧ acceleratedOrbit 15 28467 = 634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28467) = 3 ^ 6 * m + 634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28467.1, data_15_28467.2]

/-- Complete interval computation for depth 15, residue 28468. -/
theorem bounds_15_28468 : exactInterval 15 28468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28468 : oddCount 28468 15 = 7 ∧ acceleratedOrbit 15 28468 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28468) = 3 ^ 7 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28468.1, data_15_28468.2]

/-- Complete interval computation for depth 15, residue 28469. -/
theorem bounds_15_28469 : exactInterval 15 28469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28469 : oddCount 28469 15 = 7 ∧ acceleratedOrbit 15 28469 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28469) = 3 ^ 7 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28469.1, data_15_28469.2]

/-- Complete interval computation for depth 15, residue 28470. -/
theorem bounds_15_28470 : exactInterval 15 28470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28470 : oddCount 28470 15 = 9 ∧ acceleratedOrbit 15 28470 = 17104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28470) = 3 ^ 9 * m + 17104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28470.1, data_15_28470.2]

/-- Complete interval computation for depth 15, residue 28471. -/
theorem bounds_15_28471 : exactInterval 15 28471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28471 : oddCount 28471 15 = 9 ∧ acceleratedOrbit 15 28471 = 17104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28471) = 3 ^ 9 * m + 17104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28471.1, data_15_28471.2]

/-- Complete interval computation for depth 15, residue 28472. -/
theorem bounds_15_28472 : exactInterval 15 28472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28472 : oddCount 28472 15 = 7 ∧ acceleratedOrbit 15 28472 = 1901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28472) = 3 ^ 7 * m + 1901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28472.1, data_15_28472.2]

/-- Complete interval computation for depth 15, residue 28473. -/
theorem bounds_15_28473 : exactInterval 15 28473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28473 : oddCount 28473 15 = 7 ∧ acceleratedOrbit 15 28473 = 1901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28473) = 3 ^ 7 * m + 1901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28473.1, data_15_28473.2]

/-- Complete interval computation for depth 15, residue 28474. -/
theorem bounds_15_28474 : exactInterval 15 28474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28474 : oddCount 28474 15 = 7 ∧ acceleratedOrbit 15 28474 = 1901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28474) = 3 ^ 7 * m + 1901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28474.1, data_15_28474.2]

end Collatz.Research.PassageAtlas.Batch0869
