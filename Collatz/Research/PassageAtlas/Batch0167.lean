import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0167

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5439. -/
theorem bounds_15_5439 : exactInterval 15 5439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5439 : oddCount 5439 15 = 9 ∧ acceleratedOrbit 15 5439 = 3268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5439) = 3 ^ 9 * m + 3268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5439.1, data_15_5439.2]

/-- Complete interval computation for depth 15, residue 5440. -/
theorem bounds_15_5440 : exactInterval 15 5440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5440 : oddCount 5440 15 = 2 ∧ acceleratedOrbit 15 5440 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5440) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5440.1, data_15_5440.2]

/-- Complete interval computation for depth 15, residue 5441. -/
theorem bounds_15_5441 : exactInterval 15 5441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5441 : oddCount 5441 15 = 8 ∧ acceleratedOrbit 15 5441 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5441) = 3 ^ 8 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5441.1, data_15_5441.2]

/-- Complete interval computation for depth 15, residue 5442. -/
theorem bounds_15_5442 : exactInterval 15 5442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5442 : oddCount 5442 15 = 8 ∧ acceleratedOrbit 15 5442 = 1091 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5442) = 3 ^ 8 * m + 1091 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5442.1, data_15_5442.2]

/-- Complete interval computation for depth 15, residue 5443. -/
theorem bounds_15_5443 : exactInterval 15 5443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5443 : oddCount 5443 15 = 8 ∧ acceleratedOrbit 15 5443 = 1091 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5443) = 3 ^ 8 * m + 1091 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5443.1, data_15_5443.2]

/-- Complete interval computation for depth 15, residue 5444. -/
theorem bounds_15_5444 : exactInterval 15 5444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5444 : oddCount 5444 15 = 9 ∧ acceleratedOrbit 15 5444 = 3280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5444) = 3 ^ 9 * m + 3280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5444.1, data_15_5444.2]

/-- Complete interval computation for depth 15, residue 5445. -/
theorem bounds_15_5445 : exactInterval 15 5445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5445 : oddCount 5445 15 = 9 ∧ acceleratedOrbit 15 5445 = 3280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5445) = 3 ^ 9 * m + 3280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5445.1, data_15_5445.2]

/-- Complete interval computation for depth 15, residue 5446. -/
theorem bounds_15_5446 : exactInterval 15 5446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5446 : oddCount 5446 15 = 9 ∧ acceleratedOrbit 15 5446 = 3280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5446) = 3 ^ 9 * m + 3280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5446.1, data_15_5446.2]

/-- Complete interval computation for depth 15, residue 5447. -/
theorem bounds_15_5447 : exactInterval 15 5447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5447 : oddCount 5447 15 = 12 ∧ acceleratedOrbit 15 5447 = 88370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5447) = 3 ^ 12 * m + 88370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5447.1, data_15_5447.2]

/-- Complete interval computation for depth 15, residue 5448. -/
theorem bounds_15_5448 : exactInterval 15 5448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5448 : oddCount 5448 15 = 10 ∧ acceleratedOrbit 15 5448 = 9841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5448) = 3 ^ 10 * m + 9841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5448.1, data_15_5448.2]

/-- Complete interval computation for depth 15, residue 5449. -/
theorem bounds_15_5449 : exactInterval 15 5449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5449 : oddCount 5449 15 = 10 ∧ acceleratedOrbit 15 5449 = 9827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5449) = 3 ^ 10 * m + 9827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5449.1, data_15_5449.2]

/-- Complete interval computation for depth 15, residue 5450. -/
theorem bounds_15_5450 : exactInterval 15 5450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5450 : oddCount 5450 15 = 10 ∧ acceleratedOrbit 15 5450 = 9841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5450) = 3 ^ 10 * m + 9841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5450.1, data_15_5450.2]

/-- Complete interval computation for depth 15, residue 5451. -/
theorem bounds_15_5451 : exactInterval 15 5451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5451 : oddCount 5451 15 = 9 ∧ acceleratedOrbit 15 5451 = 3280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5451) = 3 ^ 9 * m + 3280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5451.1, data_15_5451.2]

/-- Complete interval computation for depth 15, residue 5452. -/
theorem bounds_15_5452 : exactInterval 15 5452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5452 : oddCount 5452 15 = 10 ∧ acceleratedOrbit 15 5452 = 9841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5452) = 3 ^ 10 * m + 9841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5452.1, data_15_5452.2]

/-- Complete interval computation for depth 15, residue 5453. -/
theorem bounds_15_5453 : exactInterval 15 5453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5453 : oddCount 5453 15 = 10 ∧ acceleratedOrbit 15 5453 = 9841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5453) = 3 ^ 10 * m + 9841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5453.1, data_15_5453.2]

/-- Complete interval computation for depth 15, residue 5454. -/
theorem bounds_15_5454 : exactInterval 15 5454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5454 : oddCount 5454 15 = 9 ∧ acceleratedOrbit 15 5454 = 3278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5454) = 3 ^ 9 * m + 3278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5454.1, data_15_5454.2]

/-- Complete interval computation for depth 15, residue 5455. -/
theorem bounds_15_5455 : exactInterval 15 5455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5455 : oddCount 5455 15 = 9 ∧ acceleratedOrbit 15 5455 = 3278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5455) = 3 ^ 9 * m + 3278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5455.1, data_15_5455.2]

/-- Complete interval computation for depth 15, residue 5456. -/
theorem bounds_15_5456 : exactInterval 15 5456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5456 : oddCount 5456 15 = 2 ∧ acceleratedOrbit 15 5456 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5456) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5456.1, data_15_5456.2]

/-- Complete interval computation for depth 15, residue 5457. -/
theorem bounds_15_5457 : exactInterval 15 5457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5457 : oddCount 5457 15 = 11 ∧ acceleratedOrbit 15 5457 = 29524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5457) = 3 ^ 11 * m + 29524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5457.1, data_15_5457.2]

/-- Complete interval computation for depth 15, residue 5458. -/
theorem bounds_15_5458 : exactInterval 15 5458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5458 : oddCount 5458 15 = 12 ∧ acceleratedOrbit 15 5458 = 88573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5458) = 3 ^ 12 * m + 88573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5458.1, data_15_5458.2]

/-- Complete interval computation for depth 15, residue 5459. -/
theorem bounds_15_5459 : exactInterval 15 5459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5459 : oddCount 5459 15 = 12 ∧ acceleratedOrbit 15 5459 = 88573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5459) = 3 ^ 12 * m + 88573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5459.1, data_15_5459.2]

/-- Complete interval computation for depth 15, residue 5460. -/
theorem bounds_15_5460 : exactInterval 15 5460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5460 : oddCount 5460 15 = 2 ∧ acceleratedOrbit 15 5460 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5460) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5460.1, data_15_5460.2]

/-- Complete interval computation for depth 15, residue 5461. -/
theorem bounds_15_5461 : exactInterval 15 5461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5461 : oddCount 5461 15 = 2 ∧ acceleratedOrbit 15 5461 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5461) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5461.1, data_15_5461.2]

/-- Complete interval computation for depth 15, residue 5462. -/
theorem bounds_15_5462 : exactInterval 15 5462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5462 : oddCount 5462 15 = 7 ∧ acceleratedOrbit 15 5462 = 365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5462) = 3 ^ 7 * m + 365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5462.1, data_15_5462.2]

/-- Complete interval computation for depth 15, residue 5463. -/
theorem bounds_15_5463 : exactInterval 15 5463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5463 : oddCount 5463 15 = 7 ∧ acceleratedOrbit 15 5463 = 365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5463) = 3 ^ 7 * m + 365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5463.1, data_15_5463.2]

/-- Complete interval computation for depth 15, residue 5464. -/
theorem bounds_15_5464 : exactInterval 15 5464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5464 : oddCount 5464 15 = 6 ∧ acceleratedOrbit 15 5464 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5464) = 3 ^ 6 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5464.1, data_15_5464.2]

/-- Complete interval computation for depth 15, residue 5465. -/
theorem bounds_15_5465 : exactInterval 15 5465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5465 : oddCount 5465 15 = 8 ∧ acceleratedOrbit 15 5465 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5465) = 3 ^ 8 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5465.1, data_15_5465.2]

/-- Complete interval computation for depth 15, residue 5466. -/
theorem bounds_15_5466 : exactInterval 15 5466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5466 : oddCount 5466 15 = 6 ∧ acceleratedOrbit 15 5466 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5466) = 3 ^ 6 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5466.1, data_15_5466.2]

/-- Complete interval computation for depth 15, residue 5467. -/
theorem bounds_15_5467 : exactInterval 15 5467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5467 : oddCount 5467 15 = 7 ∧ acceleratedOrbit 15 5467 = 365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5467) = 3 ^ 7 * m + 365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5467.1, data_15_5467.2]

/-- Complete interval computation for depth 15, residue 5468. -/
theorem bounds_15_5468 : exactInterval 15 5468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5468 : oddCount 5468 15 = 6 ∧ acceleratedOrbit 15 5468 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5468) = 3 ^ 6 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5468.1, data_15_5468.2]

/-- Complete interval computation for depth 15, residue 5469. -/
theorem bounds_15_5469 : exactInterval 15 5469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5469 : oddCount 5469 15 = 6 ∧ acceleratedOrbit 15 5469 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5469) = 3 ^ 6 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5469.1, data_15_5469.2]

/-- Complete interval computation for depth 15, residue 5470. -/
theorem bounds_15_5470 : exactInterval 15 5470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5470 : oddCount 5470 15 = 8 ∧ acceleratedOrbit 15 5470 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5470) = 3 ^ 8 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5470.1, data_15_5470.2]

/-- Complete interval computation for depth 15, residue 5471. -/
theorem bounds_15_5471 : exactInterval 15 5471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5471 : oddCount 5471 15 = 8 ∧ acceleratedOrbit 15 5471 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5471) = 3 ^ 8 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5471.1, data_15_5471.2]

end Collatz.Research.PassageAtlas.Batch0167
