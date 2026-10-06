import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0411

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13434. -/
theorem bounds_15_13434 : exactInterval 15 13434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13434 : oddCount 13434 15 = 8 ∧ acceleratedOrbit 15 13434 = 2693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13434) = 3 ^ 8 * m + 2693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13434.1, data_15_13434.2]

/-- Complete interval computation for depth 15, residue 13435. -/
theorem bounds_15_13435 : exactInterval 15 13435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13435 : oddCount 13435 15 = 10 ∧ acceleratedOrbit 15 13435 = 24218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13435) = 3 ^ 10 * m + 24218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13435.1, data_15_13435.2]

/-- Complete interval computation for depth 15, residue 13436. -/
theorem bounds_15_13436 : exactInterval 15 13436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13436 : oddCount 13436 15 = 6 ∧ acceleratedOrbit 15 13436 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13436) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13436.1, data_15_13436.2]

/-- Complete interval computation for depth 15, residue 13437. -/
theorem bounds_15_13437 : exactInterval 15 13437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13437 : oddCount 13437 15 = 6 ∧ acceleratedOrbit 15 13437 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13437) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13437.1, data_15_13437.2]

/-- Complete interval computation for depth 15, residue 13438. -/
theorem bounds_15_13438 : exactInterval 15 13438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13438 : oddCount 13438 15 = 6 ∧ acceleratedOrbit 15 13438 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13438) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13438.1, data_15_13438.2]

/-- Complete interval computation for depth 15, residue 13439. -/
theorem bounds_15_13439 : exactInterval 15 13439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13439 : oddCount 13439 15 = 11 ∧ acceleratedOrbit 15 13439 = 72659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13439) = 3 ^ 11 * m + 72659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13439.1, data_15_13439.2]

/-- Complete interval computation for depth 15, residue 13440. -/
theorem bounds_15_13440 : exactInterval 15 13440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13440 : oddCount 13440 15 = 5 ∧ acceleratedOrbit 15 13440 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13440) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13440.1, data_15_13440.2]

/-- Complete interval computation for depth 15, residue 13441. -/
theorem bounds_15_13441 : exactInterval 15 13441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13441 : oddCount 13441 15 = 8 ∧ acceleratedOrbit 15 13441 = 2692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13441) = 3 ^ 8 * m + 2692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13441.1, data_15_13441.2]

/-- Complete interval computation for depth 15, residue 13442. -/
theorem bounds_15_13442 : exactInterval 15 13442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13442 : oddCount 13442 15 = 5 ∧ acceleratedOrbit 15 13442 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13442) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13442.1, data_15_13442.2]

/-- Complete interval computation for depth 15, residue 13443. -/
theorem bounds_15_13443 : exactInterval 15 13443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13443 : oddCount 13443 15 = 5 ∧ acceleratedOrbit 15 13443 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13443) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13443.1, data_15_13443.2]

/-- Complete interval computation for depth 15, residue 13444. -/
theorem bounds_15_13444 : exactInterval 15 13444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13444 : oddCount 13444 15 = 5 ∧ acceleratedOrbit 15 13444 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13444) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13444.1, data_15_13444.2]

/-- Complete interval computation for depth 15, residue 13445. -/
theorem bounds_15_13445 : exactInterval 15 13445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13445 : oddCount 13445 15 = 5 ∧ acceleratedOrbit 15 13445 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13445) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13445.1, data_15_13445.2]

/-- Complete interval computation for depth 15, residue 13446. -/
theorem bounds_15_13446 : exactInterval 15 13446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13446 : oddCount 13446 15 = 5 ∧ acceleratedOrbit 15 13446 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13446) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13446.1, data_15_13446.2]

/-- Complete interval computation for depth 15, residue 13447. -/
theorem bounds_15_13447 : exactInterval 15 13447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13447 : oddCount 13447 15 = 10 ∧ acceleratedOrbit 15 13447 = 24239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13447) = 3 ^ 10 * m + 24239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13447.1, data_15_13447.2]

/-- Complete interval computation for depth 15, residue 13448. -/
theorem bounds_15_13448 : exactInterval 15 13448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13448 : oddCount 13448 15 = 5 ∧ acceleratedOrbit 15 13448 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13448) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13448.1, data_15_13448.2]

/-- Complete interval computation for depth 15, residue 13449. -/
theorem bounds_15_13449 : exactInterval 15 13449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13449 : oddCount 13449 15 = 12 ∧ acceleratedOrbit 15 13449 = 218153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13449) = 3 ^ 12 * m + 218153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13449.1, data_15_13449.2]

/-- Complete interval computation for depth 15, residue 13450. -/
theorem bounds_15_13450 : exactInterval 15 13450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13450 : oddCount 13450 15 = 5 ∧ acceleratedOrbit 15 13450 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13450) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13450.1, data_15_13450.2]

/-- Complete interval computation for depth 15, residue 13451. -/
theorem bounds_15_13451 : exactInterval 15 13451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13451 : oddCount 13451 15 = 7 ∧ acceleratedOrbit 15 13451 = 898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13451) = 3 ^ 7 * m + 898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13451.1, data_15_13451.2]

/-- Complete interval computation for depth 15, residue 13452. -/
theorem bounds_15_13452 : exactInterval 15 13452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13452 : oddCount 13452 15 = 5 ∧ acceleratedOrbit 15 13452 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13452) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13452.1, data_15_13452.2]

/-- Complete interval computation for depth 15, residue 13453. -/
theorem bounds_15_13453 : exactInterval 15 13453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13453 : oddCount 13453 15 = 5 ∧ acceleratedOrbit 15 13453 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13453) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13453.1, data_15_13453.2]

/-- Complete interval computation for depth 15, residue 13454. -/
theorem bounds_15_13454 : exactInterval 15 13454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13454 : oddCount 13454 15 = 8 ∧ acceleratedOrbit 15 13454 = 2695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13454) = 3 ^ 8 * m + 2695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13454.1, data_15_13454.2]

/-- Complete interval computation for depth 15, residue 13455. -/
theorem bounds_15_13455 : exactInterval 15 13455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13455 : oddCount 13455 15 = 8 ∧ acceleratedOrbit 15 13455 = 2695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13455) = 3 ^ 8 * m + 2695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13455.1, data_15_13455.2]

/-- Complete interval computation for depth 15, residue 13456. -/
theorem bounds_15_13456 : exactInterval 15 13456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13456 : oddCount 13456 15 = 5 ∧ acceleratedOrbit 15 13456 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13456) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13456.1, data_15_13456.2]

/-- Complete interval computation for depth 15, residue 13457. -/
theorem bounds_15_13457 : exactInterval 15 13457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13457 : oddCount 13457 15 = 7 ∧ acceleratedOrbit 15 13457 = 899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13457) = 3 ^ 7 * m + 899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13457.1, data_15_13457.2]

/-- Complete interval computation for depth 15, residue 13458. -/
theorem bounds_15_13458 : exactInterval 15 13458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13458 : oddCount 13458 15 = 7 ∧ acceleratedOrbit 15 13458 = 899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13458) = 3 ^ 7 * m + 899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13458.1, data_15_13458.2]

/-- Complete interval computation for depth 15, residue 13459. -/
theorem bounds_15_13459 : exactInterval 15 13459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13459 : oddCount 13459 15 = 7 ∧ acceleratedOrbit 15 13459 = 899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13459) = 3 ^ 7 * m + 899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13459.1, data_15_13459.2]

/-- Complete interval computation for depth 15, residue 13460. -/
theorem bounds_15_13460 : exactInterval 15 13460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13460 : oddCount 13460 15 = 5 ∧ acceleratedOrbit 15 13460 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13460) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13460.1, data_15_13460.2]

/-- Complete interval computation for depth 15, residue 13461. -/
theorem bounds_15_13461 : exactInterval 15 13461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13461 : oddCount 13461 15 = 5 ∧ acceleratedOrbit 15 13461 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13461) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13461.1, data_15_13461.2]

/-- Complete interval computation for depth 15, residue 13462. -/
theorem bounds_15_13462 : exactInterval 15 13462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13462 : oddCount 13462 15 = 5 ∧ acceleratedOrbit 15 13462 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13462) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13462.1, data_15_13462.2]

/-- Complete interval computation for depth 15, residue 13463. -/
theorem bounds_15_13463 : exactInterval 15 13463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13463 : oddCount 13463 15 = 5 ∧ acceleratedOrbit 15 13463 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13463) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13463.1, data_15_13463.2]

/-- Complete interval computation for depth 15, residue 13464. -/
theorem bounds_15_13464 : exactInterval 15 13464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13464 : oddCount 13464 15 = 5 ∧ acceleratedOrbit 15 13464 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13464) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13464.1, data_15_13464.2]

/-- Complete interval computation for depth 15, residue 13465. -/
theorem bounds_15_13465 : exactInterval 15 13465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13465 : oddCount 13465 15 = 8 ∧ acceleratedOrbit 15 13465 = 2699 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13465) = 3 ^ 8 * m + 2699 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13465.1, data_15_13465.2]

/-- Complete interval computation for depth 15, residue 13466. -/
theorem bounds_15_13466 : exactInterval 15 13466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13466 : oddCount 13466 15 = 5 ∧ acceleratedOrbit 15 13466 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13466) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13466.1, data_15_13466.2]

end Collatz.Research.PassageAtlas.Batch0411
