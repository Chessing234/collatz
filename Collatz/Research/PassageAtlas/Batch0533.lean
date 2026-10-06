import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0533

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17432. -/
theorem bounds_15_17432 : exactInterval 15 17432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17432 : oddCount 17432 15 = 5 ∧ acceleratedOrbit 15 17432 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17432) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17432.1, data_15_17432.2]

/-- Complete interval computation for depth 15, residue 17433. -/
theorem bounds_15_17433 : exactInterval 15 17433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17433 : oddCount 17433 15 = 9 ∧ acceleratedOrbit 15 17433 = 10475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17433) = 3 ^ 9 * m + 10475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17433.1, data_15_17433.2]

/-- Complete interval computation for depth 15, residue 17434. -/
theorem bounds_15_17434 : exactInterval 15 17434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17434 : oddCount 17434 15 = 5 ∧ acceleratedOrbit 15 17434 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17434) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17434.1, data_15_17434.2]

/-- Complete interval computation for depth 15, residue 17435. -/
theorem bounds_15_17435 : exactInterval 15 17435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17435 : oddCount 17435 15 = 12 ∧ acceleratedOrbit 15 17435 = 282791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17435) = 3 ^ 12 * m + 282791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17435.1, data_15_17435.2]

/-- Complete interval computation for depth 15, residue 17436. -/
theorem bounds_15_17436 : exactInterval 15 17436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17436 : oddCount 17436 15 = 8 ∧ acceleratedOrbit 15 17436 = 3493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17436) = 3 ^ 8 * m + 3493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17436.1, data_15_17436.2]

/-- Complete interval computation for depth 15, residue 17437. -/
theorem bounds_15_17437 : exactInterval 15 17437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17437 : oddCount 17437 15 = 8 ∧ acceleratedOrbit 15 17437 = 3493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17437) = 3 ^ 8 * m + 3493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17437.1, data_15_17437.2]

/-- Complete interval computation for depth 15, residue 17438. -/
theorem bounds_15_17438 : exactInterval 15 17438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17438 : oddCount 17438 15 = 8 ∧ acceleratedOrbit 15 17438 = 3493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17438) = 3 ^ 8 * m + 3493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17438.1, data_15_17438.2]

/-- Complete interval computation for depth 15, residue 17439. -/
theorem bounds_15_17439 : exactInterval 15 17439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17439 : oddCount 17439 15 = 13 ∧ acceleratedOrbit 15 17439 = 848555 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17439) = 3 ^ 13 * m + 848555 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17439.1, data_15_17439.2]

/-- Complete interval computation for depth 15, residue 17440. -/
theorem bounds_15_17440 : exactInterval 15 17440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17440 : oddCount 17440 15 = 5 ∧ acceleratedOrbit 15 17440 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17440) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17440.1, data_15_17440.2]

/-- Complete interval computation for depth 15, residue 17441. -/
theorem bounds_15_17441 : exactInterval 15 17441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17441 : oddCount 17441 15 = 8 ∧ acceleratedOrbit 15 17441 = 3493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17441) = 3 ^ 8 * m + 3493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17441.1, data_15_17441.2]

/-- Complete interval computation for depth 15, residue 17442. -/
theorem bounds_15_17442 : exactInterval 15 17442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17442 : oddCount 17442 15 = 5 ∧ acceleratedOrbit 15 17442 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17442) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17442.1, data_15_17442.2]

/-- Complete interval computation for depth 15, residue 17443. -/
theorem bounds_15_17443 : exactInterval 15 17443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17443 : oddCount 17443 15 = 5 ∧ acceleratedOrbit 15 17443 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17443) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17443.1, data_15_17443.2]

/-- Complete interval computation for depth 15, residue 17444. -/
theorem bounds_15_17444 : exactInterval 15 17444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17444 : oddCount 17444 15 = 7 ∧ acceleratedOrbit 15 17444 = 1165 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17444) = 3 ^ 7 * m + 1165 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17444.1, data_15_17444.2]

/-- Complete interval computation for depth 15, residue 17445. -/
theorem bounds_15_17445 : exactInterval 15 17445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17445 : oddCount 17445 15 = 7 ∧ acceleratedOrbit 15 17445 = 1165 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17445) = 3 ^ 7 * m + 1165 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17445.1, data_15_17445.2]

/-- Complete interval computation for depth 15, residue 17446. -/
theorem bounds_15_17446 : exactInterval 15 17446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17446 : oddCount 17446 15 = 7 ∧ acceleratedOrbit 15 17446 = 1165 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17446) = 3 ^ 7 * m + 1165 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17446.1, data_15_17446.2]

/-- Complete interval computation for depth 15, residue 17447. -/
theorem bounds_15_17447 : exactInterval 15 17447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17447 : oddCount 17447 15 = 8 ∧ acceleratedOrbit 15 17447 = 3494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17447) = 3 ^ 8 * m + 3494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17447.1, data_15_17447.2]

/-- Complete interval computation for depth 15, residue 17448. -/
theorem bounds_15_17448 : exactInterval 15 17448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17448 : oddCount 17448 15 = 5 ∧ acceleratedOrbit 15 17448 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17448) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17448.1, data_15_17448.2]

/-- Complete interval computation for depth 15, residue 17449. -/
theorem bounds_15_17449 : exactInterval 15 17449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17449 : oddCount 17449 15 = 10 ∧ acceleratedOrbit 15 17449 = 31448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17449) = 3 ^ 10 * m + 31448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17449.1, data_15_17449.2]

/-- Complete interval computation for depth 15, residue 17450. -/
theorem bounds_15_17450 : exactInterval 15 17450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17450 : oddCount 17450 15 = 5 ∧ acceleratedOrbit 15 17450 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17450) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17450.1, data_15_17450.2]

/-- Complete interval computation for depth 15, residue 17451. -/
theorem bounds_15_17451 : exactInterval 15 17451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17451 : oddCount 17451 15 = 8 ∧ acceleratedOrbit 15 17451 = 3496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17451) = 3 ^ 8 * m + 3496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17451.1, data_15_17451.2]

/-- Complete interval computation for depth 15, residue 17452. -/
theorem bounds_15_17452 : exactInterval 15 17452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17452 : oddCount 17452 15 = 6 ∧ acceleratedOrbit 15 17452 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17452) = 3 ^ 6 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17452.1, data_15_17452.2]

/-- Complete interval computation for depth 15, residue 17453. -/
theorem bounds_15_17453 : exactInterval 15 17453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17453 : oddCount 17453 15 = 6 ∧ acceleratedOrbit 15 17453 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17453) = 3 ^ 6 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17453.1, data_15_17453.2]

/-- Complete interval computation for depth 15, residue 17454. -/
theorem bounds_15_17454 : exactInterval 15 17454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17454 : oddCount 17454 15 = 6 ∧ acceleratedOrbit 15 17454 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17454) = 3 ^ 6 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17454.1, data_15_17454.2]

/-- Complete interval computation for depth 15, residue 17455. -/
theorem bounds_15_17455 : exactInterval 15 17455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17455 : oddCount 17455 15 = 9 ∧ acceleratedOrbit 15 17455 = 10486 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17455) = 3 ^ 9 * m + 10486 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17455.1, data_15_17455.2]

/-- Complete interval computation for depth 15, residue 17456. -/
theorem bounds_15_17456 : exactInterval 15 17456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17456 : oddCount 17456 15 = 5 ∧ acceleratedOrbit 15 17456 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17456) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17456.1, data_15_17456.2]

/-- Complete interval computation for depth 15, residue 17457. -/
theorem bounds_15_17457 : exactInterval 15 17457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17457 : oddCount 17457 15 = 6 ∧ acceleratedOrbit 15 17457 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17457) = 3 ^ 6 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17457.1, data_15_17457.2]

/-- Complete interval computation for depth 15, residue 17458. -/
theorem bounds_15_17458 : exactInterval 15 17458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17458 : oddCount 17458 15 = 6 ∧ acceleratedOrbit 15 17458 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17458) = 3 ^ 6 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17458.1, data_15_17458.2]

/-- Complete interval computation for depth 15, residue 17459. -/
theorem bounds_15_17459 : exactInterval 15 17459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17459 : oddCount 17459 15 = 6 ∧ acceleratedOrbit 15 17459 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17459) = 3 ^ 6 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17459.1, data_15_17459.2]

/-- Complete interval computation for depth 15, residue 17460. -/
theorem bounds_15_17460 : exactInterval 15 17460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17460 : oddCount 17460 15 = 5 ∧ acceleratedOrbit 15 17460 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17460) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17460.1, data_15_17460.2]

/-- Complete interval computation for depth 15, residue 17461. -/
theorem bounds_15_17461 : exactInterval 15 17461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17461 : oddCount 17461 15 = 5 ∧ acceleratedOrbit 15 17461 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17461) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17461.1, data_15_17461.2]

/-- Complete interval computation for depth 15, residue 17462. -/
theorem bounds_15_17462 : exactInterval 15 17462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17462 : oddCount 17462 15 = 8 ∧ acceleratedOrbit 15 17462 = 3497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17462) = 3 ^ 8 * m + 3497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17462.1, data_15_17462.2]

/-- Complete interval computation for depth 15, residue 17463. -/
theorem bounds_15_17463 : exactInterval 15 17463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17463 : oddCount 17463 15 = 8 ∧ acceleratedOrbit 15 17463 = 3497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17463) = 3 ^ 8 * m + 3497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17463.1, data_15_17463.2]

/-- Complete interval computation for depth 15, residue 17464. -/
theorem bounds_15_17464 : exactInterval 15 17464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17464 : oddCount 17464 15 = 6 ∧ acceleratedOrbit 15 17464 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17464) = 3 ^ 6 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17464.1, data_15_17464.2]

end Collatz.Research.PassageAtlas.Batch0533
