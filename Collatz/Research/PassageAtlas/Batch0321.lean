import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0321

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10485. -/
theorem bounds_15_10485 : exactInterval 15 10485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10485 : oddCount 10485 15 = 8 ∧ acceleratedOrbit 15 10485 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10485) = 3 ^ 8 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10485.1, data_15_10485.2]

/-- Complete interval computation for depth 15, residue 10486. -/
theorem bounds_15_10486 : exactInterval 15 10486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10486 : oddCount 10486 15 = 8 ∧ acceleratedOrbit 15 10486 = 2101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10486) = 3 ^ 8 * m + 2101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10486.1, data_15_10486.2]

/-- Complete interval computation for depth 15, residue 10487. -/
theorem bounds_15_10487 : exactInterval 15 10487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10487 : oddCount 10487 15 = 8 ∧ acceleratedOrbit 15 10487 = 2101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10487) = 3 ^ 8 * m + 2101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10487.1, data_15_10487.2]

/-- Complete interval computation for depth 15, residue 10488. -/
theorem bounds_15_10488 : exactInterval 15 10488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10488 : oddCount 10488 15 = 7 ∧ acceleratedOrbit 15 10488 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10488) = 3 ^ 7 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10488.1, data_15_10488.2]

/-- Complete interval computation for depth 15, residue 10489. -/
theorem bounds_15_10489 : exactInterval 15 10489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10489 : oddCount 10489 15 = 8 ∧ acceleratedOrbit 15 10489 = 2101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10489) = 3 ^ 8 * m + 2101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10489.1, data_15_10489.2]

/-- Complete interval computation for depth 15, residue 10490. -/
theorem bounds_15_10490 : exactInterval 15 10490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10490 : oddCount 10490 15 = 7 ∧ acceleratedOrbit 15 10490 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10490) = 3 ^ 7 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10490.1, data_15_10490.2]

/-- Complete interval computation for depth 15, residue 10491. -/
theorem bounds_15_10491 : exactInterval 15 10491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10491 : oddCount 10491 15 = 11 ∧ acceleratedOrbit 15 10491 = 56726 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10491) = 3 ^ 11 * m + 56726 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10491.1, data_15_10491.2]

/-- Complete interval computation for depth 15, residue 10492. -/
theorem bounds_15_10492 : exactInterval 15 10492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10492 : oddCount 10492 15 = 7 ∧ acceleratedOrbit 15 10492 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10492) = 3 ^ 7 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10492.1, data_15_10492.2]

/-- Complete interval computation for depth 15, residue 10493. -/
theorem bounds_15_10493 : exactInterval 15 10493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10493 : oddCount 10493 15 = 7 ∧ acceleratedOrbit 15 10493 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10493) = 3 ^ 7 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10493.1, data_15_10493.2]

/-- Complete interval computation for depth 15, residue 10494. -/
theorem bounds_15_10494 : exactInterval 15 10494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10494 : oddCount 10494 15 = 11 ∧ acceleratedOrbit 15 10494 = 56744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10494) = 3 ^ 11 * m + 56744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10494.1, data_15_10494.2]

/-- Complete interval computation for depth 15, residue 10495. -/
theorem bounds_15_10495 : exactInterval 15 10495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10495 : oddCount 10495 15 = 11 ∧ acceleratedOrbit 15 10495 = 56744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10495) = 3 ^ 11 * m + 56744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10495.1, data_15_10495.2]

/-- Complete interval computation for depth 15, residue 10496. -/
theorem bounds_15_10496 : exactInterval 15 10496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10496 : oddCount 10496 15 = 6 ∧ acceleratedOrbit 15 10496 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10496) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10496.1, data_15_10496.2]

/-- Complete interval computation for depth 15, residue 10497. -/
theorem bounds_15_10497 : exactInterval 15 10497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10497 : oddCount 10497 15 = 8 ∧ acceleratedOrbit 15 10497 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10497) = 3 ^ 8 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10497.1, data_15_10497.2]

/-- Complete interval computation for depth 15, residue 10498. -/
theorem bounds_15_10498 : exactInterval 15 10498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10498 : oddCount 10498 15 = 9 ∧ acceleratedOrbit 15 10498 = 6311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10498) = 3 ^ 9 * m + 6311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10498.1, data_15_10498.2]

/-- Complete interval computation for depth 15, residue 10499. -/
theorem bounds_15_10499 : exactInterval 15 10499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10499 : oddCount 10499 15 = 9 ∧ acceleratedOrbit 15 10499 = 6311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10499) = 3 ^ 9 * m + 6311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10499.1, data_15_10499.2]

/-- Complete interval computation for depth 15, residue 10500. -/
theorem bounds_15_10500 : exactInterval 15 10500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10500 : oddCount 10500 15 = 4 ∧ acceleratedOrbit 15 10500 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10500) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10500.1, data_15_10500.2]

/-- Complete interval computation for depth 15, residue 10501. -/
theorem bounds_15_10501 : exactInterval 15 10501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10501 : oddCount 10501 15 = 4 ∧ acceleratedOrbit 15 10501 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10501) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10501.1, data_15_10501.2]

/-- Complete interval computation for depth 15, residue 10502. -/
theorem bounds_15_10502 : exactInterval 15 10502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10502 : oddCount 10502 15 = 4 ∧ acceleratedOrbit 15 10502 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10502) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10502.1, data_15_10502.2]

/-- Complete interval computation for depth 15, residue 10503. -/
theorem bounds_15_10503 : exactInterval 15 10503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10503 : oddCount 10503 15 = 9 ∧ acceleratedOrbit 15 10503 = 6311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10503) = 3 ^ 9 * m + 6311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10503.1, data_15_10503.2]

/-- Complete interval computation for depth 15, residue 10504. -/
theorem bounds_15_10504 : exactInterval 15 10504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10504 : oddCount 10504 15 = 4 ∧ acceleratedOrbit 15 10504 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10504) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10504.1, data_15_10504.2]

/-- Complete interval computation for depth 15, residue 10505. -/
theorem bounds_15_10505 : exactInterval 15 10505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10505 : oddCount 10505 15 = 8 ∧ acceleratedOrbit 15 10505 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10505) = 3 ^ 8 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10505.1, data_15_10505.2]

/-- Complete interval computation for depth 15, residue 10506. -/
theorem bounds_15_10506 : exactInterval 15 10506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10506 : oddCount 10506 15 = 4 ∧ acceleratedOrbit 15 10506 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10506) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10506.1, data_15_10506.2]

/-- Complete interval computation for depth 15, residue 10507. -/
theorem bounds_15_10507 : exactInterval 15 10507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10507 : oddCount 10507 15 = 9 ∧ acceleratedOrbit 15 10507 = 6317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10507) = 3 ^ 9 * m + 6317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10507.1, data_15_10507.2]

/-- Complete interval computation for depth 15, residue 10508. -/
theorem bounds_15_10508 : exactInterval 15 10508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10508 : oddCount 10508 15 = 4 ∧ acceleratedOrbit 15 10508 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10508) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10508.1, data_15_10508.2]

/-- Complete interval computation for depth 15, residue 10509. -/
theorem bounds_15_10509 : exactInterval 15 10509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10509 : oddCount 10509 15 = 4 ∧ acceleratedOrbit 15 10509 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10509) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10509.1, data_15_10509.2]

/-- Complete interval computation for depth 15, residue 10510. -/
theorem bounds_15_10510 : exactInterval 15 10510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10510 : oddCount 10510 15 = 10 ∧ acceleratedOrbit 15 10510 = 18953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10510) = 3 ^ 10 * m + 18953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10510.1, data_15_10510.2]

/-- Complete interval computation for depth 15, residue 10511. -/
theorem bounds_15_10511 : exactInterval 15 10511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10511 : oddCount 10511 15 = 10 ∧ acceleratedOrbit 15 10511 = 18953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10511) = 3 ^ 10 * m + 18953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10511.1, data_15_10511.2]

/-- Complete interval computation for depth 15, residue 10512. -/
theorem bounds_15_10512 : exactInterval 15 10512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10512 : oddCount 10512 15 = 6 ∧ acceleratedOrbit 15 10512 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10512) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10512.1, data_15_10512.2]

/-- Complete interval computation for depth 15, residue 10513. -/
theorem bounds_15_10513 : exactInterval 15 10513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10513 : oddCount 10513 15 = 4 ∧ acceleratedOrbit 15 10513 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10513) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10513.1, data_15_10513.2]

/-- Complete interval computation for depth 15, residue 10514. -/
theorem bounds_15_10514 : exactInterval 15 10514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10514 : oddCount 10514 15 = 12 ∧ acceleratedOrbit 15 10514 = 170585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10514) = 3 ^ 12 * m + 170585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10514.1, data_15_10514.2]

/-- Complete interval computation for depth 15, residue 10515. -/
theorem bounds_15_10515 : exactInterval 15 10515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10515 : oddCount 10515 15 = 12 ∧ acceleratedOrbit 15 10515 = 170585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10515) = 3 ^ 12 * m + 170585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10515.1, data_15_10515.2]

/-- Complete interval computation for depth 15, residue 10516. -/
theorem bounds_15_10516 : exactInterval 15 10516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10516 : oddCount 10516 15 = 6 ∧ acceleratedOrbit 15 10516 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10516) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10516.1, data_15_10516.2]

/-- Complete interval computation for depth 15, residue 10517. -/
theorem bounds_15_10517 : exactInterval 15 10517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10517 : oddCount 10517 15 = 6 ∧ acceleratedOrbit 15 10517 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10517) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10517.1, data_15_10517.2]

end Collatz.Research.PassageAtlas.Batch0321
