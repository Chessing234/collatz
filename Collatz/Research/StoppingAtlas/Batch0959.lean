import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0959

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7546. -/
theorem bounds_13_7546 : exactInterval 13 7546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7546 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7546) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7546 : oddCount 7546 13 = 5 ∧ acceleratedOrbit 13 7546 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7546 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7546) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7546.1, data_13_7546.2]

/-- Complete interval computation for depth 13, residue 7547. -/
theorem bounds_13_7547 : exactInterval 13 7547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7547 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7547) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7547 : oddCount 7547 13 = 8 ∧ acceleratedOrbit 13 7547 = 6047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7547 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7547) = 3 ^ 8 * m + 6047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7547.1, data_13_7547.2]

/-- Complete interval computation for depth 13, residue 7548. -/
theorem bounds_13_7548 : exactInterval 13 7548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7548 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7548) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7548 : oddCount 7548 13 = 5 ∧ acceleratedOrbit 13 7548 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7548 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7548) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7548.1, data_13_7548.2]

/-- Complete interval computation for depth 13, residue 7549. -/
theorem bounds_13_7549 : exactInterval 13 7549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7549 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7549) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7549 : oddCount 7549 13 = 5 ∧ acceleratedOrbit 13 7549 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7549 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7549) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7549.1, data_13_7549.2]

/-- Complete interval computation for depth 13, residue 7550. -/
theorem bounds_13_7550 : exactInterval 13 7550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7550 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7550) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7550 : oddCount 7550 13 = 9 ∧ acceleratedOrbit 13 7550 = 18146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7550 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7550) = 3 ^ 9 * m + 18146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7550.1, data_13_7550.2]

/-- Complete interval computation for depth 13, residue 7551. -/
theorem bounds_13_7551 : exactInterval 13 7551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7551 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7551) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7551 : oddCount 7551 13 = 9 ∧ acceleratedOrbit 13 7551 = 18146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7551 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7551) = 3 ^ 9 * m + 18146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7551.1, data_13_7551.2]

/-- Complete interval computation for depth 13, residue 7552. -/
theorem bounds_13_7552 : exactInterval 13 7552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7552 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7552) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7552 : oddCount 7552 13 = 4 ∧ acceleratedOrbit 13 7552 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7552 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7552) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7552.1, data_13_7552.2]

/-- Complete interval computation for depth 13, residue 7553. -/
theorem bounds_13_7553 : exactInterval 13 7553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7553 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7553) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7553 : oddCount 7553 13 = 7 ∧ acceleratedOrbit 13 7553 = 2018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7553 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7553) = 3 ^ 7 * m + 2018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7553.1, data_13_7553.2]

/-- Complete interval computation for depth 13, residue 7554. -/
theorem bounds_13_7554 : exactInterval 13 7554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7554 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7554) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7554 : oddCount 7554 13 = 6 ∧ acceleratedOrbit 13 7554 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7554 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7554) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7554.1, data_13_7554.2]

/-- Complete interval computation for depth 13, residue 7555. -/
theorem bounds_13_7555 : exactInterval 13 7555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7555 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7555) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7555 : oddCount 7555 13 = 6 ∧ acceleratedOrbit 13 7555 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7555 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7555) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7555.1, data_13_7555.2]

/-- Complete interval computation for depth 13, residue 7556. -/
theorem bounds_13_7556 : exactInterval 13 7556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7556 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7556) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7556 : oddCount 7556 13 = 7 ∧ acceleratedOrbit 13 7556 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7556 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7556) = 3 ^ 7 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7556.1, data_13_7556.2]

/-- Complete interval computation for depth 13, residue 7557. -/
theorem bounds_13_7557 : exactInterval 13 7557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7557 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7557) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7557 : oddCount 7557 13 = 7 ∧ acceleratedOrbit 13 7557 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7557 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7557) = 3 ^ 7 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7557.1, data_13_7557.2]

/-- Complete interval computation for depth 13, residue 7558. -/
theorem bounds_13_7558 : exactInterval 13 7558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7558 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7558) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7558 : oddCount 7558 13 = 7 ∧ acceleratedOrbit 13 7558 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7558 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7558) = 3 ^ 7 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7558.1, data_13_7558.2]

/-- Complete interval computation for depth 13, residue 7559. -/
theorem bounds_13_7559 : exactInterval 13 7559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7559 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7559) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7559 : oddCount 7559 13 = 6 ∧ acceleratedOrbit 13 7559 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7559 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7559) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7559.1, data_13_7559.2]

/-- Complete interval computation for depth 13, residue 7560. -/
theorem bounds_13_7560 : exactInterval 13 7560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7560 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7560) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7560 : oddCount 7560 13 = 3 ∧ acceleratedOrbit 13 7560 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7560 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7560) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7560.1, data_13_7560.2]

/-- Complete interval computation for depth 13, residue 7561. -/
theorem bounds_13_7561 : exactInterval 13 7561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7561 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7561) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7561 : oddCount 7561 13 = 6 ∧ acceleratedOrbit 13 7561 = 673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7561 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7561) = 3 ^ 6 * m + 673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7561.1, data_13_7561.2]

end Collatz.Research.StoppingAtlas.Batch0959
