import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0700

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3568. -/
theorem bounds_13_3568 : exactInterval 13 3568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3568 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3568) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3568 : oddCount 3568 13 = 6 ∧ acceleratedOrbit 13 3568 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3568 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3568) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3568.1, data_13_3568.2]

/-- Complete interval computation for depth 13, residue 3569. -/
theorem bounds_13_3569 : exactInterval 13 3569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3569 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3569) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3569 : oddCount 3569 13 = 6 ∧ acceleratedOrbit 13 3569 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3569 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3569) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3569.1, data_13_3569.2]

/-- Complete interval computation for depth 13, residue 3570. -/
theorem bounds_13_3570 : exactInterval 13 3570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3570 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3570) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3570 : oddCount 3570 13 = 5 ∧ acceleratedOrbit 13 3570 = 106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3570 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3570) = 3 ^ 5 * m + 106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3570.1, data_13_3570.2]

/-- Complete interval computation for depth 13, residue 3571. -/
theorem bounds_13_3571 : exactInterval 13 3571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3571 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3571) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3571 : oddCount 3571 13 = 5 ∧ acceleratedOrbit 13 3571 = 106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3571 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3571) = 3 ^ 5 * m + 106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3571.1, data_13_3571.2]

/-- Complete interval computation for depth 13, residue 3572. -/
theorem bounds_13_3572 : exactInterval 13 3572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3572 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3572) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3572 : oddCount 3572 13 = 6 ∧ acceleratedOrbit 13 3572 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3572 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3572) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3572.1, data_13_3572.2]

/-- Complete interval computation for depth 13, residue 3573. -/
theorem bounds_13_3573 : exactInterval 13 3573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3573 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3573) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3573 : oddCount 3573 13 = 6 ∧ acceleratedOrbit 13 3573 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3573 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3573) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3573.1, data_13_3573.2]

/-- Complete interval computation for depth 13, residue 3574. -/
theorem bounds_13_3574 : exactInterval 13 3574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3574 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3574) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3574 : oddCount 3574 13 = 7 ∧ acceleratedOrbit 13 3574 = 955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3574 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3574) = 3 ^ 7 * m + 955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3574.1, data_13_3574.2]

/-- Complete interval computation for depth 13, residue 3575. -/
theorem bounds_13_3575 : exactInterval 13 3575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3575 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3575) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3575 : oddCount 3575 13 = 7 ∧ acceleratedOrbit 13 3575 = 955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3575 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3575) = 3 ^ 7 * m + 955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3575.1, data_13_3575.2]

/-- Complete interval computation for depth 13, residue 3576. -/
theorem bounds_13_3576 : exactInterval 13 3576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3576 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3576) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3576 : oddCount 3576 13 = 9 ∧ acceleratedOrbit 13 3576 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3576 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3576) = 3 ^ 9 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3576.1, data_13_3576.2]

/-- Complete interval computation for depth 13, residue 3577. -/
theorem bounds_13_3577 : exactInterval 13 3577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3577 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3577) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3577 : oddCount 3577 13 = 7 ∧ acceleratedOrbit 13 3577 = 956 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3577 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3577) = 3 ^ 7 * m + 956 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3577.1, data_13_3577.2]

/-- Complete interval computation for depth 13, residue 3578. -/
theorem bounds_13_3578 : exactInterval 13 3578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3578 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3578) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3578 : oddCount 3578 13 = 9 ∧ acceleratedOrbit 13 3578 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3578 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3578) = 3 ^ 9 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3578.1, data_13_3578.2]

/-- Complete interval computation for depth 13, residue 3579. -/
theorem bounds_13_3579 : exactInterval 13 3579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3579 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3579) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3579 : oddCount 3579 13 = 7 ∧ acceleratedOrbit 13 3579 = 956 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3579 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3579) = 3 ^ 7 * m + 956 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3579.1, data_13_3579.2]

/-- Complete interval computation for depth 13, residue 3580. -/
theorem bounds_13_3580 : exactInterval 13 3580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3580 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3580) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3580 : oddCount 3580 13 = 9 ∧ acceleratedOrbit 13 3580 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3580 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3580) = 3 ^ 9 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3580.1, data_13_3580.2]

/-- Complete interval computation for depth 13, residue 3581. -/
theorem bounds_13_3581 : exactInterval 13 3581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3581 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3581) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3581 : oddCount 3581 13 = 9 ∧ acceleratedOrbit 13 3581 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3581 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3581) = 3 ^ 9 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3581.1, data_13_3581.2]

/-- Complete interval computation for depth 13, residue 3582. -/
theorem bounds_13_3582 : exactInterval 13 3582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3582 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3582) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3582 : oddCount 3582 13 = 10 ∧ acceleratedOrbit 13 3582 = 25834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3582 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3582) = 3 ^ 10 * m + 25834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3582.1, data_13_3582.2]

/-- Complete interval computation for depth 13, residue 3583. -/
theorem bounds_13_3583 : exactInterval 13 3583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3583 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3583) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3583 : oddCount 3583 13 = 10 ∧ acceleratedOrbit 13 3583 = 25834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3583 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3583) = 3 ^ 10 * m + 25834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3583.1, data_13_3583.2]

end Collatz.Research.StoppingAtlas.Batch0700
