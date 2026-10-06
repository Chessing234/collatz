import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch099

/-- Complete interval computation for depth 9, residue 491. -/
theorem bounds_9_491 : exactInterval 9 491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_491 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 491) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_491 : oddCount 491 9 = 7 ∧ acceleratedOrbit 9 491 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_491 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 491) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_491.1, data_9_491.2]

/-- Complete interval computation for depth 9, residue 492. -/
theorem bounds_9_492 : exactInterval 9 492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_492 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 492) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_492 : oddCount 492 9 = 5 ∧ acceleratedOrbit 9 492 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_492 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 492) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_492.1, data_9_492.2]

/-- Complete interval computation for depth 9, residue 493. -/
theorem bounds_9_493 : exactInterval 9 493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_493 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 493) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_493 : oddCount 493 9 = 5 ∧ acceleratedOrbit 9 493 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_493 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 493) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_493.1, data_9_493.2]

/-- Complete interval computation for depth 9, residue 494. -/
theorem bounds_9_494 : exactInterval 9 494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_494 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 494) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_494 : oddCount 494 9 = 5 ∧ acceleratedOrbit 9 494 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_494 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 494) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_494.1, data_9_494.2]

/-- Complete interval computation for depth 9, residue 495. -/
theorem bounds_9_495 : exactInterval 9 495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_495 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 495) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_495 : oddCount 495 9 = 7 ∧ acceleratedOrbit 9 495 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_495 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 495) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_495.1, data_9_495.2]

/-- Complete interval computation for depth 9, residue 496. -/
theorem bounds_9_496 : exactInterval 9 496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_496 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 496) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_496 : oddCount 496 9 = 5 ∧ acceleratedOrbit 9 496 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_496 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 496) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_496.1, data_9_496.2]

/-- Complete interval computation for depth 9, residue 497. -/
theorem bounds_9_497 : exactInterval 9 497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_497 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 497) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_497 : oddCount 497 9 = 4 ∧ acceleratedOrbit 9 497 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_497 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 497) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_497.1, data_9_497.2]

/-- Complete interval computation for depth 9, residue 498. -/
theorem bounds_9_498 : exactInterval 9 498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_498 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 498) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_498 : oddCount 498 9 = 5 ∧ acceleratedOrbit 9 498 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_498 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 498) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_498.1, data_9_498.2]

/-- Complete interval computation for depth 9, residue 499. -/
theorem bounds_9_499 : exactInterval 9 499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_499 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 499) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_499 : oddCount 499 9 = 5 ∧ acceleratedOrbit 9 499 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_499 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 499) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_499.1, data_9_499.2]

/-- Complete interval computation for depth 9, residue 500. -/
theorem bounds_9_500 : exactInterval 9 500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_500 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 500) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_500 : oddCount 500 9 = 5 ∧ acceleratedOrbit 9 500 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_500 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 500) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_500.1, data_9_500.2]

end Collatz.Research.DescentIntervals.Batch099
