import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0033

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 491. -/
theorem bounds_10_491 : exactInterval 10 491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_491 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 491) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_491 : oddCount 491 10 = 8 ∧ acceleratedOrbit 10 491 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_491 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 491) = 3 ^ 8 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_491.1, data_10_491.2]

/-- Complete interval computation for depth 10, residue 492. -/
theorem bounds_10_492 : exactInterval 10 492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_492 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 492) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_492 : oddCount 492 10 = 5 ∧ acceleratedOrbit 10 492 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_492 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 492) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_492.1, data_10_492.2]

/-- Complete interval computation for depth 10, residue 493. -/
theorem bounds_10_493 : exactInterval 10 493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_493 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 493) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_493 : oddCount 493 10 = 5 ∧ acceleratedOrbit 10 493 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_493 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 493) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_493.1, data_10_493.2]

/-- Complete interval computation for depth 10, residue 494. -/
theorem bounds_10_494 : exactInterval 10 494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_494 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 494) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_494 : oddCount 494 10 = 5 ∧ acceleratedOrbit 10 494 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_494 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 494) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_494.1, data_10_494.2]

/-- Complete interval computation for depth 10, residue 495. -/
theorem bounds_10_495 : exactInterval 10 495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_495 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 495) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_495 : oddCount 495 10 = 8 ∧ acceleratedOrbit 10 495 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_495 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 495) = 3 ^ 8 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_495.1, data_10_495.2]

/-- Complete interval computation for depth 10, residue 496. -/
theorem bounds_10_496 : exactInterval 10 496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_496 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 496) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_496 : oddCount 496 10 = 5 ∧ acceleratedOrbit 10 496 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_496 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 496) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_496.1, data_10_496.2]

/-- Complete interval computation for depth 10, residue 497. -/
theorem bounds_10_497 : exactInterval 10 497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_497 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 497) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_497 : oddCount 497 10 = 4 ∧ acceleratedOrbit 10 497 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_497 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 497) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_497.1, data_10_497.2]

/-- Complete interval computation for depth 10, residue 498. -/
theorem bounds_10_498 : exactInterval 10 498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_498 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 498) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_498 : oddCount 498 10 = 5 ∧ acceleratedOrbit 10 498 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_498 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 498) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_498.1, data_10_498.2]

/-- Complete interval computation for depth 10, residue 499. -/
theorem bounds_10_499 : exactInterval 10 499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_499 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 499) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_499 : oddCount 499 10 = 5 ∧ acceleratedOrbit 10 499 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_499 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 499) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_499.1, data_10_499.2]

/-- Complete interval computation for depth 10, residue 500. -/
theorem bounds_10_500 : exactInterval 10 500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_500 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 500) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_500 : oddCount 500 10 = 5 ∧ acceleratedOrbit 10 500 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_500 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 500) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_500.1, data_10_500.2]

/-- Complete interval computation for depth 10, residue 501. -/
theorem bounds_10_501 : exactInterval 10 501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_501 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 501) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_501 : oddCount 501 10 = 5 ∧ acceleratedOrbit 10 501 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_501 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 501) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_501.1, data_10_501.2]

/-- Complete interval computation for depth 10, residue 502. -/
theorem bounds_10_502 : exactInterval 10 502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_502 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 502) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_502 : oddCount 502 10 = 7 ∧ acceleratedOrbit 10 502 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_502 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 502) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_502.1, data_10_502.2]

/-- Complete interval computation for depth 10, residue 503. -/
theorem bounds_10_503 : exactInterval 10 503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_503 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 503) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_503 : oddCount 503 10 = 7 ∧ acceleratedOrbit 10 503 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_503 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 503) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_503.1, data_10_503.2]

/-- Complete interval computation for depth 10, residue 504. -/
theorem bounds_10_504 : exactInterval 10 504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_504 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 504) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_504 : oddCount 504 10 = 6 ∧ acceleratedOrbit 10 504 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_504 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 504) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_504.1, data_10_504.2]

/-- Complete interval computation for depth 10, residue 505. -/
theorem bounds_10_505 : exactInterval 10 505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_505 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 505) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_505 : oddCount 505 10 = 6 ∧ acceleratedOrbit 10 505 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_505 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 505) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_505.1, data_10_505.2]

end Collatz.Research.StoppingAtlas.Batch0033
