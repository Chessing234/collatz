import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0233

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 491. -/
theorem bounds_12_491 : exactInterval 12 491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_491 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 491) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_491 : oddCount 491 12 = 9 ∧ acceleratedOrbit 12 491 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_491 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 491) = 3 ^ 9 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_491.1, data_12_491.2]

/-- Complete interval computation for depth 12, residue 492. -/
theorem bounds_12_492 : exactInterval 12 492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_492 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 492) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_492 : oddCount 492 12 = 6 ∧ acceleratedOrbit 12 492 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_492 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 492) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_492.1, data_12_492.2]

/-- Complete interval computation for depth 12, residue 493. -/
theorem bounds_12_493 : exactInterval 12 493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_493 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 493) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_493 : oddCount 493 12 = 6 ∧ acceleratedOrbit 12 493 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_493 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 493) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_493.1, data_12_493.2]

/-- Complete interval computation for depth 12, residue 494. -/
theorem bounds_12_494 : exactInterval 12 494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_494 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 494) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_494 : oddCount 494 12 = 6 ∧ acceleratedOrbit 12 494 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_494 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 494) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_494.1, data_12_494.2]

/-- Complete interval computation for depth 12, residue 495. -/
theorem bounds_12_495 : exactInterval 12 495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_495 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 495) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_495 : oddCount 495 12 = 10 ∧ acceleratedOrbit 12 495 = 7154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_495 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 495) = 3 ^ 10 * m + 7154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_495.1, data_12_495.2]

/-- Complete interval computation for depth 12, residue 496. -/
theorem bounds_12_496 : exactInterval 12 496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_496 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 496) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_496 : oddCount 496 12 = 6 ∧ acceleratedOrbit 12 496 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_496 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 496) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_496.1, data_12_496.2]

/-- Complete interval computation for depth 12, residue 497. -/
theorem bounds_12_497 : exactInterval 12 497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_497 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 497) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_497 : oddCount 497 12 = 4 ∧ acceleratedOrbit 12 497 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_497 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 497) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_497.1, data_12_497.2]

/-- Complete interval computation for depth 12, residue 498. -/
theorem bounds_12_498 : exactInterval 12 498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_498 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 498) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_498 : oddCount 498 12 = 7 ∧ acceleratedOrbit 12 498 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_498 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 498) = 3 ^ 7 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_498.1, data_12_498.2]

/-- Complete interval computation for depth 12, residue 499. -/
theorem bounds_12_499 : exactInterval 12 499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_499 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 499) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_499 : oddCount 499 12 = 7 ∧ acceleratedOrbit 12 499 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_499 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 499) = 3 ^ 7 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_499.1, data_12_499.2]

/-- Complete interval computation for depth 12, residue 500. -/
theorem bounds_12_500 : exactInterval 12 500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_500 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 500) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_500 : oddCount 500 12 = 6 ∧ acceleratedOrbit 12 500 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_500 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 500) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_500.1, data_12_500.2]

/-- Complete interval computation for depth 12, residue 501. -/
theorem bounds_12_501 : exactInterval 12 501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_501 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 501) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_501 : oddCount 501 12 = 6 ∧ acceleratedOrbit 12 501 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_501 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 501) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_501.1, data_12_501.2]

/-- Complete interval computation for depth 12, residue 502. -/
theorem bounds_12_502 : exactInterval 12 502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_502 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 502) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_502 : oddCount 502 12 = 9 ∧ acceleratedOrbit 12 502 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_502 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 502) = 3 ^ 9 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_502.1, data_12_502.2]

/-- Complete interval computation for depth 12, residue 503. -/
theorem bounds_12_503 : exactInterval 12 503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_503 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 503) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_503 : oddCount 503 12 = 9 ∧ acceleratedOrbit 12 503 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_503 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 503) = 3 ^ 9 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_503.1, data_12_503.2]

/-- Complete interval computation for depth 12, residue 504. -/
theorem bounds_12_504 : exactInterval 12 504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_504 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 504) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_504 : oddCount 504 12 = 6 ∧ acceleratedOrbit 12 504 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_504 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 504) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_504.1, data_12_504.2]

/-- Complete interval computation for depth 12, residue 505. -/
theorem bounds_12_505 : exactInterval 12 505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_505 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 505) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_505 : oddCount 505 12 = 7 ∧ acceleratedOrbit 12 505 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_505 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 505) = 3 ^ 7 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_505.1, data_12_505.2]

end Collatz.Research.StoppingAtlas.Batch0233
