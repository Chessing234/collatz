import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0500

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 496. -/
theorem bounds_13_496 : exactInterval 13 496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_496 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 496) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_496 : oddCount 496 13 = 7 ∧ acceleratedOrbit 13 496 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_496 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 496) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_496.1, data_13_496.2]

/-- Complete interval computation for depth 13, residue 497. -/
theorem bounds_13_497 : exactInterval 13 497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_497 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 497) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_497 : oddCount 497 13 = 4 ∧ acceleratedOrbit 13 497 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_497 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 497) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_497.1, data_13_497.2]

/-- Complete interval computation for depth 13, residue 498. -/
theorem bounds_13_498 : exactInterval 13 498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_498 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 498) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_498 : oddCount 498 13 = 8 ∧ acceleratedOrbit 13 498 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_498 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 498) = 3 ^ 8 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_498.1, data_13_498.2]

/-- Complete interval computation for depth 13, residue 499. -/
theorem bounds_13_499 : exactInterval 13 499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_499 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 499) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_499 : oddCount 499 13 = 8 ∧ acceleratedOrbit 13 499 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_499 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 499) = 3 ^ 8 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_499.1, data_13_499.2]

/-- Complete interval computation for depth 13, residue 500. -/
theorem bounds_13_500 : exactInterval 13 500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_500 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 500) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_500 : oddCount 500 13 = 7 ∧ acceleratedOrbit 13 500 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_500 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 500) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_500.1, data_13_500.2]

/-- Complete interval computation for depth 13, residue 501. -/
theorem bounds_13_501 : exactInterval 13 501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_501 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 501) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_501 : oddCount 501 13 = 7 ∧ acceleratedOrbit 13 501 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_501 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 501) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_501.1, data_13_501.2]

/-- Complete interval computation for depth 13, residue 502. -/
theorem bounds_13_502 : exactInterval 13 502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_502 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 502) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_502 : oddCount 502 13 = 10 ∧ acceleratedOrbit 13 502 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_502 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 502) = 3 ^ 10 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_502.1, data_13_502.2]

/-- Complete interval computation for depth 13, residue 503. -/
theorem bounds_13_503 : exactInterval 13 503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_503 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 503) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_503 : oddCount 503 13 = 10 ∧ acceleratedOrbit 13 503 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_503 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 503) = 3 ^ 10 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_503.1, data_13_503.2]

/-- Complete interval computation for depth 13, residue 504. -/
theorem bounds_13_504 : exactInterval 13 504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_504 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 504) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_504 : oddCount 504 13 = 7 ∧ acceleratedOrbit 13 504 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_504 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 504) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_504.1, data_13_504.2]

/-- Complete interval computation for depth 13, residue 505. -/
theorem bounds_13_505 : exactInterval 13 505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_505 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 505) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_505 : oddCount 505 13 = 8 ∧ acceleratedOrbit 13 505 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_505 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 505) = 3 ^ 8 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_505.1, data_13_505.2]

/-- Complete interval computation for depth 13, residue 506. -/
theorem bounds_13_506 : exactInterval 13 506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_506 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 506) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_506 : oddCount 506 13 = 7 ∧ acceleratedOrbit 13 506 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_506 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 506) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_506.1, data_13_506.2]

/-- Complete interval computation for depth 13, residue 507. -/
theorem bounds_13_507 : exactInterval 13 507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_507 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 507) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_507 : oddCount 507 13 = 7 ∧ acceleratedOrbit 13 507 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_507 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 507) = 3 ^ 7 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_507.1, data_13_507.2]

/-- Complete interval computation for depth 13, residue 508. -/
theorem bounds_13_508 : exactInterval 13 508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_508 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 508) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_508 : oddCount 508 13 = 8 ∧ acceleratedOrbit 13 508 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_508 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 508) = 3 ^ 8 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_508.1, data_13_508.2]

/-- Complete interval computation for depth 13, residue 509. -/
theorem bounds_13_509 : exactInterval 13 509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_509 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 509) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_509 : oddCount 509 13 = 8 ∧ acceleratedOrbit 13 509 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_509 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 509) = 3 ^ 8 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_509.1, data_13_509.2]

/-- Complete interval computation for depth 13, residue 510. -/
theorem bounds_13_510 : exactInterval 13 510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_510 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 510) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_510 : oddCount 510 13 = 8 ∧ acceleratedOrbit 13 510 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_510 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 510) = 3 ^ 8 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_510.1, data_13_510.2]

/-- Complete interval computation for depth 13, residue 511. -/
theorem bounds_13_511 : exactInterval 13 511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_511 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 511) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_511 : oddCount 511 13 = 11 ∧ acceleratedOrbit 13 511 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_511 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 511) = 3 ^ 11 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_511.1, data_13_511.2]

end Collatz.Research.StoppingAtlas.Batch0500
