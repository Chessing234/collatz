import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0100

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 496. -/
theorem bounds_11_496 : exactInterval 11 496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_496 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 496) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_496 : oddCount 496 11 = 6 ∧ acceleratedOrbit 11 496 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_496 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 496) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_496.1, data_11_496.2]

/-- Complete interval computation for depth 11, residue 497. -/
theorem bounds_11_497 : exactInterval 11 497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_497 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 497) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_497 : oddCount 497 11 = 4 ∧ acceleratedOrbit 11 497 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_497 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 497) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_497.1, data_11_497.2]

/-- Complete interval computation for depth 11, residue 498. -/
theorem bounds_11_498 : exactInterval 11 498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_498 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 498) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_498 : oddCount 498 11 = 6 ∧ acceleratedOrbit 11 498 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_498 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 498) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_498.1, data_11_498.2]

/-- Complete interval computation for depth 11, residue 499. -/
theorem bounds_11_499 : exactInterval 11 499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_499 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 499) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_499 : oddCount 499 11 = 6 ∧ acceleratedOrbit 11 499 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_499 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 499) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_499.1, data_11_499.2]

/-- Complete interval computation for depth 11, residue 500. -/
theorem bounds_11_500 : exactInterval 11 500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_500 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 500) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_500 : oddCount 500 11 = 6 ∧ acceleratedOrbit 11 500 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_500 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 500) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_500.1, data_11_500.2]

/-- Complete interval computation for depth 11, residue 501. -/
theorem bounds_11_501 : exactInterval 11 501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_501 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 501) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_501 : oddCount 501 11 = 6 ∧ acceleratedOrbit 11 501 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_501 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 501) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_501.1, data_11_501.2]

/-- Complete interval computation for depth 11, residue 502. -/
theorem bounds_11_502 : exactInterval 11 502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_502 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 502) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_502 : oddCount 502 11 = 8 ∧ acceleratedOrbit 11 502 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_502 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 502) = 3 ^ 8 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_502.1, data_11_502.2]

/-- Complete interval computation for depth 11, residue 503. -/
theorem bounds_11_503 : exactInterval 11 503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_503 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 503) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_503 : oddCount 503 11 = 8 ∧ acceleratedOrbit 11 503 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_503 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 503) = 3 ^ 8 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_503.1, data_11_503.2]

/-- Complete interval computation for depth 11, residue 504. -/
theorem bounds_11_504 : exactInterval 11 504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_504 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 504) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_504 : oddCount 504 11 = 6 ∧ acceleratedOrbit 11 504 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_504 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 504) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_504.1, data_11_504.2]

/-- Complete interval computation for depth 11, residue 505. -/
theorem bounds_11_505 : exactInterval 11 505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_505 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 505) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_505 : oddCount 505 11 = 7 ∧ acceleratedOrbit 11 505 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_505 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 505) = 3 ^ 7 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_505.1, data_11_505.2]

/-- Complete interval computation for depth 11, residue 506. -/
theorem bounds_11_506 : exactInterval 11 506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_506 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 506) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_506 : oddCount 506 11 = 6 ∧ acceleratedOrbit 11 506 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_506 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 506) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_506.1, data_11_506.2]

/-- Complete interval computation for depth 11, residue 507. -/
theorem bounds_11_507 : exactInterval 11 507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_507 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 507) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_507 : oddCount 507 11 = 6 ∧ acceleratedOrbit 11 507 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_507 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 507) = 3 ^ 6 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_507.1, data_11_507.2]

/-- Complete interval computation for depth 11, residue 508. -/
theorem bounds_11_508 : exactInterval 11 508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_508 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 508) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_508 : oddCount 508 11 = 8 ∧ acceleratedOrbit 11 508 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_508 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 508) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_508.1, data_11_508.2]

/-- Complete interval computation for depth 11, residue 509. -/
theorem bounds_11_509 : exactInterval 11 509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_509 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 509) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_509 : oddCount 509 11 = 8 ∧ acceleratedOrbit 11 509 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_509 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 509) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_509.1, data_11_509.2]

/-- Complete interval computation for depth 11, residue 510. -/
theorem bounds_11_510 : exactInterval 11 510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_510 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 510) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_510 : oddCount 510 11 = 8 ∧ acceleratedOrbit 11 510 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_510 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 510) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_510.1, data_11_510.2]

/-- Complete interval computation for depth 11, residue 511. -/
theorem bounds_11_511 : exactInterval 11 511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_511 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 511) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_511 : oddCount 511 11 = 10 ∧ acceleratedOrbit 11 511 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_511 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 511) = 3 ^ 10 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_511.1, data_11_511.2]

end Collatz.Research.StoppingAtlas.Batch0100
