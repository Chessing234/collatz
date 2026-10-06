import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch100

/-- Complete interval computation for depth 9, residue 501. -/
theorem bounds_9_501 : exactInterval 9 501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_501 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 501) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_501 : oddCount 501 9 = 5 ∧ acceleratedOrbit 9 501 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_501 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 501) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_501.1, data_9_501.2]

/-- Complete interval computation for depth 9, residue 502. -/
theorem bounds_9_502 : exactInterval 9 502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_502 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 502) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_502 : oddCount 502 9 = 6 ∧ acceleratedOrbit 9 502 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_502 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 502) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_502.1, data_9_502.2]

/-- Complete interval computation for depth 9, residue 503. -/
theorem bounds_9_503 : exactInterval 9 503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_503 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 503) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_503 : oddCount 503 9 = 6 ∧ acceleratedOrbit 9 503 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_503 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 503) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_503.1, data_9_503.2]

/-- Complete interval computation for depth 9, residue 504. -/
theorem bounds_9_504 : exactInterval 9 504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_504 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 504) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_504 : oddCount 504 9 = 6 ∧ acceleratedOrbit 9 504 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_504 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 504) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_504.1, data_9_504.2]

/-- Complete interval computation for depth 9, residue 505. -/
theorem bounds_9_505 : exactInterval 9 505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_505 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 505) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_505 : oddCount 505 9 = 6 ∧ acceleratedOrbit 9 505 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_505 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 505) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_505.1, data_9_505.2]

/-- Complete interval computation for depth 9, residue 506. -/
theorem bounds_9_506 : exactInterval 9 506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_506 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 506) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_506 : oddCount 506 9 = 6 ∧ acceleratedOrbit 9 506 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_506 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 506) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_506.1, data_9_506.2]

/-- Complete interval computation for depth 9, residue 507. -/
theorem bounds_9_507 : exactInterval 9 507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_507 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 507) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_507 : oddCount 507 9 = 6 ∧ acceleratedOrbit 9 507 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_507 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 507) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_507.1, data_9_507.2]

/-- Complete interval computation for depth 9, residue 508. -/
theorem bounds_9_508 : exactInterval 9 508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_508 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 508) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_508 : oddCount 508 9 = 7 ∧ acceleratedOrbit 9 508 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_508 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 508) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_508.1, data_9_508.2]

/-- Complete interval computation for depth 9, residue 509. -/
theorem bounds_9_509 : exactInterval 9 509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_509 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 509) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_509 : oddCount 509 9 = 7 ∧ acceleratedOrbit 9 509 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_509 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 509) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_509.1, data_9_509.2]

/-- Complete interval computation for depth 9, residue 510. -/
theorem bounds_9_510 : exactInterval 9 510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_510 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 510) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_510 : oddCount 510 9 = 8 ∧ acceleratedOrbit 9 510 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_510 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 510) = 3 ^ 8 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_510.1, data_9_510.2]

/-- Complete interval computation for depth 9, residue 511. -/
theorem bounds_9_511 : exactInterval 9 511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_511 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 511) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_511 : oddCount 511 9 = 9 ∧ acceleratedOrbit 9 511 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_511 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 511) = 3 ^ 9 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_511.1, data_9_511.2]

end Collatz.Research.DescentIntervals.Batch100
