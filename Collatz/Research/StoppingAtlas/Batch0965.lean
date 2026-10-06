import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0965

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7639. -/
theorem bounds_13_7639 : exactInterval 13 7639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7639 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7639) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7639 : oddCount 7639 13 = 6 ∧ acceleratedOrbit 13 7639 = 680 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7639 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7639) = 3 ^ 6 * m + 680 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7639.1, data_13_7639.2]

/-- Complete interval computation for depth 13, residue 7640. -/
theorem bounds_13_7640 : exactInterval 13 7640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7640 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7640) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7640 : oddCount 7640 13 = 5 ∧ acceleratedOrbit 13 7640 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7640 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7640) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7640.1, data_13_7640.2]

/-- Complete interval computation for depth 13, residue 7641. -/
theorem bounds_13_7641 : exactInterval 13 7641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7641 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7641) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7641 : oddCount 7641 13 = 5 ∧ acceleratedOrbit 13 7641 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7641 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7641) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7641.1, data_13_7641.2]

/-- Complete interval computation for depth 13, residue 7642. -/
theorem bounds_13_7642 : exactInterval 13 7642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7642 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7642) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7642 : oddCount 7642 13 = 5 ∧ acceleratedOrbit 13 7642 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7642 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7642) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7642.1, data_13_7642.2]

/-- Complete interval computation for depth 13, residue 7643. -/
theorem bounds_13_7643 : exactInterval 13 7643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7643 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7643) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7643 : oddCount 7643 13 = 7 ∧ acceleratedOrbit 13 7643 = 2042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7643 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7643) = 3 ^ 7 * m + 2042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7643.1, data_13_7643.2]

/-- Complete interval computation for depth 13, residue 7644. -/
theorem bounds_13_7644 : exactInterval 13 7644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7644 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7644) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7644 : oddCount 7644 13 = 5 ∧ acceleratedOrbit 13 7644 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7644 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7644) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7644.1, data_13_7644.2]

/-- Complete interval computation for depth 13, residue 7645. -/
theorem bounds_13_7645 : exactInterval 13 7645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7645 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7645) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7645 : oddCount 7645 13 = 5 ∧ acceleratedOrbit 13 7645 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7645 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7645) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7645.1, data_13_7645.2]

/-- Complete interval computation for depth 13, residue 7646. -/
theorem bounds_13_7646 : exactInterval 13 7646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7646 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7646) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7646 : oddCount 7646 13 = 9 ∧ acceleratedOrbit 13 7646 = 18377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7646 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7646) = 3 ^ 9 * m + 18377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7646.1, data_13_7646.2]

/-- Complete interval computation for depth 13, residue 7647. -/
theorem bounds_13_7647 : exactInterval 13 7647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7647 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7647) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7647 : oddCount 7647 13 = 9 ∧ acceleratedOrbit 13 7647 = 18377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7647 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7647) = 3 ^ 9 * m + 18377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7647.1, data_13_7647.2]

/-- Complete interval computation for depth 13, residue 7648. -/
theorem bounds_13_7648 : exactInterval 13 7648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7648 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7648) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7648 : oddCount 7648 13 = 7 ∧ acceleratedOrbit 13 7648 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7648 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7648) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7648.1, data_13_7648.2]

/-- Complete interval computation for depth 13, residue 7649. -/
theorem bounds_13_7649 : exactInterval 13 7649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7649 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7649) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7649 : oddCount 7649 13 = 9 ∧ acceleratedOrbit 13 7649 = 18386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7649 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7649) = 3 ^ 9 * m + 18386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7649.1, data_13_7649.2]

/-- Complete interval computation for depth 13, residue 7650. -/
theorem bounds_13_7650 : exactInterval 13 7650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7650 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7650) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7650 : oddCount 7650 13 = 4 ∧ acceleratedOrbit 13 7650 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7650 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7650) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7650.1, data_13_7650.2]

/-- Complete interval computation for depth 13, residue 7651. -/
theorem bounds_13_7651 : exactInterval 13 7651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7651 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7651) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7651 : oddCount 7651 13 = 4 ∧ acceleratedOrbit 13 7651 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7651 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7651) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7651.1, data_13_7651.2]

/-- Complete interval computation for depth 13, residue 7652. -/
theorem bounds_13_7652 : exactInterval 13 7652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7652 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7652) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7652 : oddCount 7652 13 = 7 ∧ acceleratedOrbit 13 7652 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7652 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7652) = 3 ^ 7 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7652.1, data_13_7652.2]

/-- Complete interval computation for depth 13, residue 7653. -/
theorem bounds_13_7653 : exactInterval 13 7653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7653 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7653) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7653 : oddCount 7653 13 = 7 ∧ acceleratedOrbit 13 7653 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7653 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7653) = 3 ^ 7 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7653.1, data_13_7653.2]

end Collatz.Research.StoppingAtlas.Batch0965
