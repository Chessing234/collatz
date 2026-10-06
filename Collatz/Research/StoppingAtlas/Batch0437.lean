import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0437

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3624. -/
theorem bounds_12_3624 : exactInterval 12 3624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3624 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3624) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3624 : oddCount 3624 12 = 2 ∧ acceleratedOrbit 12 3624 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3624 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3624) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3624.1, data_12_3624.2]

/-- Complete interval computation for depth 12, residue 3625. -/
theorem bounds_12_3625 : exactInterval 12 3625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3625 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3625) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3625 : oddCount 3625 12 = 9 ∧ acceleratedOrbit 12 3625 = 17428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3625 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3625) = 3 ^ 9 * m + 17428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3625.1, data_12_3625.2]

/-- Complete interval computation for depth 12, residue 3626. -/
theorem bounds_12_3626 : exactInterval 12 3626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3626 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3626) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3626 : oddCount 3626 12 = 2 ∧ acceleratedOrbit 12 3626 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3626 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3626) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3626.1, data_12_3626.2]

/-- Complete interval computation for depth 12, residue 3627. -/
theorem bounds_12_3627 : exactInterval 12 3627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3627 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3627) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3627 : oddCount 3627 12 = 6 ∧ acceleratedOrbit 12 3627 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3627 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3627) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3627.1, data_12_3627.2]

/-- Complete interval computation for depth 12, residue 3628. -/
theorem bounds_12_3628 : exactInterval 12 3628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3628 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3628) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3628 : oddCount 3628 12 = 7 ∧ acceleratedOrbit 12 3628 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3628 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3628) = 3 ^ 7 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3628.1, data_12_3628.2]

/-- Complete interval computation for depth 12, residue 3629. -/
theorem bounds_12_3629 : exactInterval 12 3629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3629 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3629) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3629 : oddCount 3629 12 = 7 ∧ acceleratedOrbit 12 3629 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3629 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3629) = 3 ^ 7 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3629.1, data_12_3629.2]

/-- Complete interval computation for depth 12, residue 3630. -/
theorem bounds_12_3630 : exactInterval 12 3630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3630 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3630) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3630 : oddCount 3630 12 = 7 ∧ acceleratedOrbit 12 3630 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3630 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3630) = 3 ^ 7 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3630.1, data_12_3630.2]

/-- Complete interval computation for depth 12, residue 3631. -/
theorem bounds_12_3631 : exactInterval 12 3631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3631 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3631) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3631 : oddCount 3631 12 = 9 ∧ acceleratedOrbit 12 3631 = 17455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3631 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3631) = 3 ^ 9 * m + 17455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3631.1, data_12_3631.2]

/-- Complete interval computation for depth 12, residue 3632. -/
theorem bounds_12_3632 : exactInterval 12 3632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3632 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3632) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3632 : oddCount 3632 12 = 2 ∧ acceleratedOrbit 12 3632 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3632 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3632) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3632.1, data_12_3632.2]

/-- Complete interval computation for depth 12, residue 3633. -/
theorem bounds_12_3633 : exactInterval 12 3633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3633 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3633) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3633 : oddCount 3633 12 = 8 ∧ acceleratedOrbit 12 3633 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3633 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3633) = 3 ^ 8 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3633.1, data_12_3633.2]

/-- Complete interval computation for depth 12, residue 3634. -/
theorem bounds_12_3634 : exactInterval 12 3634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3634 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3634) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3634 : oddCount 3634 12 = 8 ∧ acceleratedOrbit 12 3634 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3634 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3634) = 3 ^ 8 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3634.1, data_12_3634.2]

/-- Complete interval computation for depth 12, residue 3635. -/
theorem bounds_12_3635 : exactInterval 12 3635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3635 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3635) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3635 : oddCount 3635 12 = 8 ∧ acceleratedOrbit 12 3635 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3635 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3635) = 3 ^ 8 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3635.1, data_12_3635.2]

/-- Complete interval computation for depth 12, residue 3636. -/
theorem bounds_12_3636 : exactInterval 12 3636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3636 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3636) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3636 : oddCount 3636 12 = 2 ∧ acceleratedOrbit 12 3636 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3636 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3636) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3636.1, data_12_3636.2]

/-- Complete interval computation for depth 12, residue 3637. -/
theorem bounds_12_3637 : exactInterval 12 3637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3637 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3637) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3637 : oddCount 3637 12 = 2 ∧ acceleratedOrbit 12 3637 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3637 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3637) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3637.1, data_12_3637.2]

/-- Complete interval computation for depth 12, residue 3638. -/
theorem bounds_12_3638 : exactInterval 12 3638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3638 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3638) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3638 : oddCount 3638 12 = 10 ∧ acceleratedOrbit 12 3638 = 52487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3638 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3638) = 3 ^ 10 * m + 52487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3638.1, data_12_3638.2]

/-- Complete interval computation for depth 12, residue 3639. -/
theorem bounds_12_3639 : exactInterval 12 3639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3639 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3639) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3639 : oddCount 3639 12 = 10 ∧ acceleratedOrbit 12 3639 = 52487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3639 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3639) = 3 ^ 10 * m + 52487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3639.1, data_12_3639.2]

end Collatz.Research.StoppingAtlas.Batch0437
