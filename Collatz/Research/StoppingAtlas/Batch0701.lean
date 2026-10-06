import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0701

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3584. -/
theorem bounds_13_3584 : exactInterval 13 3584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3584 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3584) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3584 : oddCount 3584 13 = 3 ∧ acceleratedOrbit 13 3584 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3584 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3584) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3584.1, data_13_3584.2]

/-- Complete interval computation for depth 13, residue 3585. -/
theorem bounds_13_3585 : exactInterval 13 3585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3585 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3585) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3585 : oddCount 3585 13 = 8 ∧ acceleratedOrbit 13 3585 = 2875 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3585 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3585) = 3 ^ 8 * m + 2875 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3585.1, data_13_3585.2]

/-- Complete interval computation for depth 13, residue 3586. -/
theorem bounds_13_3586 : exactInterval 13 3586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3586 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3586) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3586 : oddCount 3586 13 = 5 ∧ acceleratedOrbit 13 3586 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3586 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3586) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3586.1, data_13_3586.2]

/-- Complete interval computation for depth 13, residue 3587. -/
theorem bounds_13_3587 : exactInterval 13 3587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3587 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3587) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3587 : oddCount 3587 13 = 5 ∧ acceleratedOrbit 13 3587 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3587 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3587) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3587.1, data_13_3587.2]

/-- Complete interval computation for depth 13, residue 3588. -/
theorem bounds_13_3588 : exactInterval 13 3588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3588 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3588) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3588 : oddCount 3588 13 = 7 ∧ acceleratedOrbit 13 3588 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3588 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3588) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3588.1, data_13_3588.2]

/-- Complete interval computation for depth 13, residue 3589. -/
theorem bounds_13_3589 : exactInterval 13 3589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3589 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3589) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3589 : oddCount 3589 13 = 7 ∧ acceleratedOrbit 13 3589 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3589 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3589) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3589.1, data_13_3589.2]

/-- Complete interval computation for depth 13, residue 3590. -/
theorem bounds_13_3590 : exactInterval 13 3590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3590 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3590) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3590 : oddCount 3590 13 = 7 ∧ acceleratedOrbit 13 3590 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3590 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3590) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3590.1, data_13_3590.2]

/-- Complete interval computation for depth 13, residue 3591. -/
theorem bounds_13_3591 : exactInterval 13 3591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3591 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3591) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3591 : oddCount 3591 13 = 8 ∧ acceleratedOrbit 13 3591 = 2879 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3591 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3591) = 3 ^ 8 * m + 2879 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3591.1, data_13_3591.2]

/-- Complete interval computation for depth 13, residue 3592. -/
theorem bounds_13_3592 : exactInterval 13 3592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3592 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3592) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3592 : oddCount 3592 13 = 6 ∧ acceleratedOrbit 13 3592 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3592 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3592) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3592.1, data_13_3592.2]

/-- Complete interval computation for depth 13, residue 3593. -/
theorem bounds_13_3593 : exactInterval 13 3593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3593 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3593) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3593 : oddCount 3593 13 = 6 ∧ acceleratedOrbit 13 3593 = 320 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3593 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3593) = 3 ^ 6 * m + 320 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3593.1, data_13_3593.2]

/-- Complete interval computation for depth 13, residue 3594. -/
theorem bounds_13_3594 : exactInterval 13 3594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3594 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3594) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3594 : oddCount 3594 13 = 6 ∧ acceleratedOrbit 13 3594 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3594 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3594) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3594.1, data_13_3594.2]

/-- Complete interval computation for depth 13, residue 3595. -/
theorem bounds_13_3595 : exactInterval 13 3595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3595 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3595) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3595 : oddCount 3595 13 = 7 ∧ acceleratedOrbit 13 3595 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3595 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3595) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3595.1, data_13_3595.2]

/-- Complete interval computation for depth 13, residue 3596. -/
theorem bounds_13_3596 : exactInterval 13 3596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3596 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3596) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3596 : oddCount 3596 13 = 6 ∧ acceleratedOrbit 13 3596 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3596 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3596) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3596.1, data_13_3596.2]

/-- Complete interval computation for depth 13, residue 3597. -/
theorem bounds_13_3597 : exactInterval 13 3597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3597 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3597) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3597 : oddCount 3597 13 = 6 ∧ acceleratedOrbit 13 3597 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3597 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3597) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3597.1, data_13_3597.2]

/-- Complete interval computation for depth 13, residue 3598. -/
theorem bounds_13_3598 : exactInterval 13 3598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3598 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3598) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3598 : oddCount 3598 13 = 7 ∧ acceleratedOrbit 13 3598 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3598 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3598) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3598.1, data_13_3598.2]

end Collatz.Research.StoppingAtlas.Batch0701
