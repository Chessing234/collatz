import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0962

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7592. -/
theorem bounds_13_7592 : exactInterval 13 7592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7592 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7592) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7592 : oddCount 7592 13 = 4 ∧ acceleratedOrbit 13 7592 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7592 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7592) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7592.1, data_13_7592.2]

/-- Complete interval computation for depth 13, residue 7593. -/
theorem bounds_13_7593 : exactInterval 13 7593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7593 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7593) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7593 : oddCount 7593 13 = 8 ∧ acceleratedOrbit 13 7593 = 6083 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7593 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7593) = 3 ^ 8 * m + 6083 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7593.1, data_13_7593.2]

/-- Complete interval computation for depth 13, residue 7594. -/
theorem bounds_13_7594 : exactInterval 13 7594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7594 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7594) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7594 : oddCount 7594 13 = 4 ∧ acceleratedOrbit 13 7594 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7594 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7594) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7594.1, data_13_7594.2]

/-- Complete interval computation for depth 13, residue 7595. -/
theorem bounds_13_7595 : exactInterval 13 7595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7595 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7595) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7595 : oddCount 7595 13 = 8 ∧ acceleratedOrbit 13 7595 = 6085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7595 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7595) = 3 ^ 8 * m + 6085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7595.1, data_13_7595.2]

/-- Complete interval computation for depth 13, residue 7596. -/
theorem bounds_13_7596 : exactInterval 13 7596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7596 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7596) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7596 : oddCount 7596 13 = 6 ∧ acceleratedOrbit 13 7596 = 677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7596 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7596) = 3 ^ 6 * m + 677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7596.1, data_13_7596.2]

/-- Complete interval computation for depth 13, residue 7597. -/
theorem bounds_13_7597 : exactInterval 13 7597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7597 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7597) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7597 : oddCount 7597 13 = 6 ∧ acceleratedOrbit 13 7597 = 677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7597 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7597) = 3 ^ 6 * m + 677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7597.1, data_13_7597.2]

/-- Complete interval computation for depth 13, residue 7598. -/
theorem bounds_13_7598 : exactInterval 13 7598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7598 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7598) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7598 : oddCount 7598 13 = 6 ∧ acceleratedOrbit 13 7598 = 677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7598 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7598) = 3 ^ 6 * m + 677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7598.1, data_13_7598.2]

/-- Complete interval computation for depth 13, residue 7599. -/
theorem bounds_13_7599 : exactInterval 13 7599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7599 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7599) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7599 : oddCount 7599 13 = 8 ∧ acceleratedOrbit 13 7599 = 6088 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7599 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7599) = 3 ^ 8 * m + 6088 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7599.1, data_13_7599.2]

/-- Complete interval computation for depth 13, residue 7600. -/
theorem bounds_13_7600 : exactInterval 13 7600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7600 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7600) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7600 : oddCount 7600 13 = 5 ∧ acceleratedOrbit 13 7600 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7600 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7600) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7600.1, data_13_7600.2]

/-- Complete interval computation for depth 13, residue 7601. -/
theorem bounds_13_7601 : exactInterval 13 7601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7601 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7601) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7601 : oddCount 7601 13 = 5 ∧ acceleratedOrbit 13 7601 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7601 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7601) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7601.1, data_13_7601.2]

/-- Complete interval computation for depth 13, residue 7602. -/
theorem bounds_13_7602 : exactInterval 13 7602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7602 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7602) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7602 : oddCount 7602 13 = 5 ∧ acceleratedOrbit 13 7602 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7602 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7602) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7602.1, data_13_7602.2]

/-- Complete interval computation for depth 13, residue 7603. -/
theorem bounds_13_7603 : exactInterval 13 7603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7603 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7603) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7603 : oddCount 7603 13 = 5 ∧ acceleratedOrbit 13 7603 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7603 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7603) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7603.1, data_13_7603.2]

/-- Complete interval computation for depth 13, residue 7604. -/
theorem bounds_13_7604 : exactInterval 13 7604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7604 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7604) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7604 : oddCount 7604 13 = 5 ∧ acceleratedOrbit 13 7604 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7604 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7604) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7604.1, data_13_7604.2]

/-- Complete interval computation for depth 13, residue 7605. -/
theorem bounds_13_7605 : exactInterval 13 7605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7605 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7605) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7605 : oddCount 7605 13 = 5 ∧ acceleratedOrbit 13 7605 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7605 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7605) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7605.1, data_13_7605.2]

/-- Complete interval computation for depth 13, residue 7606. -/
theorem bounds_13_7606 : exactInterval 13 7606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7606 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7606) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7606 : oddCount 7606 13 = 8 ∧ acceleratedOrbit 13 7606 = 6095 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7606 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7606) = 3 ^ 8 * m + 6095 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7606.1, data_13_7606.2]

/-- Complete interval computation for depth 13, residue 7607. -/
theorem bounds_13_7607 : exactInterval 13 7607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7607 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7607) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7607 : oddCount 7607 13 = 8 ∧ acceleratedOrbit 13 7607 = 6095 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7607 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7607) = 3 ^ 8 * m + 6095 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7607.1, data_13_7607.2]

end Collatz.Research.StoppingAtlas.Batch0962
