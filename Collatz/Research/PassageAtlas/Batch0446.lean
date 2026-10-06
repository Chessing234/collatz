import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0446

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14581. -/
theorem bounds_15_14581 : exactInterval 15 14581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14581 : oddCount 14581 15 = 6 ∧ acceleratedOrbit 15 14581 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14581) = 3 ^ 6 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14581.1, data_15_14581.2]

/-- Complete interval computation for depth 15, residue 14582. -/
theorem bounds_15_14582 : exactInterval 15 14582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14582 : oddCount 14582 15 = 7 ∧ acceleratedOrbit 15 14582 = 974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14582) = 3 ^ 7 * m + 974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14582.1, data_15_14582.2]

/-- Complete interval computation for depth 15, residue 14583. -/
theorem bounds_15_14583 : exactInterval 15 14583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14583 : oddCount 14583 15 = 7 ∧ acceleratedOrbit 15 14583 = 974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14583) = 3 ^ 7 * m + 974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14583.1, data_15_14583.2]

/-- Complete interval computation for depth 15, residue 14584. -/
theorem bounds_15_14584 : exactInterval 15 14584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14584 : oddCount 14584 15 = 7 ∧ acceleratedOrbit 15 14584 = 974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14584) = 3 ^ 7 * m + 974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14584.1, data_15_14584.2]

/-- Complete interval computation for depth 15, residue 14585. -/
theorem bounds_15_14585 : exactInterval 15 14585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14585 : oddCount 14585 15 = 8 ∧ acceleratedOrbit 15 14585 = 2921 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14585) = 3 ^ 8 * m + 2921 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14585.1, data_15_14585.2]

/-- Complete interval computation for depth 15, residue 14586. -/
theorem bounds_15_14586 : exactInterval 15 14586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14586 : oddCount 14586 15 = 7 ∧ acceleratedOrbit 15 14586 = 974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14586) = 3 ^ 7 * m + 974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14586.1, data_15_14586.2]

/-- Complete interval computation for depth 15, residue 14587. -/
theorem bounds_15_14587 : exactInterval 15 14587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14587 : oddCount 14587 15 = 11 ∧ acceleratedOrbit 15 14587 = 78869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14587) = 3 ^ 11 * m + 78869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14587.1, data_15_14587.2]

/-- Complete interval computation for depth 15, residue 14588. -/
theorem bounds_15_14588 : exactInterval 15 14588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14588 : oddCount 14588 15 = 7 ∧ acceleratedOrbit 15 14588 = 974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14588) = 3 ^ 7 * m + 974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14588.1, data_15_14588.2]

/-- Complete interval computation for depth 15, residue 14589. -/
theorem bounds_15_14589 : exactInterval 15 14589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14589 : oddCount 14589 15 = 7 ∧ acceleratedOrbit 15 14589 = 974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14589) = 3 ^ 7 * m + 974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14589.1, data_15_14589.2]

/-- Complete interval computation for depth 15, residue 14590. -/
theorem bounds_15_14590 : exactInterval 15 14590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14590 : oddCount 14590 15 = 11 ∧ acceleratedOrbit 15 14590 = 78887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14590) = 3 ^ 11 * m + 78887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14590.1, data_15_14590.2]

/-- Complete interval computation for depth 15, residue 14591. -/
theorem bounds_15_14591 : exactInterval 15 14591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14591 : oddCount 14591 15 = 11 ∧ acceleratedOrbit 15 14591 = 78887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14591) = 3 ^ 11 * m + 78887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14591.1, data_15_14591.2]

/-- Complete interval computation for depth 15, residue 14592. -/
theorem bounds_15_14592 : exactInterval 15 14592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14592 : oddCount 14592 15 = 4 ∧ acceleratedOrbit 15 14592 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14592) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14592.1, data_15_14592.2]

/-- Complete interval computation for depth 15, residue 14593. -/
theorem bounds_15_14593 : exactInterval 15 14593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14593 : oddCount 14593 15 = 6 ∧ acceleratedOrbit 15 14593 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14593) = 3 ^ 6 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14593.1, data_15_14593.2]

/-- Complete interval computation for depth 15, residue 14594. -/
theorem bounds_15_14594 : exactInterval 15 14594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14594 : oddCount 14594 15 = 8 ∧ acceleratedOrbit 15 14594 = 2924 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14594) = 3 ^ 8 * m + 2924 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14594.1, data_15_14594.2]

/-- Complete interval computation for depth 15, residue 14595. -/
theorem bounds_15_14595 : exactInterval 15 14595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14595 : oddCount 14595 15 = 8 ∧ acceleratedOrbit 15 14595 = 2924 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14595) = 3 ^ 8 * m + 2924 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14595.1, data_15_14595.2]

/-- Complete interval computation for depth 15, residue 14596. -/
theorem bounds_15_14596 : exactInterval 15 14596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14596 : oddCount 14596 15 = 6 ∧ acceleratedOrbit 15 14596 = 326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14596) = 3 ^ 6 * m + 326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14596.1, data_15_14596.2]

/-- Complete interval computation for depth 15, residue 14597. -/
theorem bounds_15_14597 : exactInterval 15 14597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14597 : oddCount 14597 15 = 6 ∧ acceleratedOrbit 15 14597 = 326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14597) = 3 ^ 6 * m + 326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14597.1, data_15_14597.2]

/-- Complete interval computation for depth 15, residue 14598. -/
theorem bounds_15_14598 : exactInterval 15 14598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14598 : oddCount 14598 15 = 6 ∧ acceleratedOrbit 15 14598 = 326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14598) = 3 ^ 6 * m + 326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14598.1, data_15_14598.2]

/-- Complete interval computation for depth 15, residue 14599. -/
theorem bounds_15_14599 : exactInterval 15 14599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14599 : oddCount 14599 15 = 8 ∧ acceleratedOrbit 15 14599 = 2924 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14599) = 3 ^ 8 * m + 2924 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14599.1, data_15_14599.2]

/-- Complete interval computation for depth 15, residue 14600. -/
theorem bounds_15_14600 : exactInterval 15 14600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14600 : oddCount 14600 15 = 6 ∧ acceleratedOrbit 15 14600 = 326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14600) = 3 ^ 6 * m + 326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14600.1, data_15_14600.2]

/-- Complete interval computation for depth 15, residue 14601. -/
theorem bounds_15_14601 : exactInterval 15 14601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14601 : oddCount 14601 15 = 9 ∧ acceleratedOrbit 15 14601 = 8774 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14601) = 3 ^ 9 * m + 8774 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14601.1, data_15_14601.2]

/-- Complete interval computation for depth 15, residue 14602. -/
theorem bounds_15_14602 : exactInterval 15 14602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14602 : oddCount 14602 15 = 6 ∧ acceleratedOrbit 15 14602 = 326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14602) = 3 ^ 6 * m + 326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14602.1, data_15_14602.2]

/-- Complete interval computation for depth 15, residue 14603. -/
theorem bounds_15_14603 : exactInterval 15 14603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14603 : oddCount 14603 15 = 6 ∧ acceleratedOrbit 15 14603 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14603) = 3 ^ 6 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14603.1, data_15_14603.2]

/-- Complete interval computation for depth 15, residue 14604. -/
theorem bounds_15_14604 : exactInterval 15 14604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14604 : oddCount 14604 15 = 6 ∧ acceleratedOrbit 15 14604 = 326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14604) = 3 ^ 6 * m + 326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14604.1, data_15_14604.2]

/-- Complete interval computation for depth 15, residue 14605. -/
theorem bounds_15_14605 : exactInterval 15 14605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14605 : oddCount 14605 15 = 6 ∧ acceleratedOrbit 15 14605 = 326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14605) = 3 ^ 6 * m + 326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14605.1, data_15_14605.2]

/-- Complete interval computation for depth 15, residue 14606. -/
theorem bounds_15_14606 : exactInterval 15 14606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14606 : oddCount 14606 15 = 8 ∧ acceleratedOrbit 15 14606 = 2926 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14606) = 3 ^ 8 * m + 2926 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14606.1, data_15_14606.2]

/-- Complete interval computation for depth 15, residue 14607. -/
theorem bounds_15_14607 : exactInterval 15 14607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14607 : oddCount 14607 15 = 8 ∧ acceleratedOrbit 15 14607 = 2926 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14607) = 3 ^ 8 * m + 2926 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14607.1, data_15_14607.2]

/-- Complete interval computation for depth 15, residue 14608. -/
theorem bounds_15_14608 : exactInterval 15 14608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14608 : oddCount 14608 15 = 5 ∧ acceleratedOrbit 15 14608 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14608) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14608.1, data_15_14608.2]

/-- Complete interval computation for depth 15, residue 14609. -/
theorem bounds_15_14609 : exactInterval 15 14609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14609 : oddCount 14609 15 = 6 ∧ acceleratedOrbit 15 14609 = 326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14609) = 3 ^ 6 * m + 326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14609.1, data_15_14609.2]

/-- Complete interval computation for depth 15, residue 14610. -/
theorem bounds_15_14610 : exactInterval 15 14610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14610 : oddCount 14610 15 = 10 ∧ acceleratedOrbit 15 14610 = 26335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14610) = 3 ^ 10 * m + 26335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14610.1, data_15_14610.2]

/-- Complete interval computation for depth 15, residue 14611. -/
theorem bounds_15_14611 : exactInterval 15 14611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14611 : oddCount 14611 15 = 10 ∧ acceleratedOrbit 15 14611 = 26335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14611) = 3 ^ 10 * m + 26335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14611.1, data_15_14611.2]

/-- Complete interval computation for depth 15, residue 14612. -/
theorem bounds_15_14612 : exactInterval 15 14612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14612 : oddCount 14612 15 = 5 ∧ acceleratedOrbit 15 14612 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14612) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14612.1, data_15_14612.2]

/-- Complete interval computation for depth 15, residue 14613. -/
theorem bounds_15_14613 : exactInterval 15 14613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14613 : oddCount 14613 15 = 5 ∧ acceleratedOrbit 15 14613 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14613) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14613.1, data_15_14613.2]

end Collatz.Research.PassageAtlas.Batch0446
