import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0963

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7608. -/
theorem bounds_13_7608 : exactInterval 13 7608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7608 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7608) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7608 : oddCount 7608 13 = 5 ∧ acceleratedOrbit 13 7608 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7608 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7608) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7608.1, data_13_7608.2]

/-- Complete interval computation for depth 13, residue 7609. -/
theorem bounds_13_7609 : exactInterval 13 7609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7609 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7609) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7609 : oddCount 7609 13 = 5 ∧ acceleratedOrbit 13 7609 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7609 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7609) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7609.1, data_13_7609.2]

/-- Complete interval computation for depth 13, residue 7610. -/
theorem bounds_13_7610 : exactInterval 13 7610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7610 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7610) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7610 : oddCount 7610 13 = 5 ∧ acceleratedOrbit 13 7610 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7610 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7610) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7610.1, data_13_7610.2]

/-- Complete interval computation for depth 13, residue 7611. -/
theorem bounds_13_7611 : exactInterval 13 7611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7611 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7611) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7611 : oddCount 7611 13 = 7 ∧ acceleratedOrbit 13 7611 = 2033 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7611 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7611) = 3 ^ 7 * m + 2033 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7611.1, data_13_7611.2]

/-- Complete interval computation for depth 13, residue 7612. -/
theorem bounds_13_7612 : exactInterval 13 7612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7612 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7612) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7612 : oddCount 7612 13 = 8 ∧ acceleratedOrbit 13 7612 = 6101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7612 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7612) = 3 ^ 8 * m + 6101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7612.1, data_13_7612.2]

/-- Complete interval computation for depth 13, residue 7613. -/
theorem bounds_13_7613 : exactInterval 13 7613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7613 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7613) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7613 : oddCount 7613 13 = 8 ∧ acceleratedOrbit 13 7613 = 6101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7613 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7613) = 3 ^ 8 * m + 6101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7613.1, data_13_7613.2]

/-- Complete interval computation for depth 13, residue 7614. -/
theorem bounds_13_7614 : exactInterval 13 7614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7614 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7614) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7614 : oddCount 7614 13 = 8 ∧ acceleratedOrbit 13 7614 = 6101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7614 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7614) = 3 ^ 8 * m + 6101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7614.1, data_13_7614.2]

/-- Complete interval computation for depth 13, residue 7615. -/
theorem bounds_13_7615 : exactInterval 13 7615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7615 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7615) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7615 : oddCount 7615 13 = 11 ∧ acceleratedOrbit 13 7615 = 164693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7615 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7615) = 3 ^ 11 * m + 164693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7615.1, data_13_7615.2]

/-- Complete interval computation for depth 13, residue 7616. -/
theorem bounds_13_7616 : exactInterval 13 7616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7616 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7616) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7616 : oddCount 7616 13 = 4 ∧ acceleratedOrbit 13 7616 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7616 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7616) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7616.1, data_13_7616.2]

/-- Complete interval computation for depth 13, residue 7617. -/
theorem bounds_13_7617 : exactInterval 13 7617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7617 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7617) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7617 : oddCount 7617 13 = 7 ∧ acceleratedOrbit 13 7617 = 2035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7617 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7617) = 3 ^ 7 * m + 2035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7617.1, data_13_7617.2]

/-- Complete interval computation for depth 13, residue 7618. -/
theorem bounds_13_7618 : exactInterval 13 7618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7618 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7618) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7618 : oddCount 7618 13 = 7 ∧ acceleratedOrbit 13 7618 = 2035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7618 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7618) = 3 ^ 7 * m + 2035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7618.1, data_13_7618.2]

/-- Complete interval computation for depth 13, residue 7619. -/
theorem bounds_13_7619 : exactInterval 13 7619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7619 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7619) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7619 : oddCount 7619 13 = 7 ∧ acceleratedOrbit 13 7619 = 2035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7619 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7619) = 3 ^ 7 * m + 2035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7619.1, data_13_7619.2]

/-- Complete interval computation for depth 13, residue 7620. -/
theorem bounds_13_7620 : exactInterval 13 7620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7620 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7620) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7620 : oddCount 7620 13 = 4 ∧ acceleratedOrbit 13 7620 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7620 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7620) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7620.1, data_13_7620.2]

/-- Complete interval computation for depth 13, residue 7621. -/
theorem bounds_13_7621 : exactInterval 13 7621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7621 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7621) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7621 : oddCount 7621 13 = 4 ∧ acceleratedOrbit 13 7621 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7621 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7621) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7621.1, data_13_7621.2]

/-- Complete interval computation for depth 13, residue 7622. -/
theorem bounds_13_7622 : exactInterval 13 7622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7622 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7622) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7622 : oddCount 7622 13 = 4 ∧ acceleratedOrbit 13 7622 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7622 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7622) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7622.1, data_13_7622.2]

end Collatz.Research.StoppingAtlas.Batch0963
