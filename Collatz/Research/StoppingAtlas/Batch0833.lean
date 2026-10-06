import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0833

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5611. -/
theorem bounds_13_5611 : exactInterval 13 5611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5611 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5611) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5611 : oddCount 5611 13 = 10 ∧ acceleratedOrbit 13 5611 = 40459 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5611 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5611) = 3 ^ 10 * m + 40459 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5611.1, data_13_5611.2]

/-- Complete interval computation for depth 13, residue 5612. -/
theorem bounds_13_5612 : exactInterval 13 5612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5612 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5612) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5612 : oddCount 5612 13 = 6 ∧ acceleratedOrbit 13 5612 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5612 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5612) = 3 ^ 6 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5612.1, data_13_5612.2]

/-- Complete interval computation for depth 13, residue 5613. -/
theorem bounds_13_5613 : exactInterval 13 5613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5613 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5613) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5613 : oddCount 5613 13 = 6 ∧ acceleratedOrbit 13 5613 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5613 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5613) = 3 ^ 6 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5613.1, data_13_5613.2]

/-- Complete interval computation for depth 13, residue 5614. -/
theorem bounds_13_5614 : exactInterval 13 5614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5614 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5614) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5614 : oddCount 5614 13 = 6 ∧ acceleratedOrbit 13 5614 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5614 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5614) = 3 ^ 6 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5614.1, data_13_5614.2]

/-- Complete interval computation for depth 13, residue 5615. -/
theorem bounds_13_5615 : exactInterval 13 5615 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5615 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5615) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5615 : oddCount 5615 13 = 8 ∧ acceleratedOrbit 13 5615 = 4498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5615 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5615) = 3 ^ 8 * m + 4498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5615.1, data_13_5615.2]

/-- Complete interval computation for depth 13, residue 5616. -/
theorem bounds_13_5616 : exactInterval 13 5616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5616 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5616) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5616 : oddCount 5616 13 = 5 ∧ acceleratedOrbit 13 5616 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5616 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5616) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5616.1, data_13_5616.2]

/-- Complete interval computation for depth 13, residue 5617. -/
theorem bounds_13_5617 : exactInterval 13 5617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5617 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5617) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5617 : oddCount 5617 13 = 5 ∧ acceleratedOrbit 13 5617 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5617 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5617) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5617.1, data_13_5617.2]

/-- Complete interval computation for depth 13, residue 5618. -/
theorem bounds_13_5618 : exactInterval 13 5618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5618 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5618) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5618 : oddCount 5618 13 = 7 ∧ acceleratedOrbit 13 5618 = 1502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5618 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5618) = 3 ^ 7 * m + 1502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5618.1, data_13_5618.2]

/-- Complete interval computation for depth 13, residue 5619. -/
theorem bounds_13_5619 : exactInterval 13 5619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5619 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5619) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5619 : oddCount 5619 13 = 7 ∧ acceleratedOrbit 13 5619 = 1502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5619 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5619) = 3 ^ 7 * m + 1502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5619.1, data_13_5619.2]

/-- Complete interval computation for depth 13, residue 5620. -/
theorem bounds_13_5620 : exactInterval 13 5620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5620 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5620) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5620 : oddCount 5620 13 = 5 ∧ acceleratedOrbit 13 5620 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5620 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5620) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5620.1, data_13_5620.2]

/-- Complete interval computation for depth 13, residue 5621. -/
theorem bounds_13_5621 : exactInterval 13 5621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5621 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5621) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5621 : oddCount 5621 13 = 5 ∧ acceleratedOrbit 13 5621 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5621 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5621) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5621.1, data_13_5621.2]

/-- Complete interval computation for depth 13, residue 5622. -/
theorem bounds_13_5622 : exactInterval 13 5622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5622 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5622) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5622 : oddCount 5622 13 = 9 ∧ acceleratedOrbit 13 5622 = 13517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5622 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5622) = 3 ^ 9 * m + 13517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5622.1, data_13_5622.2]

/-- Complete interval computation for depth 13, residue 5623. -/
theorem bounds_13_5623 : exactInterval 13 5623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5623 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5623) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5623 : oddCount 5623 13 = 9 ∧ acceleratedOrbit 13 5623 = 13517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5623 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5623) = 3 ^ 9 * m + 13517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5623.1, data_13_5623.2]

/-- Complete interval computation for depth 13, residue 5624. -/
theorem bounds_13_5624 : exactInterval 13 5624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5624 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5624) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5624 : oddCount 5624 13 = 8 ∧ acceleratedOrbit 13 5624 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5624 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5624) = 3 ^ 8 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5624.1, data_13_5624.2]

/-- Complete interval computation for depth 13, residue 5625. -/
theorem bounds_13_5625 : exactInterval 13 5625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5625 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5625) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5625 : oddCount 5625 13 = 8 ∧ acceleratedOrbit 13 5625 = 4508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5625 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5625) = 3 ^ 8 * m + 4508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5625.1, data_13_5625.2]

end Collatz.Research.StoppingAtlas.Batch0833
