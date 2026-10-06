import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0436

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3609. -/
theorem bounds_12_3609 : exactInterval 12 3609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3609 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3609) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3609 : oddCount 3609 12 = 6 ∧ acceleratedOrbit 12 3609 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3609 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3609) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3609.1, data_12_3609.2]

/-- Complete interval computation for depth 12, residue 3610. -/
theorem bounds_12_3610 : exactInterval 12 3610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3610 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3610) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3610 : oddCount 3610 12 = 6 ∧ acceleratedOrbit 12 3610 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3610 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3610) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3610.1, data_12_3610.2]

/-- Complete interval computation for depth 12, residue 3611. -/
theorem bounds_12_3611 : exactInterval 12 3611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3611 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3611) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3611 : oddCount 3611 12 = 9 ∧ acceleratedOrbit 12 3611 = 17360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3611 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3611) = 3 ^ 9 * m + 17360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3611.1, data_12_3611.2]

/-- Complete interval computation for depth 12, residue 3612. -/
theorem bounds_12_3612 : exactInterval 12 3612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3612 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3612) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3612 : oddCount 3612 12 = 5 ∧ acceleratedOrbit 12 3612 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3612 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3612) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3612.1, data_12_3612.2]

/-- Complete interval computation for depth 12, residue 3613. -/
theorem bounds_12_3613 : exactInterval 12 3613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3613 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3613) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3613 : oddCount 3613 12 = 5 ∧ acceleratedOrbit 12 3613 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3613 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3613) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3613.1, data_12_3613.2]

/-- Complete interval computation for depth 12, residue 3614. -/
theorem bounds_12_3614 : exactInterval 12 3614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3614 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3614) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3614 : oddCount 3614 12 = 5 ∧ acceleratedOrbit 12 3614 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3614 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3614) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3614.1, data_12_3614.2]

/-- Complete interval computation for depth 12, residue 3615. -/
theorem bounds_12_3615 : exactInterval 12 3615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3615 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3615) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3615 : oddCount 3615 12 = 9 ∧ acceleratedOrbit 12 3615 = 17378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3615 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3615) = 3 ^ 9 * m + 17378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3615.1, data_12_3615.2]

/-- Complete interval computation for depth 12, residue 3616. -/
theorem bounds_12_3616 : exactInterval 12 3616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3616 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3616) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3616 : oddCount 3616 12 = 2 ∧ acceleratedOrbit 12 3616 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3616 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3616) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3616.1, data_12_3616.2]

/-- Complete interval computation for depth 12, residue 3617. -/
theorem bounds_12_3617 : exactInterval 12 3617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3617 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3617) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3617 : oddCount 3617 12 = 7 ∧ acceleratedOrbit 12 3617 = 1934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3617 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3617) = 3 ^ 7 * m + 1934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3617.1, data_12_3617.2]

/-- Complete interval computation for depth 12, residue 3618. -/
theorem bounds_12_3618 : exactInterval 12 3618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3618 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3618) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3618 : oddCount 3618 12 = 6 ∧ acceleratedOrbit 12 3618 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3618 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3618) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3618.1, data_12_3618.2]

/-- Complete interval computation for depth 12, residue 3619. -/
theorem bounds_12_3619 : exactInterval 12 3619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3619 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3619) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3619 : oddCount 3619 12 = 6 ∧ acceleratedOrbit 12 3619 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3619 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3619) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3619.1, data_12_3619.2]

/-- Complete interval computation for depth 12, residue 3620. -/
theorem bounds_12_3620 : exactInterval 12 3620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3620 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3620) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3620 : oddCount 3620 12 = 7 ∧ acceleratedOrbit 12 3620 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3620 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3620) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3620.1, data_12_3620.2]

/-- Complete interval computation for depth 12, residue 3621. -/
theorem bounds_12_3621 : exactInterval 12 3621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3621 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3621) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3621 : oddCount 3621 12 = 7 ∧ acceleratedOrbit 12 3621 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3621 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3621) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3621.1, data_12_3621.2]

/-- Complete interval computation for depth 12, residue 3622. -/
theorem bounds_12_3622 : exactInterval 12 3622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3622 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3622) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3622 : oddCount 3622 12 = 7 ∧ acceleratedOrbit 12 3622 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3622 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3622) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3622.1, data_12_3622.2]

/-- Complete interval computation for depth 12, residue 3623. -/
theorem bounds_12_3623 : exactInterval 12 3623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3623 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3623) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3623 : oddCount 3623 12 = 5 ∧ acceleratedOrbit 12 3623 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3623 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3623) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3623.1, data_12_3623.2]

end Collatz.Research.StoppingAtlas.Batch0436
