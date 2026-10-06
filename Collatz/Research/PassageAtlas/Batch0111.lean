import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0111

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3604. -/
theorem bounds_15_3604 : exactInterval 15 3604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3604 : oddCount 3604 15 = 9 ∧ acceleratedOrbit 15 3604 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3604) = 3 ^ 9 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3604.1, data_15_3604.2]

/-- Complete interval computation for depth 15, residue 3605. -/
theorem bounds_15_3605 : exactInterval 15 3605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3605 : oddCount 3605 15 = 9 ∧ acceleratedOrbit 15 3605 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3605) = 3 ^ 9 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3605.1, data_15_3605.2]

/-- Complete interval computation for depth 15, residue 3606. -/
theorem bounds_15_3606 : exactInterval 15 3606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3606 : oddCount 3606 15 = 8 ∧ acceleratedOrbit 15 3606 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3606) = 3 ^ 8 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3606.1, data_15_3606.2]

/-- Complete interval computation for depth 15, residue 3607. -/
theorem bounds_15_3607 : exactInterval 15 3607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3607 : oddCount 3607 15 = 8 ∧ acceleratedOrbit 15 3607 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3607) = 3 ^ 8 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3607.1, data_15_3607.2]

/-- Complete interval computation for depth 15, residue 3608. -/
theorem bounds_15_3608 : exactInterval 15 3608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3608 : oddCount 3608 15 = 9 ∧ acceleratedOrbit 15 3608 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3608) = 3 ^ 9 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3608.1, data_15_3608.2]

/-- Complete interval computation for depth 15, residue 3609. -/
theorem bounds_15_3609 : exactInterval 15 3609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3609 : oddCount 3609 15 = 8 ∧ acceleratedOrbit 15 3609 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3609) = 3 ^ 8 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3609.1, data_15_3609.2]

/-- Complete interval computation for depth 15, residue 3610. -/
theorem bounds_15_3610 : exactInterval 15 3610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3610 : oddCount 3610 15 = 9 ∧ acceleratedOrbit 15 3610 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3610) = 3 ^ 9 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3610.1, data_15_3610.2]

/-- Complete interval computation for depth 15, residue 3611. -/
theorem bounds_15_3611 : exactInterval 15 3611 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3611) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3611 : oddCount 3611 15 = 9 ∧ acceleratedOrbit 15 3611 = 2170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3611) = 3 ^ 9 * m + 2170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3611.1, data_15_3611.2]

/-- Complete interval computation for depth 15, residue 3612. -/
theorem bounds_15_3612 : exactInterval 15 3612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3612 : oddCount 3612 15 = 8 ∧ acceleratedOrbit 15 3612 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3612) = 3 ^ 8 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3612.1, data_15_3612.2]

/-- Complete interval computation for depth 15, residue 3613. -/
theorem bounds_15_3613 : exactInterval 15 3613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3613 : oddCount 3613 15 = 8 ∧ acceleratedOrbit 15 3613 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3613) = 3 ^ 8 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3613.1, data_15_3613.2]

/-- Complete interval computation for depth 15, residue 3614. -/
theorem bounds_15_3614 : exactInterval 15 3614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3614 : oddCount 3614 15 = 8 ∧ acceleratedOrbit 15 3614 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3614) = 3 ^ 8 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3614.1, data_15_3614.2]

/-- Complete interval computation for depth 15, residue 3615. -/
theorem bounds_15_3615 : exactInterval 15 3615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3615 : oddCount 3615 15 = 10 ∧ acceleratedOrbit 15 3615 = 6517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3615) = 3 ^ 10 * m + 6517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3615.1, data_15_3615.2]

/-- Complete interval computation for depth 15, residue 3616. -/
theorem bounds_15_3616 : exactInterval 15 3616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3616 : oddCount 3616 15 = 2 ∧ acceleratedOrbit 15 3616 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3616) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3616.1, data_15_3616.2]

/-- Complete interval computation for depth 15, residue 3617. -/
theorem bounds_15_3617 : exactInterval 15 3617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3617 : oddCount 3617 15 = 9 ∧ acceleratedOrbit 15 3617 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3617) = 3 ^ 9 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3617.1, data_15_3617.2]

/-- Complete interval computation for depth 15, residue 3618. -/
theorem bounds_15_3618 : exactInterval 15 3618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3618 : oddCount 3618 15 = 9 ∧ acceleratedOrbit 15 3618 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3618) = 3 ^ 9 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3618.1, data_15_3618.2]

/-- Complete interval computation for depth 15, residue 3619. -/
theorem bounds_15_3619 : exactInterval 15 3619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3619 : oddCount 3619 15 = 9 ∧ acceleratedOrbit 15 3619 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3619) = 3 ^ 9 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3619.1, data_15_3619.2]

/-- Complete interval computation for depth 15, residue 3620. -/
theorem bounds_15_3620 : exactInterval 15 3620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3620 : oddCount 3620 15 = 9 ∧ acceleratedOrbit 15 3620 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3620) = 3 ^ 9 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3620.1, data_15_3620.2]

/-- Complete interval computation for depth 15, residue 3621. -/
theorem bounds_15_3621 : exactInterval 15 3621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3621 : oddCount 3621 15 = 9 ∧ acceleratedOrbit 15 3621 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3621) = 3 ^ 9 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3621.1, data_15_3621.2]

/-- Complete interval computation for depth 15, residue 3622. -/
theorem bounds_15_3622 : exactInterval 15 3622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3622 : oddCount 3622 15 = 9 ∧ acceleratedOrbit 15 3622 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3622) = 3 ^ 9 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3622.1, data_15_3622.2]

/-- Complete interval computation for depth 15, residue 3623. -/
theorem bounds_15_3623 : exactInterval 15 3623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3623 : oddCount 3623 15 = 8 ∧ acceleratedOrbit 15 3623 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3623) = 3 ^ 8 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3623.1, data_15_3623.2]

/-- Complete interval computation for depth 15, residue 3624. -/
theorem bounds_15_3624 : exactInterval 15 3624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3624 : oddCount 3624 15 = 2 ∧ acceleratedOrbit 15 3624 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3624) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3624.1, data_15_3624.2]

/-- Complete interval computation for depth 15, residue 3625. -/
theorem bounds_15_3625 : exactInterval 15 3625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3625 : oddCount 3625 15 = 10 ∧ acceleratedOrbit 15 3625 = 6536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3625) = 3 ^ 10 * m + 6536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3625.1, data_15_3625.2]

/-- Complete interval computation for depth 15, residue 3626. -/
theorem bounds_15_3626 : exactInterval 15 3626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3626 : oddCount 3626 15 = 2 ∧ acceleratedOrbit 15 3626 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3626) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3626.1, data_15_3626.2]

/-- Complete interval computation for depth 15, residue 3627. -/
theorem bounds_15_3627 : exactInterval 15 3627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3627 : oddCount 3627 15 = 9 ∧ acceleratedOrbit 15 3627 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3627) = 3 ^ 9 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3627.1, data_15_3627.2]

/-- Complete interval computation for depth 15, residue 3628. -/
theorem bounds_15_3628 : exactInterval 15 3628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3628 : oddCount 3628 15 = 10 ∧ acceleratedOrbit 15 3628 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3628) = 3 ^ 10 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3628.1, data_15_3628.2]

/-- Complete interval computation for depth 15, residue 3629. -/
theorem bounds_15_3629 : exactInterval 15 3629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3629 : oddCount 3629 15 = 10 ∧ acceleratedOrbit 15 3629 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3629) = 3 ^ 10 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3629.1, data_15_3629.2]

/-- Complete interval computation for depth 15, residue 3630. -/
theorem bounds_15_3630 : exactInterval 15 3630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3630 : oddCount 3630 15 = 10 ∧ acceleratedOrbit 15 3630 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3630) = 3 ^ 10 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3630.1, data_15_3630.2]

/-- Complete interval computation for depth 15, residue 3631. -/
theorem bounds_15_3631 : exactInterval 15 3631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3631 : oddCount 3631 15 = 12 ∧ acceleratedOrbit 15 3631 = 58913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3631) = 3 ^ 12 * m + 58913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3631.1, data_15_3631.2]

/-- Complete interval computation for depth 15, residue 3632. -/
theorem bounds_15_3632 : exactInterval 15 3632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3632 : oddCount 3632 15 = 2 ∧ acceleratedOrbit 15 3632 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3632) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3632.1, data_15_3632.2]

/-- Complete interval computation for depth 15, residue 3633. -/
theorem bounds_15_3633 : exactInterval 15 3633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3633 : oddCount 3633 15 = 11 ∧ acceleratedOrbit 15 3633 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3633) = 3 ^ 11 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3633.1, data_15_3633.2]

/-- Complete interval computation for depth 15, residue 3634. -/
theorem bounds_15_3634 : exactInterval 15 3634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3634 : oddCount 3634 15 = 11 ∧ acceleratedOrbit 15 3634 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3634) = 3 ^ 11 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3634.1, data_15_3634.2]

/-- Complete interval computation for depth 15, residue 3635. -/
theorem bounds_15_3635 : exactInterval 15 3635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3635 : oddCount 3635 15 = 11 ∧ acceleratedOrbit 15 3635 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3635) = 3 ^ 11 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3635.1, data_15_3635.2]

/-- Complete interval computation for depth 15, residue 3636. -/
theorem bounds_15_3636 : exactInterval 15 3636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3636 : oddCount 3636 15 = 2 ∧ acceleratedOrbit 15 3636 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3636) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3636.1, data_15_3636.2]

end Collatz.Research.PassageAtlas.Batch0111
