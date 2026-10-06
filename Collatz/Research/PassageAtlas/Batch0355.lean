import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0355

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11599. -/
theorem bounds_15_11599 : exactInterval 15 11599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11599 : oddCount 11599 15 = 8 ∧ acceleratedOrbit 15 11599 = 2323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11599) = 3 ^ 8 * m + 2323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11599.1, data_15_11599.2]

/-- Complete interval computation for depth 15, residue 11600. -/
theorem bounds_15_11600 : exactInterval 15 11600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11600 : oddCount 11600 15 = 3 ∧ acceleratedOrbit 15 11600 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11600) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11600.1, data_15_11600.2]

/-- Complete interval computation for depth 15, residue 11601. -/
theorem bounds_15_11601 : exactInterval 15 11601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11601 : oddCount 11601 15 = 9 ∧ acceleratedOrbit 15 11601 = 6971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11601) = 3 ^ 9 * m + 6971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11601.1, data_15_11601.2]

/-- Complete interval computation for depth 15, residue 11602. -/
theorem bounds_15_11602 : exactInterval 15 11602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11602 : oddCount 11602 15 = 9 ∧ acceleratedOrbit 15 11602 = 6971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11602) = 3 ^ 9 * m + 6971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11602.1, data_15_11602.2]

/-- Complete interval computation for depth 15, residue 11603. -/
theorem bounds_15_11603 : exactInterval 15 11603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11603 : oddCount 11603 15 = 9 ∧ acceleratedOrbit 15 11603 = 6971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11603) = 3 ^ 9 * m + 6971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11603.1, data_15_11603.2]

/-- Complete interval computation for depth 15, residue 11604. -/
theorem bounds_15_11604 : exactInterval 15 11604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11604 : oddCount 11604 15 = 3 ∧ acceleratedOrbit 15 11604 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11604) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11604.1, data_15_11604.2]

/-- Complete interval computation for depth 15, residue 11605. -/
theorem bounds_15_11605 : exactInterval 15 11605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11605 : oddCount 11605 15 = 3 ∧ acceleratedOrbit 15 11605 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11605) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11605.1, data_15_11605.2]

/-- Complete interval computation for depth 15, residue 11606. -/
theorem bounds_15_11606 : exactInterval 15 11606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11606 : oddCount 11606 15 = 7 ∧ acceleratedOrbit 15 11606 = 775 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11606) = 3 ^ 7 * m + 775 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11606.1, data_15_11606.2]

/-- Complete interval computation for depth 15, residue 11607. -/
theorem bounds_15_11607 : exactInterval 15 11607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11607 : oddCount 11607 15 = 7 ∧ acceleratedOrbit 15 11607 = 775 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11607) = 3 ^ 7 * m + 775 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11607.1, data_15_11607.2]

/-- Complete interval computation for depth 15, residue 11608. -/
theorem bounds_15_11608 : exactInterval 15 11608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11608 : oddCount 11608 15 = 7 ∧ acceleratedOrbit 15 11608 = 776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11608) = 3 ^ 7 * m + 776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11608.1, data_15_11608.2]

/-- Complete interval computation for depth 15, residue 11609. -/
theorem bounds_15_11609 : exactInterval 15 11609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11609 : oddCount 11609 15 = 7 ∧ acceleratedOrbit 15 11609 = 776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11609) = 3 ^ 7 * m + 776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11609.1, data_15_11609.2]

/-- Complete interval computation for depth 15, residue 11610. -/
theorem bounds_15_11610 : exactInterval 15 11610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11610 : oddCount 11610 15 = 7 ∧ acceleratedOrbit 15 11610 = 776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11610) = 3 ^ 7 * m + 776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11610.1, data_15_11610.2]

/-- Complete interval computation for depth 15, residue 11611. -/
theorem bounds_15_11611 : exactInterval 15 11611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11611 : oddCount 11611 15 = 9 ∧ acceleratedOrbit 15 11611 = 6976 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11611) = 3 ^ 9 * m + 6976 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11611.1, data_15_11611.2]

/-- Complete interval computation for depth 15, residue 11612. -/
theorem bounds_15_11612 : exactInterval 15 11612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11612 : oddCount 11612 15 = 7 ∧ acceleratedOrbit 15 11612 = 776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11612) = 3 ^ 7 * m + 776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11612.1, data_15_11612.2]

/-- Complete interval computation for depth 15, residue 11613. -/
theorem bounds_15_11613 : exactInterval 15 11613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11613 : oddCount 11613 15 = 7 ∧ acceleratedOrbit 15 11613 = 776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11613) = 3 ^ 7 * m + 776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11613.1, data_15_11613.2]

/-- Complete interval computation for depth 15, residue 11614. -/
theorem bounds_15_11614 : exactInterval 15 11614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11614 : oddCount 11614 15 = 9 ∧ acceleratedOrbit 15 11614 = 6979 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11614) = 3 ^ 9 * m + 6979 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11614.1, data_15_11614.2]

/-- Complete interval computation for depth 15, residue 11615. -/
theorem bounds_15_11615 : exactInterval 15 11615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11615 : oddCount 11615 15 = 9 ∧ acceleratedOrbit 15 11615 = 6979 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11615) = 3 ^ 9 * m + 6979 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11615.1, data_15_11615.2]

/-- Complete interval computation for depth 15, residue 11616. -/
theorem bounds_15_11616 : exactInterval 15 11616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11616 : oddCount 11616 15 = 6 ∧ acceleratedOrbit 15 11616 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11616) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11616.1, data_15_11616.2]

/-- Complete interval computation for depth 15, residue 11617. -/
theorem bounds_15_11617 : exactInterval 15 11617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11617 : oddCount 11617 15 = 7 ∧ acceleratedOrbit 15 11617 = 776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11617) = 3 ^ 7 * m + 776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11617.1, data_15_11617.2]

/-- Complete interval computation for depth 15, residue 11618. -/
theorem bounds_15_11618 : exactInterval 15 11618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11618 : oddCount 11618 15 = 6 ∧ acceleratedOrbit 15 11618 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11618) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11618.1, data_15_11618.2]

/-- Complete interval computation for depth 15, residue 11619. -/
theorem bounds_15_11619 : exactInterval 15 11619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11619 : oddCount 11619 15 = 6 ∧ acceleratedOrbit 15 11619 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11619) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11619.1, data_15_11619.2]

/-- Complete interval computation for depth 15, residue 11620. -/
theorem bounds_15_11620 : exactInterval 15 11620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11620 : oddCount 11620 15 = 6 ∧ acceleratedOrbit 15 11620 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11620) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11620.1, data_15_11620.2]

/-- Complete interval computation for depth 15, residue 11621. -/
theorem bounds_15_11621 : exactInterval 15 11621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11621 : oddCount 11621 15 = 6 ∧ acceleratedOrbit 15 11621 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11621) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11621.1, data_15_11621.2]

/-- Complete interval computation for depth 15, residue 11622. -/
theorem bounds_15_11622 : exactInterval 15 11622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11622 : oddCount 11622 15 = 6 ∧ acceleratedOrbit 15 11622 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11622) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11622.1, data_15_11622.2]

/-- Complete interval computation for depth 15, residue 11623. -/
theorem bounds_15_11623 : exactInterval 15 11623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11623 : oddCount 11623 15 = 12 ∧ acceleratedOrbit 15 11623 = 188527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11623) = 3 ^ 12 * m + 188527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11623.1, data_15_11623.2]

/-- Complete interval computation for depth 15, residue 11624. -/
theorem bounds_15_11624 : exactInterval 15 11624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11624 : oddCount 11624 15 = 6 ∧ acceleratedOrbit 15 11624 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11624) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11624.1, data_15_11624.2]

/-- Complete interval computation for depth 15, residue 11625. -/
theorem bounds_15_11625 : exactInterval 15 11625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11625 : oddCount 11625 15 = 9 ∧ acceleratedOrbit 15 11625 = 6986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11625) = 3 ^ 9 * m + 6986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11625.1, data_15_11625.2]

/-- Complete interval computation for depth 15, residue 11626. -/
theorem bounds_15_11626 : exactInterval 15 11626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11626 : oddCount 11626 15 = 6 ∧ acceleratedOrbit 15 11626 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11626) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11626.1, data_15_11626.2]

/-- Complete interval computation for depth 15, residue 11627. -/
theorem bounds_15_11627 : exactInterval 15 11627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11627 : oddCount 11627 15 = 9 ∧ acceleratedOrbit 15 11627 = 6986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11627) = 3 ^ 9 * m + 6986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11627.1, data_15_11627.2]

/-- Complete interval computation for depth 15, residue 11628. -/
theorem bounds_15_11628 : exactInterval 15 11628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11628 : oddCount 11628 15 = 8 ∧ acceleratedOrbit 15 11628 = 2330 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11628) = 3 ^ 8 * m + 2330 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11628.1, data_15_11628.2]

/-- Complete interval computation for depth 15, residue 11629. -/
theorem bounds_15_11629 : exactInterval 15 11629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11629 : oddCount 11629 15 = 8 ∧ acceleratedOrbit 15 11629 = 2330 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11629) = 3 ^ 8 * m + 2330 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11629.1, data_15_11629.2]

/-- Complete interval computation for depth 15, residue 11630. -/
theorem bounds_15_11630 : exactInterval 15 11630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11630 : oddCount 11630 15 = 8 ∧ acceleratedOrbit 15 11630 = 2330 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11630) = 3 ^ 8 * m + 2330 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11630.1, data_15_11630.2]

/-- Complete interval computation for depth 15, residue 11631. -/
theorem bounds_15_11631 : exactInterval 15 11631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11631 : oddCount 11631 15 = 9 ∧ acceleratedOrbit 15 11631 = 6988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11631) = 3 ^ 9 * m + 6988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11631.1, data_15_11631.2]

end Collatz.Research.PassageAtlas.Batch0355
