import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0233

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7602. -/
theorem bounds_15_7602 : exactInterval 15 7602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7602 : oddCount 7602 15 = 6 ∧ acceleratedOrbit 15 7602 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7602) = 3 ^ 6 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7602.1, data_15_7602.2]

/-- Complete interval computation for depth 15, residue 7603. -/
theorem bounds_15_7603 : exactInterval 15 7603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7603 : oddCount 7603 15 = 6 ∧ acceleratedOrbit 15 7603 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7603) = 3 ^ 6 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7603.1, data_15_7603.2]

/-- Complete interval computation for depth 15, residue 7604. -/
theorem bounds_15_7604 : exactInterval 15 7604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7604 : oddCount 7604 15 = 6 ∧ acceleratedOrbit 15 7604 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7604) = 3 ^ 6 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7604.1, data_15_7604.2]

/-- Complete interval computation for depth 15, residue 7605. -/
theorem bounds_15_7605 : exactInterval 15 7605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7605 : oddCount 7605 15 = 6 ∧ acceleratedOrbit 15 7605 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7605) = 3 ^ 6 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7605.1, data_15_7605.2]

/-- Complete interval computation for depth 15, residue 7606. -/
theorem bounds_15_7606 : exactInterval 15 7606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7606 : oddCount 7606 15 = 10 ∧ acceleratedOrbit 15 7606 = 13715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7606) = 3 ^ 10 * m + 13715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7606.1, data_15_7606.2]

/-- Complete interval computation for depth 15, residue 7607. -/
theorem bounds_15_7607 : exactInterval 15 7607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7607 : oddCount 7607 15 = 10 ∧ acceleratedOrbit 15 7607 = 13715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7607) = 3 ^ 10 * m + 13715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7607.1, data_15_7607.2]

/-- Complete interval computation for depth 15, residue 7608. -/
theorem bounds_15_7608 : exactInterval 15 7608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7608 : oddCount 7608 15 = 6 ∧ acceleratedOrbit 15 7608 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7608) = 3 ^ 6 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7608.1, data_15_7608.2]

/-- Complete interval computation for depth 15, residue 7609. -/
theorem bounds_15_7609 : exactInterval 15 7609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7609 : oddCount 7609 15 = 6 ∧ acceleratedOrbit 15 7609 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7609) = 3 ^ 6 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7609.1, data_15_7609.2]

/-- Complete interval computation for depth 15, residue 7610. -/
theorem bounds_15_7610 : exactInterval 15 7610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7610 : oddCount 7610 15 = 6 ∧ acceleratedOrbit 15 7610 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7610) = 3 ^ 6 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7610.1, data_15_7610.2]

/-- Complete interval computation for depth 15, residue 7611. -/
theorem bounds_15_7611 : exactInterval 15 7611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7611 : oddCount 7611 15 = 8 ∧ acceleratedOrbit 15 7611 = 1525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7611) = 3 ^ 8 * m + 1525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7611.1, data_15_7611.2]

/-- Complete interval computation for depth 15, residue 7612. -/
theorem bounds_15_7612 : exactInterval 15 7612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7612 : oddCount 7612 15 = 9 ∧ acceleratedOrbit 15 7612 = 4576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7612) = 3 ^ 9 * m + 4576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7612.1, data_15_7612.2]

/-- Complete interval computation for depth 15, residue 7613. -/
theorem bounds_15_7613 : exactInterval 15 7613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7613 : oddCount 7613 15 = 9 ∧ acceleratedOrbit 15 7613 = 4576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7613) = 3 ^ 9 * m + 4576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7613.1, data_15_7613.2]

/-- Complete interval computation for depth 15, residue 7614. -/
theorem bounds_15_7614 : exactInterval 15 7614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7614 : oddCount 7614 15 = 9 ∧ acceleratedOrbit 15 7614 = 4576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7614) = 3 ^ 9 * m + 4576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7614.1, data_15_7614.2]

/-- Complete interval computation for depth 15, residue 7615. -/
theorem bounds_15_7615 : exactInterval 15 7615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7615 : oddCount 7615 15 = 12 ∧ acceleratedOrbit 15 7615 = 123520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7615) = 3 ^ 12 * m + 123520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7615.1, data_15_7615.2]

/-- Complete interval computation for depth 15, residue 7616. -/
theorem bounds_15_7616 : exactInterval 15 7616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7616 : oddCount 7616 15 = 4 ∧ acceleratedOrbit 15 7616 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7616) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7616.1, data_15_7616.2]

/-- Complete interval computation for depth 15, residue 7617. -/
theorem bounds_15_7617 : exactInterval 15 7617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7617 : oddCount 7617 15 = 9 ∧ acceleratedOrbit 15 7617 = 4580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7617) = 3 ^ 9 * m + 4580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7617.1, data_15_7617.2]

/-- Complete interval computation for depth 15, residue 7618. -/
theorem bounds_15_7618 : exactInterval 15 7618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7618 : oddCount 7618 15 = 9 ∧ acceleratedOrbit 15 7618 = 4580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7618) = 3 ^ 9 * m + 4580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7618.1, data_15_7618.2]

/-- Complete interval computation for depth 15, residue 7619. -/
theorem bounds_15_7619 : exactInterval 15 7619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7619 : oddCount 7619 15 = 9 ∧ acceleratedOrbit 15 7619 = 4580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7619) = 3 ^ 9 * m + 4580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7619.1, data_15_7619.2]

/-- Complete interval computation for depth 15, residue 7620. -/
theorem bounds_15_7620 : exactInterval 15 7620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7620 : oddCount 7620 15 = 4 ∧ acceleratedOrbit 15 7620 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7620) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7620.1, data_15_7620.2]

/-- Complete interval computation for depth 15, residue 7621. -/
theorem bounds_15_7621 : exactInterval 15 7621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7621 : oddCount 7621 15 = 4 ∧ acceleratedOrbit 15 7621 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7621) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7621.1, data_15_7621.2]

/-- Complete interval computation for depth 15, residue 7622. -/
theorem bounds_15_7622 : exactInterval 15 7622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7622 : oddCount 7622 15 = 4 ∧ acceleratedOrbit 15 7622 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7622) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7622.1, data_15_7622.2]

/-- Complete interval computation for depth 15, residue 7623. -/
theorem bounds_15_7623 : exactInterval 15 7623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7623 : oddCount 7623 15 = 7 ∧ acceleratedOrbit 15 7623 = 509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7623) = 3 ^ 7 * m + 509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7623.1, data_15_7623.2]

/-- Complete interval computation for depth 15, residue 7624. -/
theorem bounds_15_7624 : exactInterval 15 7624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7624 : oddCount 7624 15 = 7 ∧ acceleratedOrbit 15 7624 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7624) = 3 ^ 7 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7624.1, data_15_7624.2]

/-- Complete interval computation for depth 15, residue 7625. -/
theorem bounds_15_7625 : exactInterval 15 7625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7625 : oddCount 7625 15 = 8 ∧ acceleratedOrbit 15 7625 = 1529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7625) = 3 ^ 8 * m + 1529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7625.1, data_15_7625.2]

/-- Complete interval computation for depth 15, residue 7626. -/
theorem bounds_15_7626 : exactInterval 15 7626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7626 : oddCount 7626 15 = 7 ∧ acceleratedOrbit 15 7626 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7626) = 3 ^ 7 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7626.1, data_15_7626.2]

/-- Complete interval computation for depth 15, residue 7627. -/
theorem bounds_15_7627 : exactInterval 15 7627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7627 : oddCount 7627 15 = 8 ∧ acceleratedOrbit 15 7627 = 1529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7627) = 3 ^ 8 * m + 1529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7627.1, data_15_7627.2]

/-- Complete interval computation for depth 15, residue 7628. -/
theorem bounds_15_7628 : exactInterval 15 7628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7628 : oddCount 7628 15 = 7 ∧ acceleratedOrbit 15 7628 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7628) = 3 ^ 7 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7628.1, data_15_7628.2]

/-- Complete interval computation for depth 15, residue 7629. -/
theorem bounds_15_7629 : exactInterval 15 7629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7629 : oddCount 7629 15 = 7 ∧ acceleratedOrbit 15 7629 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7629) = 3 ^ 7 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7629.1, data_15_7629.2]

/-- Complete interval computation for depth 15, residue 7630. -/
theorem bounds_15_7630 : exactInterval 15 7630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7630 : oddCount 7630 15 = 9 ∧ acceleratedOrbit 15 7630 = 4585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7630) = 3 ^ 9 * m + 4585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7630.1, data_15_7630.2]

/-- Complete interval computation for depth 15, residue 7631. -/
theorem bounds_15_7631 : exactInterval 15 7631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7631 : oddCount 7631 15 = 9 ∧ acceleratedOrbit 15 7631 = 4585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7631) = 3 ^ 9 * m + 4585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7631.1, data_15_7631.2]

/-- Complete interval computation for depth 15, residue 7632. -/
theorem bounds_15_7632 : exactInterval 15 7632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7632 : oddCount 7632 15 = 4 ∧ acceleratedOrbit 15 7632 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7632) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7632.1, data_15_7632.2]

/-- Complete interval computation for depth 15, residue 7633. -/
theorem bounds_15_7633 : exactInterval 15 7633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7633 : oddCount 7633 15 = 7 ∧ acceleratedOrbit 15 7633 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7633) = 3 ^ 7 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7633.1, data_15_7633.2]

end Collatz.Research.PassageAtlas.Batch0233
