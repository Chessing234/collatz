import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0416

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13598. -/
theorem bounds_15_13598 : exactInterval 15 13598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13598 : oddCount 13598 15 = 9 ∧ acceleratedOrbit 15 13598 = 8171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13598) = 3 ^ 9 * m + 8171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13598.1, data_15_13598.2]

/-- Complete interval computation for depth 15, residue 13599. -/
theorem bounds_15_13599 : exactInterval 15 13599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13599 : oddCount 13599 15 = 9 ∧ acceleratedOrbit 15 13599 = 8171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13599) = 3 ^ 9 * m + 8171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13599.1, data_15_13599.2]

/-- Complete interval computation for depth 15, residue 13600. -/
theorem bounds_15_13600 : exactInterval 15 13600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13600 : oddCount 13600 15 = 7 ∧ acceleratedOrbit 15 13600 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13600) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13600.1, data_15_13600.2]

/-- Complete interval computation for depth 15, residue 13601. -/
theorem bounds_15_13601 : exactInterval 15 13601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13601 : oddCount 13601 15 = 5 ∧ acceleratedOrbit 15 13601 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13601) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13601.1, data_15_13601.2]

/-- Complete interval computation for depth 15, residue 13602. -/
theorem bounds_15_13602 : exactInterval 15 13602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13602 : oddCount 13602 15 = 9 ∧ acceleratedOrbit 15 13602 = 8180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13602) = 3 ^ 9 * m + 8180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13602.1, data_15_13602.2]

/-- Complete interval computation for depth 15, residue 13603. -/
theorem bounds_15_13603 : exactInterval 15 13603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13603 : oddCount 13603 15 = 9 ∧ acceleratedOrbit 15 13603 = 8180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13603) = 3 ^ 9 * m + 8180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13603.1, data_15_13603.2]

/-- Complete interval computation for depth 15, residue 13604. -/
theorem bounds_15_13604 : exactInterval 15 13604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13604 : oddCount 13604 15 = 9 ∧ acceleratedOrbit 15 13604 = 8180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13604) = 3 ^ 9 * m + 8180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13604.1, data_15_13604.2]

/-- Complete interval computation for depth 15, residue 13605. -/
theorem bounds_15_13605 : exactInterval 15 13605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13605 : oddCount 13605 15 = 9 ∧ acceleratedOrbit 15 13605 = 8180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13605) = 3 ^ 9 * m + 8180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13605.1, data_15_13605.2]

/-- Complete interval computation for depth 15, residue 13606. -/
theorem bounds_15_13606 : exactInterval 15 13606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13606 : oddCount 13606 15 = 9 ∧ acceleratedOrbit 15 13606 = 8180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13606) = 3 ^ 9 * m + 8180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13606.1, data_15_13606.2]

/-- Complete interval computation for depth 15, residue 13607. -/
theorem bounds_15_13607 : exactInterval 15 13607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13607 : oddCount 13607 15 = 8 ∧ acceleratedOrbit 15 13607 = 2726 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13607) = 3 ^ 8 * m + 2726 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13607.1, data_15_13607.2]

/-- Complete interval computation for depth 15, residue 13608. -/
theorem bounds_15_13608 : exactInterval 15 13608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13608 : oddCount 13608 15 = 7 ∧ acceleratedOrbit 15 13608 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13608) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13608.1, data_15_13608.2]

/-- Complete interval computation for depth 15, residue 13609. -/
theorem bounds_15_13609 : exactInterval 15 13609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13609 : oddCount 13609 15 = 9 ∧ acceleratedOrbit 15 13609 = 8176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13609) = 3 ^ 9 * m + 8176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13609.1, data_15_13609.2]

/-- Complete interval computation for depth 15, residue 13610. -/
theorem bounds_15_13610 : exactInterval 15 13610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13610 : oddCount 13610 15 = 7 ∧ acceleratedOrbit 15 13610 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13610) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13610.1, data_15_13610.2]

/-- Complete interval computation for depth 15, residue 13611. -/
theorem bounds_15_13611 : exactInterval 15 13611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13611 : oddCount 13611 15 = 9 ∧ acceleratedOrbit 15 13611 = 8180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13611) = 3 ^ 9 * m + 8180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13611.1, data_15_13611.2]

/-- Complete interval computation for depth 15, residue 13612. -/
theorem bounds_15_13612 : exactInterval 15 13612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13612 : oddCount 13612 15 = 7 ∧ acceleratedOrbit 15 13612 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13612) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13612.1, data_15_13612.2]

/-- Complete interval computation for depth 15, residue 13613. -/
theorem bounds_15_13613 : exactInterval 15 13613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13613 : oddCount 13613 15 = 7 ∧ acceleratedOrbit 15 13613 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13613) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13613.1, data_15_13613.2]

/-- Complete interval computation for depth 15, residue 13614. -/
theorem bounds_15_13614 : exactInterval 15 13614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13614 : oddCount 13614 15 = 7 ∧ acceleratedOrbit 15 13614 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13614) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13614.1, data_15_13614.2]

/-- Complete interval computation for depth 15, residue 13615. -/
theorem bounds_15_13615 : exactInterval 15 13615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13615 : oddCount 13615 15 = 10 ∧ acceleratedOrbit 15 13615 = 24538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13615) = 3 ^ 10 * m + 24538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13615.1, data_15_13615.2]

/-- Complete interval computation for depth 15, residue 13616. -/
theorem bounds_15_13616 : exactInterval 15 13616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13616 : oddCount 13616 15 = 7 ∧ acceleratedOrbit 15 13616 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13616) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13616.1, data_15_13616.2]

/-- Complete interval computation for depth 15, residue 13617. -/
theorem bounds_15_13617 : exactInterval 15 13617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13617 : oddCount 13617 15 = 8 ∧ acceleratedOrbit 15 13617 = 2729 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13617) = 3 ^ 8 * m + 2729 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13617.1, data_15_13617.2]

/-- Complete interval computation for depth 15, residue 13618. -/
theorem bounds_15_13618 : exactInterval 15 13618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13618 : oddCount 13618 15 = 8 ∧ acceleratedOrbit 15 13618 = 2729 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13618) = 3 ^ 8 * m + 2729 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13618.1, data_15_13618.2]

/-- Complete interval computation for depth 15, residue 13619. -/
theorem bounds_15_13619 : exactInterval 15 13619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13619 : oddCount 13619 15 = 8 ∧ acceleratedOrbit 15 13619 = 2729 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13619) = 3 ^ 8 * m + 2729 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13619.1, data_15_13619.2]

/-- Complete interval computation for depth 15, residue 13620. -/
theorem bounds_15_13620 : exactInterval 15 13620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13620 : oddCount 13620 15 = 7 ∧ acceleratedOrbit 15 13620 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13620) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13620.1, data_15_13620.2]

/-- Complete interval computation for depth 15, residue 13621. -/
theorem bounds_15_13621 : exactInterval 15 13621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13621 : oddCount 13621 15 = 7 ∧ acceleratedOrbit 15 13621 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13621) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13621.1, data_15_13621.2]

/-- Complete interval computation for depth 15, residue 13622. -/
theorem bounds_15_13622 : exactInterval 15 13622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13622 : oddCount 13622 15 = 10 ∧ acceleratedOrbit 15 13622 = 24553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13622) = 3 ^ 10 * m + 24553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13622.1, data_15_13622.2]

/-- Complete interval computation for depth 15, residue 13623. -/
theorem bounds_15_13623 : exactInterval 15 13623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13623 : oddCount 13623 15 = 10 ∧ acceleratedOrbit 15 13623 = 24553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13623) = 3 ^ 10 * m + 24553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13623.1, data_15_13623.2]

/-- Complete interval computation for depth 15, residue 13624. -/
theorem bounds_15_13624 : exactInterval 15 13624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13624 : oddCount 13624 15 = 7 ∧ acceleratedOrbit 15 13624 = 910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13624) = 3 ^ 7 * m + 910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13624.1, data_15_13624.2]

/-- Complete interval computation for depth 15, residue 13625. -/
theorem bounds_15_13625 : exactInterval 15 13625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13625 : oddCount 13625 15 = 9 ∧ acceleratedOrbit 15 13625 = 8186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13625) = 3 ^ 9 * m + 8186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13625.1, data_15_13625.2]

/-- Complete interval computation for depth 15, residue 13626. -/
theorem bounds_15_13626 : exactInterval 15 13626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13626 : oddCount 13626 15 = 7 ∧ acceleratedOrbit 15 13626 = 910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13626) = 3 ^ 7 * m + 910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13626.1, data_15_13626.2]

/-- Complete interval computation for depth 15, residue 13627. -/
theorem bounds_15_13627 : exactInterval 15 13627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13627 : oddCount 13627 15 = 7 ∧ acceleratedOrbit 15 13627 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13627) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13627.1, data_15_13627.2]

/-- Complete interval computation for depth 15, residue 13628. -/
theorem bounds_15_13628 : exactInterval 15 13628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13628 : oddCount 13628 15 = 7 ∧ acceleratedOrbit 15 13628 = 910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13628) = 3 ^ 7 * m + 910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13628.1, data_15_13628.2]

/-- Complete interval computation for depth 15, residue 13629. -/
theorem bounds_15_13629 : exactInterval 15 13629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13629 : oddCount 13629 15 = 7 ∧ acceleratedOrbit 15 13629 = 910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13629) = 3 ^ 7 * m + 910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13629.1, data_15_13629.2]

/-- Complete interval computation for depth 15, residue 13630. -/
theorem bounds_15_13630 : exactInterval 15 13630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13630 : oddCount 13630 15 = 9 ∧ acceleratedOrbit 15 13630 = 8189 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13630) = 3 ^ 9 * m + 8189 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13630.1, data_15_13630.2]

end Collatz.Research.PassageAtlas.Batch0416
