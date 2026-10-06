import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0599

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19595. -/
theorem bounds_15_19595 : exactInterval 15 19595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19595 : oddCount 19595 15 = 6 ∧ acceleratedOrbit 15 19595 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19595) = 3 ^ 6 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19595.1, data_15_19595.2]

/-- Complete interval computation for depth 15, residue 19596. -/
theorem bounds_15_19596 : exactInterval 15 19596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19596 : oddCount 19596 15 = 5 ∧ acceleratedOrbit 15 19596 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19596) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19596.1, data_15_19596.2]

/-- Complete interval computation for depth 15, residue 19597. -/
theorem bounds_15_19597 : exactInterval 15 19597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19597 : oddCount 19597 15 = 5 ∧ acceleratedOrbit 15 19597 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19597) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19597.1, data_15_19597.2]

/-- Complete interval computation for depth 15, residue 19598. -/
theorem bounds_15_19598 : exactInterval 15 19598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19598 : oddCount 19598 15 = 8 ∧ acceleratedOrbit 15 19598 = 3925 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19598) = 3 ^ 8 * m + 3925 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19598.1, data_15_19598.2]

/-- Complete interval computation for depth 15, residue 19599. -/
theorem bounds_15_19599 : exactInterval 15 19599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19599 : oddCount 19599 15 = 8 ∧ acceleratedOrbit 15 19599 = 3925 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19599) = 3 ^ 8 * m + 3925 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19599.1, data_15_19599.2]

/-- Complete interval computation for depth 15, residue 19600. -/
theorem bounds_15_19600 : exactInterval 15 19600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19600 : oddCount 19600 15 = 5 ∧ acceleratedOrbit 15 19600 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19600) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19600.1, data_15_19600.2]

/-- Complete interval computation for depth 15, residue 19601. -/
theorem bounds_15_19601 : exactInterval 15 19601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19601 : oddCount 19601 15 = 8 ∧ acceleratedOrbit 15 19601 = 3926 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19601) = 3 ^ 8 * m + 3926 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19601.1, data_15_19601.2]

/-- Complete interval computation for depth 15, residue 19602. -/
theorem bounds_15_19602 : exactInterval 15 19602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19602 : oddCount 19602 15 = 8 ∧ acceleratedOrbit 15 19602 = 3926 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19602) = 3 ^ 8 * m + 3926 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19602.1, data_15_19602.2]

/-- Complete interval computation for depth 15, residue 19603. -/
theorem bounds_15_19603 : exactInterval 15 19603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19603 : oddCount 19603 15 = 8 ∧ acceleratedOrbit 15 19603 = 3926 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19603) = 3 ^ 8 * m + 3926 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19603.1, data_15_19603.2]

/-- Complete interval computation for depth 15, residue 19604. -/
theorem bounds_15_19604 : exactInterval 15 19604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19604 : oddCount 19604 15 = 5 ∧ acceleratedOrbit 15 19604 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19604) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19604.1, data_15_19604.2]

/-- Complete interval computation for depth 15, residue 19605. -/
theorem bounds_15_19605 : exactInterval 15 19605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19605 : oddCount 19605 15 = 5 ∧ acceleratedOrbit 15 19605 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19605) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19605.1, data_15_19605.2]

/-- Complete interval computation for depth 15, residue 19606. -/
theorem bounds_15_19606 : exactInterval 15 19606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19606 : oddCount 19606 15 = 5 ∧ acceleratedOrbit 15 19606 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19606) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19606.1, data_15_19606.2]

/-- Complete interval computation for depth 15, residue 19607. -/
theorem bounds_15_19607 : exactInterval 15 19607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19607 : oddCount 19607 15 = 5 ∧ acceleratedOrbit 15 19607 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19607) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19607.1, data_15_19607.2]

/-- Complete interval computation for depth 15, residue 19608. -/
theorem bounds_15_19608 : exactInterval 15 19608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19608 : oddCount 19608 15 = 5 ∧ acceleratedOrbit 15 19608 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19608) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19608.1, data_15_19608.2]

/-- Complete interval computation for depth 15, residue 19609. -/
theorem bounds_15_19609 : exactInterval 15 19609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19609 : oddCount 19609 15 = 8 ∧ acceleratedOrbit 15 19609 = 3928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19609) = 3 ^ 8 * m + 3928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19609.1, data_15_19609.2]

/-- Complete interval computation for depth 15, residue 19610. -/
theorem bounds_15_19610 : exactInterval 15 19610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19610 : oddCount 19610 15 = 5 ∧ acceleratedOrbit 15 19610 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19610) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19610.1, data_15_19610.2]

/-- Complete interval computation for depth 15, residue 19611. -/
theorem bounds_15_19611 : exactInterval 15 19611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19611 : oddCount 19611 15 = 12 ∧ acceleratedOrbit 15 19611 = 318086 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19611) = 3 ^ 12 * m + 318086 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19611.1, data_15_19611.2]

/-- Complete interval computation for depth 15, residue 19612. -/
theorem bounds_15_19612 : exactInterval 15 19612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19612 : oddCount 19612 15 = 9 ∧ acceleratedOrbit 15 19612 = 11785 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19612) = 3 ^ 9 * m + 11785 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19612.1, data_15_19612.2]

/-- Complete interval computation for depth 15, residue 19613. -/
theorem bounds_15_19613 : exactInterval 15 19613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19613 : oddCount 19613 15 = 9 ∧ acceleratedOrbit 15 19613 = 11785 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19613) = 3 ^ 9 * m + 11785 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19613.1, data_15_19613.2]

/-- Complete interval computation for depth 15, residue 19614. -/
theorem bounds_15_19614 : exactInterval 15 19614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19614 : oddCount 19614 15 = 9 ∧ acceleratedOrbit 15 19614 = 11785 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19614) = 3 ^ 9 * m + 11785 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19614.1, data_15_19614.2]

/-- Complete interval computation for depth 15, residue 19615. -/
theorem bounds_15_19615 : exactInterval 15 19615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19615 : oddCount 19615 15 = 13 ∧ acceleratedOrbit 15 19615 = 954422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19615) = 3 ^ 13 * m + 954422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19615.1, data_15_19615.2]

/-- Complete interval computation for depth 15, residue 19616. -/
theorem bounds_15_19616 : exactInterval 15 19616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19616 : oddCount 19616 15 = 4 ∧ acceleratedOrbit 15 19616 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19616) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19616.1, data_15_19616.2]

/-- Complete interval computation for depth 15, residue 19617. -/
theorem bounds_15_19617 : exactInterval 15 19617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19617 : oddCount 19617 15 = 11 ∧ acceleratedOrbit 15 19617 = 106069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19617) = 3 ^ 11 * m + 106069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19617.1, data_15_19617.2]

/-- Complete interval computation for depth 15, residue 19618. -/
theorem bounds_15_19618 : exactInterval 15 19618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19618 : oddCount 19618 15 = 7 ∧ acceleratedOrbit 15 19618 = 1310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19618) = 3 ^ 7 * m + 1310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19618.1, data_15_19618.2]

/-- Complete interval computation for depth 15, residue 19619. -/
theorem bounds_15_19619 : exactInterval 15 19619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19619 : oddCount 19619 15 = 7 ∧ acceleratedOrbit 15 19619 = 1310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19619) = 3 ^ 7 * m + 1310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19619.1, data_15_19619.2]

/-- Complete interval computation for depth 15, residue 19620. -/
theorem bounds_15_19620 : exactInterval 15 19620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19620 : oddCount 19620 15 = 7 ∧ acceleratedOrbit 15 19620 = 1310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19620) = 3 ^ 7 * m + 1310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19620.1, data_15_19620.2]

/-- Complete interval computation for depth 15, residue 19621. -/
theorem bounds_15_19621 : exactInterval 15 19621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19621 : oddCount 19621 15 = 7 ∧ acceleratedOrbit 15 19621 = 1310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19621) = 3 ^ 7 * m + 1310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19621.1, data_15_19621.2]

/-- Complete interval computation for depth 15, residue 19622. -/
theorem bounds_15_19622 : exactInterval 15 19622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19622 : oddCount 19622 15 = 7 ∧ acceleratedOrbit 15 19622 = 1310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19622) = 3 ^ 7 * m + 1310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19622.1, data_15_19622.2]

/-- Complete interval computation for depth 15, residue 19623. -/
theorem bounds_15_19623 : exactInterval 15 19623 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19623) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19623 : oddCount 19623 15 = 9 ∧ acceleratedOrbit 15 19623 = 11788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19623) = 3 ^ 9 * m + 11788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19623.1, data_15_19623.2]

/-- Complete interval computation for depth 15, residue 19624. -/
theorem bounds_15_19624 : exactInterval 15 19624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19624 : oddCount 19624 15 = 4 ∧ acceleratedOrbit 15 19624 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19624) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19624.1, data_15_19624.2]

/-- Complete interval computation for depth 15, residue 19625. -/
theorem bounds_15_19625 : exactInterval 15 19625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19625 : oddCount 19625 15 = 10 ∧ acceleratedOrbit 15 19625 = 35369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19625) = 3 ^ 10 * m + 35369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19625.1, data_15_19625.2]

/-- Complete interval computation for depth 15, residue 19626. -/
theorem bounds_15_19626 : exactInterval 15 19626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19626 : oddCount 19626 15 = 4 ∧ acceleratedOrbit 15 19626 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19626) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19626.1, data_15_19626.2]

/-- Complete interval computation for depth 15, residue 19627. -/
theorem bounds_15_19627 : exactInterval 15 19627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19627 : oddCount 19627 15 = 8 ∧ acceleratedOrbit 15 19627 = 3932 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19627) = 3 ^ 8 * m + 3932 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19627.1, data_15_19627.2]

end Collatz.Research.PassageAtlas.Batch0599
