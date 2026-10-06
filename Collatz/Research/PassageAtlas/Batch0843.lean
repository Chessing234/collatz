import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0843

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27590. -/
theorem bounds_15_27590 : exactInterval 15 27590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27590 : oddCount 27590 15 = 5 ∧ acceleratedOrbit 15 27590 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27590) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27590.1, data_15_27590.2]

/-- Complete interval computation for depth 15, residue 27591. -/
theorem bounds_15_27591 : exactInterval 15 27591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27591 : oddCount 27591 15 = 10 ∧ acceleratedOrbit 15 27591 = 49724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27591) = 3 ^ 10 * m + 49724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27591.1, data_15_27591.2]

/-- Complete interval computation for depth 15, residue 27592. -/
theorem bounds_15_27592 : exactInterval 15 27592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27592 : oddCount 27592 15 = 8 ∧ acceleratedOrbit 15 27592 = 5528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27592) = 3 ^ 8 * m + 5528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27592.1, data_15_27592.2]

/-- Complete interval computation for depth 15, residue 27593. -/
theorem bounds_15_27593 : exactInterval 15 27593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27593 : oddCount 27593 15 = 10 ∧ acceleratedOrbit 15 27593 = 49733 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27593) = 3 ^ 10 * m + 49733 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27593.1, data_15_27593.2]

/-- Complete interval computation for depth 15, residue 27594. -/
theorem bounds_15_27594 : exactInterval 15 27594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27594 : oddCount 27594 15 = 8 ∧ acceleratedOrbit 15 27594 = 5528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27594) = 3 ^ 8 * m + 5528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27594.1, data_15_27594.2]

/-- Complete interval computation for depth 15, residue 27595. -/
theorem bounds_15_27595 : exactInterval 15 27595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27595 : oddCount 27595 15 = 8 ∧ acceleratedOrbit 15 27595 = 5528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27595) = 3 ^ 8 * m + 5528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27595.1, data_15_27595.2]

/-- Complete interval computation for depth 15, residue 27596. -/
theorem bounds_15_27596 : exactInterval 15 27596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27596 : oddCount 27596 15 = 8 ∧ acceleratedOrbit 15 27596 = 5528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27596) = 3 ^ 8 * m + 5528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27596.1, data_15_27596.2]

/-- Complete interval computation for depth 15, residue 27597. -/
theorem bounds_15_27597 : exactInterval 15 27597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27597 : oddCount 27597 15 = 8 ∧ acceleratedOrbit 15 27597 = 5528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27597) = 3 ^ 8 * m + 5528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27597.1, data_15_27597.2]

/-- Complete interval computation for depth 15, residue 27598. -/
theorem bounds_15_27598 : exactInterval 15 27598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27598 : oddCount 27598 15 = 9 ∧ acceleratedOrbit 15 27598 = 16580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27598) = 3 ^ 9 * m + 16580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27598.1, data_15_27598.2]

/-- Complete interval computation for depth 15, residue 27599. -/
theorem bounds_15_27599 : exactInterval 15 27599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27599 : oddCount 27599 15 = 9 ∧ acceleratedOrbit 15 27599 = 16580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27599) = 3 ^ 9 * m + 16580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27599.1, data_15_27599.2]

/-- Complete interval computation for depth 15, residue 27600. -/
theorem bounds_15_27600 : exactInterval 15 27600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27600 : oddCount 27600 15 = 5 ∧ acceleratedOrbit 15 27600 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27600) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27600.1, data_15_27600.2]

/-- Complete interval computation for depth 15, residue 27601. -/
theorem bounds_15_27601 : exactInterval 15 27601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27601 : oddCount 27601 15 = 8 ∧ acceleratedOrbit 15 27601 = 5528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27601) = 3 ^ 8 * m + 5528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27601.1, data_15_27601.2]

/-- Complete interval computation for depth 15, residue 27602. -/
theorem bounds_15_27602 : exactInterval 15 27602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27602 : oddCount 27602 15 = 10 ∧ acceleratedOrbit 15 27602 = 49747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27602) = 3 ^ 10 * m + 49747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27602.1, data_15_27602.2]

/-- Complete interval computation for depth 15, residue 27603. -/
theorem bounds_15_27603 : exactInterval 15 27603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27603 : oddCount 27603 15 = 10 ∧ acceleratedOrbit 15 27603 = 49747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27603) = 3 ^ 10 * m + 49747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27603.1, data_15_27603.2]

/-- Complete interval computation for depth 15, residue 27604. -/
theorem bounds_15_27604 : exactInterval 15 27604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27604 : oddCount 27604 15 = 5 ∧ acceleratedOrbit 15 27604 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27604) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27604.1, data_15_27604.2]

/-- Complete interval computation for depth 15, residue 27605. -/
theorem bounds_15_27605 : exactInterval 15 27605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27605 : oddCount 27605 15 = 5 ∧ acceleratedOrbit 15 27605 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27605) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27605.1, data_15_27605.2]

/-- Complete interval computation for depth 15, residue 27606. -/
theorem bounds_15_27606 : exactInterval 15 27606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27606 : oddCount 27606 15 = 10 ∧ acceleratedOrbit 15 27606 = 49754 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27606) = 3 ^ 10 * m + 49754 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27606.1, data_15_27606.2]

/-- Complete interval computation for depth 15, residue 27607. -/
theorem bounds_15_27607 : exactInterval 15 27607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27607 : oddCount 27607 15 = 10 ∧ acceleratedOrbit 15 27607 = 49754 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27607) = 3 ^ 10 * m + 49754 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27607.1, data_15_27607.2]

/-- Complete interval computation for depth 15, residue 27608. -/
theorem bounds_15_27608 : exactInterval 15 27608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27608 : oddCount 27608 15 = 7 ∧ acceleratedOrbit 15 27608 = 1844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27608) = 3 ^ 7 * m + 1844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27608.1, data_15_27608.2]

/-- Complete interval computation for depth 15, residue 27609. -/
theorem bounds_15_27609 : exactInterval 15 27609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27609 : oddCount 27609 15 = 5 ∧ acceleratedOrbit 15 27609 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27609) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27609.1, data_15_27609.2]

/-- Complete interval computation for depth 15, residue 27610. -/
theorem bounds_15_27610 : exactInterval 15 27610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27610 : oddCount 27610 15 = 7 ∧ acceleratedOrbit 15 27610 = 1844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27610) = 3 ^ 7 * m + 1844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27610.1, data_15_27610.2]

/-- Complete interval computation for depth 15, residue 27611. -/
theorem bounds_15_27611 : exactInterval 15 27611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27611 : oddCount 27611 15 = 7 ∧ acceleratedOrbit 15 27611 = 1843 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27611) = 3 ^ 7 * m + 1843 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27611.1, data_15_27611.2]

/-- Complete interval computation for depth 15, residue 27612. -/
theorem bounds_15_27612 : exactInterval 15 27612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27612 : oddCount 27612 15 = 7 ∧ acceleratedOrbit 15 27612 = 1844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27612) = 3 ^ 7 * m + 1844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27612.1, data_15_27612.2]

/-- Complete interval computation for depth 15, residue 27613. -/
theorem bounds_15_27613 : exactInterval 15 27613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27613 : oddCount 27613 15 = 7 ∧ acceleratedOrbit 15 27613 = 1844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27613) = 3 ^ 7 * m + 1844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27613.1, data_15_27613.2]

/-- Complete interval computation for depth 15, residue 27614. -/
theorem bounds_15_27614 : exactInterval 15 27614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27614 : oddCount 27614 15 = 9 ∧ acceleratedOrbit 15 27614 = 16589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27614) = 3 ^ 9 * m + 16589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27614.1, data_15_27614.2]

/-- Complete interval computation for depth 15, residue 27615. -/
theorem bounds_15_27615 : exactInterval 15 27615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27615 : oddCount 27615 15 = 9 ∧ acceleratedOrbit 15 27615 = 16589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27615) = 3 ^ 9 * m + 16589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27615.1, data_15_27615.2]

/-- Complete interval computation for depth 15, residue 27616. -/
theorem bounds_15_27616 : exactInterval 15 27616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27616 : oddCount 27616 15 = 5 ∧ acceleratedOrbit 15 27616 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27616) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27616.1, data_15_27616.2]

/-- Complete interval computation for depth 15, residue 27617. -/
theorem bounds_15_27617 : exactInterval 15 27617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27617 : oddCount 27617 15 = 9 ∧ acceleratedOrbit 15 27617 = 16591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27617) = 3 ^ 9 * m + 16591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27617.1, data_15_27617.2]

/-- Complete interval computation for depth 15, residue 27618. -/
theorem bounds_15_27618 : exactInterval 15 27618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27618 : oddCount 27618 15 = 5 ∧ acceleratedOrbit 15 27618 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27618) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27618.1, data_15_27618.2]

/-- Complete interval computation for depth 15, residue 27619. -/
theorem bounds_15_27619 : exactInterval 15 27619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27619 : oddCount 27619 15 = 5 ∧ acceleratedOrbit 15 27619 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27619) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27619.1, data_15_27619.2]

/-- Complete interval computation for depth 15, residue 27620. -/
theorem bounds_15_27620 : exactInterval 15 27620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27620 : oddCount 27620 15 = 8 ∧ acceleratedOrbit 15 27620 = 5534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27620) = 3 ^ 8 * m + 5534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27620.1, data_15_27620.2]

/-- Complete interval computation for depth 15, residue 27621. -/
theorem bounds_15_27621 : exactInterval 15 27621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27621 : oddCount 27621 15 = 8 ∧ acceleratedOrbit 15 27621 = 5534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27621) = 3 ^ 8 * m + 5534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27621.1, data_15_27621.2]

/-- Complete interval computation for depth 15, residue 27622. -/
theorem bounds_15_27622 : exactInterval 15 27622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27622 : oddCount 27622 15 = 8 ∧ acceleratedOrbit 15 27622 = 5534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27622) = 3 ^ 8 * m + 5534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27622.1, data_15_27622.2]

end Collatz.Research.PassageAtlas.Batch0843
