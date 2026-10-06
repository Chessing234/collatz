import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0996

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32604. -/
theorem bounds_15_32604 : exactInterval 15 32604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32604 : oddCount 32604 15 = 9 ∧ acceleratedOrbit 15 32604 = 19592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32604) = 3 ^ 9 * m + 19592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32604.1, data_15_32604.2]

/-- Complete interval computation for depth 15, residue 32605. -/
theorem bounds_15_32605 : exactInterval 15 32605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32605 : oddCount 32605 15 = 9 ∧ acceleratedOrbit 15 32605 = 19592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32605) = 3 ^ 9 * m + 19592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32605.1, data_15_32605.2]

/-- Complete interval computation for depth 15, residue 32606. -/
theorem bounds_15_32606 : exactInterval 15 32606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32606 : oddCount 32606 15 = 7 ∧ acceleratedOrbit 15 32606 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32606) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32606.1, data_15_32606.2]

/-- Complete interval computation for depth 15, residue 32607. -/
theorem bounds_15_32607 : exactInterval 15 32607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32607 : oddCount 32607 15 = 7 ∧ acceleratedOrbit 15 32607 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32607) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32607.1, data_15_32607.2]

/-- Complete interval computation for depth 15, residue 32608. -/
theorem bounds_15_32608 : exactInterval 15 32608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32608 : oddCount 32608 15 = 7 ∧ acceleratedOrbit 15 32608 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32608) = 3 ^ 7 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32608.1, data_15_32608.2]

/-- Complete interval computation for depth 15, residue 32609. -/
theorem bounds_15_32609 : exactInterval 15 32609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32609 : oddCount 32609 15 = 10 ∧ acceleratedOrbit 15 32609 = 58769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32609) = 3 ^ 10 * m + 58769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32609.1, data_15_32609.2]

/-- Complete interval computation for depth 15, residue 32610. -/
theorem bounds_15_32610 : exactInterval 15 32610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32610 : oddCount 32610 15 = 6 ∧ acceleratedOrbit 15 32610 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32610) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32610.1, data_15_32610.2]

/-- Complete interval computation for depth 15, residue 32611. -/
theorem bounds_15_32611 : exactInterval 15 32611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32611 : oddCount 32611 15 = 6 ∧ acceleratedOrbit 15 32611 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32611) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32611.1, data_15_32611.2]

/-- Complete interval computation for depth 15, residue 32612. -/
theorem bounds_15_32612 : exactInterval 15 32612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32612 : oddCount 32612 15 = 6 ∧ acceleratedOrbit 15 32612 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32612) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32612.1, data_15_32612.2]

/-- Complete interval computation for depth 15, residue 32613. -/
theorem bounds_15_32613 : exactInterval 15 32613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32613 : oddCount 32613 15 = 6 ∧ acceleratedOrbit 15 32613 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32613) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32613.1, data_15_32613.2]

/-- Complete interval computation for depth 15, residue 32614. -/
theorem bounds_15_32614 : exactInterval 15 32614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32614 : oddCount 32614 15 = 6 ∧ acceleratedOrbit 15 32614 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32614) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32614.1, data_15_32614.2]

/-- Complete interval computation for depth 15, residue 32615. -/
theorem bounds_15_32615 : exactInterval 15 32615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32615 : oddCount 32615 15 = 13 ∧ acceleratedOrbit 15 32615 = 1586942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32615) = 3 ^ 13 * m + 1586942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32615.1, data_15_32615.2]

/-- Complete interval computation for depth 15, residue 32616. -/
theorem bounds_15_32616 : exactInterval 15 32616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32616 : oddCount 32616 15 = 7 ∧ acceleratedOrbit 15 32616 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32616) = 3 ^ 7 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32616.1, data_15_32616.2]

/-- Complete interval computation for depth 15, residue 32617. -/
theorem bounds_15_32617 : exactInterval 15 32617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32617 : oddCount 32617 15 = 9 ∧ acceleratedOrbit 15 32617 = 19595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32617) = 3 ^ 9 * m + 19595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32617.1, data_15_32617.2]

/-- Complete interval computation for depth 15, residue 32618. -/
theorem bounds_15_32618 : exactInterval 15 32618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32618 : oddCount 32618 15 = 7 ∧ acceleratedOrbit 15 32618 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32618) = 3 ^ 7 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32618.1, data_15_32618.2]

/-- Complete interval computation for depth 15, residue 32619. -/
theorem bounds_15_32619 : exactInterval 15 32619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32619 : oddCount 32619 15 = 8 ∧ acceleratedOrbit 15 32619 = 6533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32619) = 3 ^ 8 * m + 6533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32619.1, data_15_32619.2]

/-- Complete interval computation for depth 15, residue 32620. -/
theorem bounds_15_32620 : exactInterval 15 32620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32620 : oddCount 32620 15 = 9 ∧ acceleratedOrbit 15 32620 = 19601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32620) = 3 ^ 9 * m + 19601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32620.1, data_15_32620.2]

/-- Complete interval computation for depth 15, residue 32621. -/
theorem bounds_15_32621 : exactInterval 15 32621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32621 : oddCount 32621 15 = 9 ∧ acceleratedOrbit 15 32621 = 19601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32621) = 3 ^ 9 * m + 19601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32621.1, data_15_32621.2]

/-- Complete interval computation for depth 15, residue 32622. -/
theorem bounds_15_32622 : exactInterval 15 32622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32622 : oddCount 32622 15 = 9 ∧ acceleratedOrbit 15 32622 = 19601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32622) = 3 ^ 9 * m + 19601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32622.1, data_15_32622.2]

/-- Complete interval computation for depth 15, residue 32623. -/
theorem bounds_15_32623 : exactInterval 15 32623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32623 : oddCount 32623 15 = 9 ∧ acceleratedOrbit 15 32623 = 19597 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32623) = 3 ^ 9 * m + 19597 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32623.1, data_15_32623.2]

/-- Complete interval computation for depth 15, residue 32624. -/
theorem bounds_15_32624 : exactInterval 15 32624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32624 : oddCount 32624 15 = 7 ∧ acceleratedOrbit 15 32624 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32624) = 3 ^ 7 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32624.1, data_15_32624.2]

/-- Complete interval computation for depth 15, residue 32625. -/
theorem bounds_15_32625 : exactInterval 15 32625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32625 : oddCount 32625 15 = 7 ∧ acceleratedOrbit 15 32625 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32625) = 3 ^ 7 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32625.1, data_15_32625.2]

/-- Complete interval computation for depth 15, residue 32626. -/
theorem bounds_15_32626 : exactInterval 15 32626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32626 : oddCount 32626 15 = 5 ∧ acceleratedOrbit 15 32626 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32626) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32626.1, data_15_32626.2]

/-- Complete interval computation for depth 15, residue 32627. -/
theorem bounds_15_32627 : exactInterval 15 32627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32627 : oddCount 32627 15 = 5 ∧ acceleratedOrbit 15 32627 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32627) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32627.1, data_15_32627.2]

/-- Complete interval computation for depth 15, residue 32628. -/
theorem bounds_15_32628 : exactInterval 15 32628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32628 : oddCount 32628 15 = 7 ∧ acceleratedOrbit 15 32628 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32628) = 3 ^ 7 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32628.1, data_15_32628.2]

/-- Complete interval computation for depth 15, residue 32629. -/
theorem bounds_15_32629 : exactInterval 15 32629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32629 : oddCount 32629 15 = 7 ∧ acceleratedOrbit 15 32629 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32629) = 3 ^ 7 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32629.1, data_15_32629.2]

/-- Complete interval computation for depth 15, residue 32630. -/
theorem bounds_15_32630 : exactInterval 15 32630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32630 : oddCount 32630 15 = 5 ∧ acceleratedOrbit 15 32630 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32630) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32630.1, data_15_32630.2]

/-- Complete interval computation for depth 15, residue 32631. -/
theorem bounds_15_32631 : exactInterval 15 32631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32631 : oddCount 32631 15 = 5 ∧ acceleratedOrbit 15 32631 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32631) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32631.1, data_15_32631.2]

/-- Complete interval computation for depth 15, residue 32632. -/
theorem bounds_15_32632 : exactInterval 15 32632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32632 : oddCount 32632 15 = 8 ∧ acceleratedOrbit 15 32632 = 6536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32632) = 3 ^ 8 * m + 6536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32632.1, data_15_32632.2]

/-- Complete interval computation for depth 15, residue 32633. -/
theorem bounds_15_32633 : exactInterval 15 32633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32633 : oddCount 32633 15 = 9 ∧ acceleratedOrbit 15 32633 = 19604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32633) = 3 ^ 9 * m + 19604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32633.1, data_15_32633.2]

/-- Complete interval computation for depth 15, residue 32634. -/
theorem bounds_15_32634 : exactInterval 15 32634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32634 : oddCount 32634 15 = 8 ∧ acceleratedOrbit 15 32634 = 6536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32634) = 3 ^ 8 * m + 6536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32634.1, data_15_32634.2]

/-- Complete interval computation for depth 15, residue 32635. -/
theorem bounds_15_32635 : exactInterval 15 32635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32635 : oddCount 32635 15 = 8 ∧ acceleratedOrbit 15 32635 = 6535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32635) = 3 ^ 8 * m + 6535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32635.1, data_15_32635.2]

end Collatz.Research.PassageAtlas.Batch0996
