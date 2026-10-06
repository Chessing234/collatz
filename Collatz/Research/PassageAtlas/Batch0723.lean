import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0723

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23658. -/
theorem bounds_15_23658 : exactInterval 15 23658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23658 : oddCount 23658 15 = 3 ∧ acceleratedOrbit 15 23658 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23658) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23658.1, data_15_23658.2]

/-- Complete interval computation for depth 15, residue 23659. -/
theorem bounds_15_23659 : exactInterval 15 23659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23659 : oddCount 23659 15 = 9 ∧ acceleratedOrbit 15 23659 = 14213 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23659) = 3 ^ 9 * m + 14213 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23659.1, data_15_23659.2]

/-- Complete interval computation for depth 15, residue 23660. -/
theorem bounds_15_23660 : exactInterval 15 23660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23660 : oddCount 23660 15 = 11 ∧ acceleratedOrbit 15 23660 = 127939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23660) = 3 ^ 11 * m + 127939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23660.1, data_15_23660.2]

/-- Complete interval computation for depth 15, residue 23661. -/
theorem bounds_15_23661 : exactInterval 15 23661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23661 : oddCount 23661 15 = 11 ∧ acceleratedOrbit 15 23661 = 127939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23661) = 3 ^ 11 * m + 127939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23661.1, data_15_23661.2]

/-- Complete interval computation for depth 15, residue 23662. -/
theorem bounds_15_23662 : exactInterval 15 23662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23662 : oddCount 23662 15 = 11 ∧ acceleratedOrbit 15 23662 = 127939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23662) = 3 ^ 11 * m + 127939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23662.1, data_15_23662.2]

/-- Complete interval computation for depth 15, residue 23663. -/
theorem bounds_15_23663 : exactInterval 15 23663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23663 : oddCount 23663 15 = 10 ∧ acceleratedOrbit 15 23663 = 42644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23663) = 3 ^ 10 * m + 42644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23663.1, data_15_23663.2]

/-- Complete interval computation for depth 15, residue 23664. -/
theorem bounds_15_23664 : exactInterval 15 23664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23664 : oddCount 23664 15 = 6 ∧ acceleratedOrbit 15 23664 = 527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23664) = 3 ^ 6 * m + 527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23664.1, data_15_23664.2]

/-- Complete interval computation for depth 15, residue 23665. -/
theorem bounds_15_23665 : exactInterval 15 23665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23665 : oddCount 23665 15 = 3 ∧ acceleratedOrbit 15 23665 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23665) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23665.1, data_15_23665.2]

/-- Complete interval computation for depth 15, residue 23666. -/
theorem bounds_15_23666 : exactInterval 15 23666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23666 : oddCount 23666 15 = 7 ∧ acceleratedOrbit 15 23666 = 1580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23666) = 3 ^ 7 * m + 1580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23666.1, data_15_23666.2]

/-- Complete interval computation for depth 15, residue 23667. -/
theorem bounds_15_23667 : exactInterval 15 23667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23667 : oddCount 23667 15 = 7 ∧ acceleratedOrbit 15 23667 = 1580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23667) = 3 ^ 7 * m + 1580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23667.1, data_15_23667.2]

/-- Complete interval computation for depth 15, residue 23668. -/
theorem bounds_15_23668 : exactInterval 15 23668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23668 : oddCount 23668 15 = 6 ∧ acceleratedOrbit 15 23668 = 527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23668) = 3 ^ 6 * m + 527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23668.1, data_15_23668.2]

/-- Complete interval computation for depth 15, residue 23669. -/
theorem bounds_15_23669 : exactInterval 15 23669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23669 : oddCount 23669 15 = 6 ∧ acceleratedOrbit 15 23669 = 527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23669) = 3 ^ 6 * m + 527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23669.1, data_15_23669.2]

/-- Complete interval computation for depth 15, residue 23670. -/
theorem bounds_15_23670 : exactInterval 15 23670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23670 : oddCount 23670 15 = 8 ∧ acceleratedOrbit 15 23670 = 4742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23670) = 3 ^ 8 * m + 4742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23670.1, data_15_23670.2]

/-- Complete interval computation for depth 15, residue 23671. -/
theorem bounds_15_23671 : exactInterval 15 23671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23671 : oddCount 23671 15 = 8 ∧ acceleratedOrbit 15 23671 = 4742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23671) = 3 ^ 8 * m + 4742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23671.1, data_15_23671.2]

/-- Complete interval computation for depth 15, residue 23672. -/
theorem bounds_15_23672 : exactInterval 15 23672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23672 : oddCount 23672 15 = 6 ∧ acceleratedOrbit 15 23672 = 527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23672) = 3 ^ 6 * m + 527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23672.1, data_15_23672.2]

/-- Complete interval computation for depth 15, residue 23673. -/
theorem bounds_15_23673 : exactInterval 15 23673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23673 : oddCount 23673 15 = 9 ∧ acceleratedOrbit 15 23673 = 14222 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23673) = 3 ^ 9 * m + 14222 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23673.1, data_15_23673.2]

/-- Complete interval computation for depth 15, residue 23674. -/
theorem bounds_15_23674 : exactInterval 15 23674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23674 : oddCount 23674 15 = 6 ∧ acceleratedOrbit 15 23674 = 527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23674) = 3 ^ 6 * m + 527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23674.1, data_15_23674.2]

/-- Complete interval computation for depth 15, residue 23675. -/
theorem bounds_15_23675 : exactInterval 15 23675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23675 : oddCount 23675 15 = 8 ∧ acceleratedOrbit 15 23675 = 4742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23675) = 3 ^ 8 * m + 4742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23675.1, data_15_23675.2]

/-- Complete interval computation for depth 15, residue 23676. -/
theorem bounds_15_23676 : exactInterval 15 23676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23676 : oddCount 23676 15 = 8 ∧ acceleratedOrbit 15 23676 = 4742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23676) = 3 ^ 8 * m + 4742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23676.1, data_15_23676.2]

/-- Complete interval computation for depth 15, residue 23677. -/
theorem bounds_15_23677 : exactInterval 15 23677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23677 : oddCount 23677 15 = 8 ∧ acceleratedOrbit 15 23677 = 4742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23677) = 3 ^ 8 * m + 4742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23677.1, data_15_23677.2]

/-- Complete interval computation for depth 15, residue 23678. -/
theorem bounds_15_23678 : exactInterval 15 23678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23678 : oddCount 23678 15 = 8 ∧ acceleratedOrbit 15 23678 = 4742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23678) = 3 ^ 8 * m + 4742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23678.1, data_15_23678.2]

/-- Complete interval computation for depth 15, residue 23679. -/
theorem bounds_15_23679 : exactInterval 15 23679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23679 : oddCount 23679 15 = 11 ∧ acceleratedOrbit 15 23679 = 128017 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23679) = 3 ^ 11 * m + 128017 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23679.1, data_15_23679.2]

/-- Complete interval computation for depth 15, residue 23680. -/
theorem bounds_15_23680 : exactInterval 15 23680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23680 : oddCount 23680 15 = 4 ∧ acceleratedOrbit 15 23680 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23680) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23680.1, data_15_23680.2]

/-- Complete interval computation for depth 15, residue 23681. -/
theorem bounds_15_23681 : exactInterval 15 23681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23681 : oddCount 23681 15 = 9 ∧ acceleratedOrbit 15 23681 = 14228 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23681) = 3 ^ 9 * m + 14228 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23681.1, data_15_23681.2]

/-- Complete interval computation for depth 15, residue 23682. -/
theorem bounds_15_23682 : exactInterval 15 23682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23682 : oddCount 23682 15 = 7 ∧ acceleratedOrbit 15 23682 = 1583 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23682) = 3 ^ 7 * m + 1583 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23682.1, data_15_23682.2]

/-- Complete interval computation for depth 15, residue 23683. -/
theorem bounds_15_23683 : exactInterval 15 23683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23683 : oddCount 23683 15 = 7 ∧ acceleratedOrbit 15 23683 = 1583 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23683) = 3 ^ 7 * m + 1583 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23683.1, data_15_23683.2]

/-- Complete interval computation for depth 15, residue 23684. -/
theorem bounds_15_23684 : exactInterval 15 23684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23684 : oddCount 23684 15 = 7 ∧ acceleratedOrbit 15 23684 = 1583 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23684) = 3 ^ 7 * m + 1583 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23684.1, data_15_23684.2]

/-- Complete interval computation for depth 15, residue 23685. -/
theorem bounds_15_23685 : exactInterval 15 23685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23685 : oddCount 23685 15 = 7 ∧ acceleratedOrbit 15 23685 = 1583 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23685) = 3 ^ 7 * m + 1583 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23685.1, data_15_23685.2]

/-- Complete interval computation for depth 15, residue 23686. -/
theorem bounds_15_23686 : exactInterval 15 23686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23686 : oddCount 23686 15 = 7 ∧ acceleratedOrbit 15 23686 = 1583 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23686) = 3 ^ 7 * m + 1583 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23686.1, data_15_23686.2]

/-- Complete interval computation for depth 15, residue 23687. -/
theorem bounds_15_23687 : exactInterval 15 23687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23687 : oddCount 23687 15 = 9 ∧ acceleratedOrbit 15 23687 = 14231 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23687) = 3 ^ 9 * m + 14231 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23687.1, data_15_23687.2]

/-- Complete interval computation for depth 15, residue 23688. -/
theorem bounds_15_23688 : exactInterval 15 23688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23688 : oddCount 23688 15 = 5 ∧ acceleratedOrbit 15 23688 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23688) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23688.1, data_15_23688.2]

/-- Complete interval computation for depth 15, residue 23689. -/
theorem bounds_15_23689 : exactInterval 15 23689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23689 : oddCount 23689 15 = 10 ∧ acceleratedOrbit 15 23689 = 42692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23689) = 3 ^ 10 * m + 42692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23689.1, data_15_23689.2]

/-- Complete interval computation for depth 15, residue 23690. -/
theorem bounds_15_23690 : exactInterval 15 23690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23690 : oddCount 23690 15 = 5 ∧ acceleratedOrbit 15 23690 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23690) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23690.1, data_15_23690.2]

end Collatz.Research.PassageAtlas.Batch0723
