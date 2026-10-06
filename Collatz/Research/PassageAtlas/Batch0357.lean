import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0357

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11665. -/
theorem bounds_15_11665 : exactInterval 15 11665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11665 : oddCount 11665 15 = 8 ∧ acceleratedOrbit 15 11665 = 2339 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11665) = 3 ^ 8 * m + 2339 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11665.1, data_15_11665.2]

/-- Complete interval computation for depth 15, residue 11666. -/
theorem bounds_15_11666 : exactInterval 15 11666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11666 : oddCount 11666 15 = 8 ∧ acceleratedOrbit 15 11666 = 2339 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11666) = 3 ^ 8 * m + 2339 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11666.1, data_15_11666.2]

/-- Complete interval computation for depth 15, residue 11667. -/
theorem bounds_15_11667 : exactInterval 15 11667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11667 : oddCount 11667 15 = 8 ∧ acceleratedOrbit 15 11667 = 2339 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11667) = 3 ^ 8 * m + 2339 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11667.1, data_15_11667.2]

/-- Complete interval computation for depth 15, residue 11668. -/
theorem bounds_15_11668 : exactInterval 15 11668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11668 : oddCount 11668 15 = 4 ∧ acceleratedOrbit 15 11668 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11668) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11668.1, data_15_11668.2]

/-- Complete interval computation for depth 15, residue 11669. -/
theorem bounds_15_11669 : exactInterval 15 11669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11669 : oddCount 11669 15 = 4 ∧ acceleratedOrbit 15 11669 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11669) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11669.1, data_15_11669.2]

/-- Complete interval computation for depth 15, residue 11670. -/
theorem bounds_15_11670 : exactInterval 15 11670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11670 : oddCount 11670 15 = 8 ∧ acceleratedOrbit 15 11670 = 2339 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11670) = 3 ^ 8 * m + 2339 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11670.1, data_15_11670.2]

/-- Complete interval computation for depth 15, residue 11671. -/
theorem bounds_15_11671 : exactInterval 15 11671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11671 : oddCount 11671 15 = 8 ∧ acceleratedOrbit 15 11671 = 2339 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11671) = 3 ^ 8 * m + 2339 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11671.1, data_15_11671.2]

/-- Complete interval computation for depth 15, residue 11672. -/
theorem bounds_15_11672 : exactInterval 15 11672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11672 : oddCount 11672 15 = 4 ∧ acceleratedOrbit 15 11672 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11672) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11672.1, data_15_11672.2]

/-- Complete interval computation for depth 15, residue 11673. -/
theorem bounds_15_11673 : exactInterval 15 11673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11673 : oddCount 11673 15 = 8 ∧ acceleratedOrbit 15 11673 = 2339 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11673) = 3 ^ 8 * m + 2339 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11673.1, data_15_11673.2]

/-- Complete interval computation for depth 15, residue 11674. -/
theorem bounds_15_11674 : exactInterval 15 11674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11674 : oddCount 11674 15 = 4 ∧ acceleratedOrbit 15 11674 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11674) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11674.1, data_15_11674.2]

/-- Complete interval computation for depth 15, residue 11675. -/
theorem bounds_15_11675 : exactInterval 15 11675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11675 : oddCount 11675 15 = 8 ∧ acceleratedOrbit 15 11675 = 2338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11675) = 3 ^ 8 * m + 2338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11675.1, data_15_11675.2]

/-- Complete interval computation for depth 15, residue 11676. -/
theorem bounds_15_11676 : exactInterval 15 11676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11676 : oddCount 11676 15 = 10 ∧ acceleratedOrbit 15 11676 = 21050 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11676) = 3 ^ 10 * m + 21050 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11676.1, data_15_11676.2]

/-- Complete interval computation for depth 15, residue 11677. -/
theorem bounds_15_11677 : exactInterval 15 11677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11677 : oddCount 11677 15 = 10 ∧ acceleratedOrbit 15 11677 = 21050 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11677) = 3 ^ 10 * m + 21050 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11677.1, data_15_11677.2]

/-- Complete interval computation for depth 15, residue 11678. -/
theorem bounds_15_11678 : exactInterval 15 11678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11678 : oddCount 11678 15 = 10 ∧ acceleratedOrbit 15 11678 = 21050 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11678) = 3 ^ 10 * m + 21050 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11678.1, data_15_11678.2]

/-- Complete interval computation for depth 15, residue 11679. -/
theorem bounds_15_11679 : exactInterval 15 11679 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11679) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11679 : oddCount 11679 15 = 9 ∧ acceleratedOrbit 15 11679 = 7016 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11679) = 3 ^ 9 * m + 7016 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11679.1, data_15_11679.2]

/-- Complete interval computation for depth 15, residue 11680. -/
theorem bounds_15_11680 : exactInterval 15 11680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11680 : oddCount 11680 15 = 6 ∧ acceleratedOrbit 15 11680 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11680) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11680.1, data_15_11680.2]

/-- Complete interval computation for depth 15, residue 11681. -/
theorem bounds_15_11681 : exactInterval 15 11681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11681 : oddCount 11681 15 = 10 ∧ acceleratedOrbit 15 11681 = 21059 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11681) = 3 ^ 10 * m + 21059 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11681.1, data_15_11681.2]

/-- Complete interval computation for depth 15, residue 11682. -/
theorem bounds_15_11682 : exactInterval 15 11682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11682 : oddCount 11682 15 = 8 ∧ acceleratedOrbit 15 11682 = 2342 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11682) = 3 ^ 8 * m + 2342 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11682.1, data_15_11682.2]

/-- Complete interval computation for depth 15, residue 11683. -/
theorem bounds_15_11683 : exactInterval 15 11683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11683 : oddCount 11683 15 = 8 ∧ acceleratedOrbit 15 11683 = 2342 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11683) = 3 ^ 8 * m + 2342 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11683.1, data_15_11683.2]

/-- Complete interval computation for depth 15, residue 11684. -/
theorem bounds_15_11684 : exactInterval 15 11684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11684 : oddCount 11684 15 = 8 ∧ acceleratedOrbit 15 11684 = 2342 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11684) = 3 ^ 8 * m + 2342 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11684.1, data_15_11684.2]

/-- Complete interval computation for depth 15, residue 11685. -/
theorem bounds_15_11685 : exactInterval 15 11685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11685 : oddCount 11685 15 = 8 ∧ acceleratedOrbit 15 11685 = 2342 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11685) = 3 ^ 8 * m + 2342 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11685.1, data_15_11685.2]

/-- Complete interval computation for depth 15, residue 11686. -/
theorem bounds_15_11686 : exactInterval 15 11686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11686 : oddCount 11686 15 = 8 ∧ acceleratedOrbit 15 11686 = 2342 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11686) = 3 ^ 8 * m + 2342 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11686.1, data_15_11686.2]

/-- Complete interval computation for depth 15, residue 11687. -/
theorem bounds_15_11687 : exactInterval 15 11687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11687 : oddCount 11687 15 = 9 ∧ acceleratedOrbit 15 11687 = 7022 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11687) = 3 ^ 9 * m + 7022 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11687.1, data_15_11687.2]

/-- Complete interval computation for depth 15, residue 11688. -/
theorem bounds_15_11688 : exactInterval 15 11688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11688 : oddCount 11688 15 = 6 ∧ acceleratedOrbit 15 11688 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11688) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11688.1, data_15_11688.2]

/-- Complete interval computation for depth 15, residue 11689. -/
theorem bounds_15_11689 : exactInterval 15 11689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11689 : oddCount 11689 15 = 8 ∧ acceleratedOrbit 15 11689 = 2341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11689) = 3 ^ 8 * m + 2341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11689.1, data_15_11689.2]

/-- Complete interval computation for depth 15, residue 11690. -/
theorem bounds_15_11690 : exactInterval 15 11690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11690 : oddCount 11690 15 = 6 ∧ acceleratedOrbit 15 11690 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11690) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11690.1, data_15_11690.2]

/-- Complete interval computation for depth 15, residue 11691. -/
theorem bounds_15_11691 : exactInterval 15 11691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11691 : oddCount 11691 15 = 10 ∧ acceleratedOrbit 15 11691 = 21073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11691) = 3 ^ 10 * m + 21073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11691.1, data_15_11691.2]

/-- Complete interval computation for depth 15, residue 11692. -/
theorem bounds_15_11692 : exactInterval 15 11692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11692 : oddCount 11692 15 = 7 ∧ acceleratedOrbit 15 11692 = 782 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11692) = 3 ^ 7 * m + 782 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11692.1, data_15_11692.2]

/-- Complete interval computation for depth 15, residue 11693. -/
theorem bounds_15_11693 : exactInterval 15 11693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11693 : oddCount 11693 15 = 7 ∧ acceleratedOrbit 15 11693 = 782 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11693) = 3 ^ 7 * m + 782 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11693.1, data_15_11693.2]

/-- Complete interval computation for depth 15, residue 11694. -/
theorem bounds_15_11694 : exactInterval 15 11694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11694 : oddCount 11694 15 = 7 ∧ acceleratedOrbit 15 11694 = 782 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11694) = 3 ^ 7 * m + 782 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11694.1, data_15_11694.2]

/-- Complete interval computation for depth 15, residue 11695. -/
theorem bounds_15_11695 : exactInterval 15 11695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11695 : oddCount 11695 15 = 10 ∧ acceleratedOrbit 15 11695 = 21080 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11695) = 3 ^ 10 * m + 21080 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11695.1, data_15_11695.2]

/-- Complete interval computation for depth 15, residue 11696. -/
theorem bounds_15_11696 : exactInterval 15 11696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11696 : oddCount 11696 15 = 8 ∧ acceleratedOrbit 15 11696 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11696) = 3 ^ 8 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11696.1, data_15_11696.2]

/-- Complete interval computation for depth 15, residue 11697. -/
theorem bounds_15_11697 : exactInterval 15 11697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11697 : oddCount 11697 15 = 8 ∧ acceleratedOrbit 15 11697 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11697) = 3 ^ 8 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11697.1, data_15_11697.2]

end Collatz.Research.PassageAtlas.Batch0357
