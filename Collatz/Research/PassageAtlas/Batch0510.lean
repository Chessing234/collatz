import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0510

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16678. -/
theorem bounds_15_16678 : exactInterval 15 16678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16678 : oddCount 16678 15 = 8 ∧ acceleratedOrbit 15 16678 = 3341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16678) = 3 ^ 8 * m + 3341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16678.1, data_15_16678.2]

/-- Complete interval computation for depth 15, residue 16679. -/
theorem bounds_15_16679 : exactInterval 15 16679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16679 : oddCount 16679 15 = 8 ∧ acceleratedOrbit 15 16679 = 3340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16679) = 3 ^ 8 * m + 3340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16679.1, data_15_16679.2]

/-- Complete interval computation for depth 15, residue 16680. -/
theorem bounds_15_16680 : exactInterval 15 16680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16680 : oddCount 16680 15 = 5 ∧ acceleratedOrbit 15 16680 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16680) = 3 ^ 5 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16680.1, data_15_16680.2]

/-- Complete interval computation for depth 15, residue 16681. -/
theorem bounds_15_16681 : exactInterval 15 16681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16681 : oddCount 16681 15 = 10 ∧ acceleratedOrbit 15 16681 = 30064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16681) = 3 ^ 10 * m + 30064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16681.1, data_15_16681.2]

/-- Complete interval computation for depth 15, residue 16682. -/
theorem bounds_15_16682 : exactInterval 15 16682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16682 : oddCount 16682 15 = 5 ∧ acceleratedOrbit 15 16682 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16682) = 3 ^ 5 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16682.1, data_15_16682.2]

/-- Complete interval computation for depth 15, residue 16683. -/
theorem bounds_15_16683 : exactInterval 15 16683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16683 : oddCount 16683 15 = 10 ∧ acceleratedOrbit 15 16683 = 30071 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16683) = 3 ^ 10 * m + 30071 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16683.1, data_15_16683.2]

/-- Complete interval computation for depth 15, residue 16684. -/
theorem bounds_15_16684 : exactInterval 15 16684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16684 : oddCount 16684 15 = 5 ∧ acceleratedOrbit 15 16684 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16684) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16684.1, data_15_16684.2]

/-- Complete interval computation for depth 15, residue 16685. -/
theorem bounds_15_16685 : exactInterval 15 16685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16685 : oddCount 16685 15 = 5 ∧ acceleratedOrbit 15 16685 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16685) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16685.1, data_15_16685.2]

/-- Complete interval computation for depth 15, residue 16686. -/
theorem bounds_15_16686 : exactInterval 15 16686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16686 : oddCount 16686 15 = 5 ∧ acceleratedOrbit 15 16686 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16686) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16686.1, data_15_16686.2]

/-- Complete interval computation for depth 15, residue 16687. -/
theorem bounds_15_16687 : exactInterval 15 16687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16687 : oddCount 16687 15 = 9 ∧ acceleratedOrbit 15 16687 = 10025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16687) = 3 ^ 9 * m + 10025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16687.1, data_15_16687.2]

/-- Complete interval computation for depth 15, residue 16688. -/
theorem bounds_15_16688 : exactInterval 15 16688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16688 : oddCount 16688 15 = 5 ∧ acceleratedOrbit 15 16688 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16688) = 3 ^ 5 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16688.1, data_15_16688.2]

/-- Complete interval computation for depth 15, residue 16689. -/
theorem bounds_15_16689 : exactInterval 15 16689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16689 : oddCount 16689 15 = 7 ∧ acceleratedOrbit 15 16689 = 1115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16689) = 3 ^ 7 * m + 1115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16689.1, data_15_16689.2]

/-- Complete interval computation for depth 15, residue 16690. -/
theorem bounds_15_16690 : exactInterval 15 16690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16690 : oddCount 16690 15 = 7 ∧ acceleratedOrbit 15 16690 = 1115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16690) = 3 ^ 7 * m + 1115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16690.1, data_15_16690.2]

/-- Complete interval computation for depth 15, residue 16691. -/
theorem bounds_15_16691 : exactInterval 15 16691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16691 : oddCount 16691 15 = 7 ∧ acceleratedOrbit 15 16691 = 1115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16691) = 3 ^ 7 * m + 1115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16691.1, data_15_16691.2]

/-- Complete interval computation for depth 15, residue 16692. -/
theorem bounds_15_16692 : exactInterval 15 16692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16692 : oddCount 16692 15 = 5 ∧ acceleratedOrbit 15 16692 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16692) = 3 ^ 5 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16692.1, data_15_16692.2]

/-- Complete interval computation for depth 15, residue 16693. -/
theorem bounds_15_16693 : exactInterval 15 16693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16693 : oddCount 16693 15 = 5 ∧ acceleratedOrbit 15 16693 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16693) = 3 ^ 5 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16693.1, data_15_16693.2]

/-- Complete interval computation for depth 15, residue 16694. -/
theorem bounds_15_16694 : exactInterval 15 16694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16694 : oddCount 16694 15 = 9 ∧ acceleratedOrbit 15 16694 = 10030 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16694) = 3 ^ 9 * m + 10030 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16694.1, data_15_16694.2]

/-- Complete interval computation for depth 15, residue 16695. -/
theorem bounds_15_16695 : exactInterval 15 16695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16695 : oddCount 16695 15 = 9 ∧ acceleratedOrbit 15 16695 = 10030 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16695) = 3 ^ 9 * m + 10030 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16695.1, data_15_16695.2]

/-- Complete interval computation for depth 15, residue 16696. -/
theorem bounds_15_16696 : exactInterval 15 16696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16696 : oddCount 16696 15 = 8 ∧ acceleratedOrbit 15 16696 = 3347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16696) = 3 ^ 8 * m + 3347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16696.1, data_15_16696.2]

/-- Complete interval computation for depth 15, residue 16697. -/
theorem bounds_15_16697 : exactInterval 15 16697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16697 : oddCount 16697 15 = 10 ∧ acceleratedOrbit 15 16697 = 30095 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16697) = 3 ^ 10 * m + 30095 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16697.1, data_15_16697.2]

/-- Complete interval computation for depth 15, residue 16698. -/
theorem bounds_15_16698 : exactInterval 15 16698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16698 : oddCount 16698 15 = 8 ∧ acceleratedOrbit 15 16698 = 3347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16698) = 3 ^ 8 * m + 3347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16698.1, data_15_16698.2]

/-- Complete interval computation for depth 15, residue 16699. -/
theorem bounds_15_16699 : exactInterval 15 16699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16699 : oddCount 16699 15 = 8 ∧ acceleratedOrbit 15 16699 = 3347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16699) = 3 ^ 8 * m + 3347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16699.1, data_15_16699.2]

/-- Complete interval computation for depth 15, residue 16700. -/
theorem bounds_15_16700 : exactInterval 15 16700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16700 : oddCount 16700 15 = 8 ∧ acceleratedOrbit 15 16700 = 3347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16700) = 3 ^ 8 * m + 3347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16700.1, data_15_16700.2]

/-- Complete interval computation for depth 15, residue 16701. -/
theorem bounds_15_16701 : exactInterval 15 16701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16701 : oddCount 16701 15 = 8 ∧ acceleratedOrbit 15 16701 = 3347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16701) = 3 ^ 8 * m + 3347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16701.1, data_15_16701.2]

/-- Complete interval computation for depth 15, residue 16702. -/
theorem bounds_15_16702 : exactInterval 15 16702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16702 : oddCount 16702 15 = 11 ∧ acceleratedOrbit 15 16702 = 90305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16702) = 3 ^ 11 * m + 90305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16702.1, data_15_16702.2]

/-- Complete interval computation for depth 15, residue 16703. -/
theorem bounds_15_16703 : exactInterval 15 16703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16703 : oddCount 16703 15 = 11 ∧ acceleratedOrbit 15 16703 = 90305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16703) = 3 ^ 11 * m + 90305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16703.1, data_15_16703.2]

/-- Complete interval computation for depth 15, residue 16704. -/
theorem bounds_15_16704 : exactInterval 15 16704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16704 : oddCount 16704 15 = 3 ∧ acceleratedOrbit 15 16704 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16704) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16704.1, data_15_16704.2]

/-- Complete interval computation for depth 15, residue 16705. -/
theorem bounds_15_16705 : exactInterval 15 16705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16705 : oddCount 16705 15 = 5 ∧ acceleratedOrbit 15 16705 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16705) = 3 ^ 5 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16705.1, data_15_16705.2]

/-- Complete interval computation for depth 15, residue 16706. -/
theorem bounds_15_16706 : exactInterval 15 16706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16706 : oddCount 16706 15 = 9 ∧ acceleratedOrbit 15 16706 = 10039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16706) = 3 ^ 9 * m + 10039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16706.1, data_15_16706.2]

/-- Complete interval computation for depth 15, residue 16707. -/
theorem bounds_15_16707 : exactInterval 15 16707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16707 : oddCount 16707 15 = 9 ∧ acceleratedOrbit 15 16707 = 10039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16707) = 3 ^ 9 * m + 10039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16707.1, data_15_16707.2]

/-- Complete interval computation for depth 15, residue 16708. -/
theorem bounds_15_16708 : exactInterval 15 16708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16708 : oddCount 16708 15 = 5 ∧ acceleratedOrbit 15 16708 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16708) = 3 ^ 5 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16708.1, data_15_16708.2]

/-- Complete interval computation for depth 15, residue 16709. -/
theorem bounds_15_16709 : exactInterval 15 16709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16709 : oddCount 16709 15 = 5 ∧ acceleratedOrbit 15 16709 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16709) = 3 ^ 5 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16709.1, data_15_16709.2]

/-- Complete interval computation for depth 15, residue 16710. -/
theorem bounds_15_16710 : exactInterval 15 16710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16710 : oddCount 16710 15 = 5 ∧ acceleratedOrbit 15 16710 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16710) = 3 ^ 5 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16710.1, data_15_16710.2]

end Collatz.Research.PassageAtlas.Batch0510
