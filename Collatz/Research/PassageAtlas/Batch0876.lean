import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0876

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28672. -/
theorem bounds_15_28672 : exactInterval 15 28672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28672 : oddCount 28672 15 = 3 ∧ acceleratedOrbit 15 28672 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28672) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28672.1, data_15_28672.2]

/-- Complete interval computation for depth 15, residue 28673. -/
theorem bounds_15_28673 : exactInterval 15 28673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28673 : oddCount 28673 15 = 6 ∧ acceleratedOrbit 15 28673 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28673) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28673.1, data_15_28673.2]

/-- Complete interval computation for depth 15, residue 28674. -/
theorem bounds_15_28674 : exactInterval 15 28674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28674 : oddCount 28674 15 = 8 ∧ acceleratedOrbit 15 28674 = 5744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28674) = 3 ^ 8 * m + 5744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28674.1, data_15_28674.2]

/-- Complete interval computation for depth 15, residue 28675. -/
theorem bounds_15_28675 : exactInterval 15 28675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28675 : oddCount 28675 15 = 8 ∧ acceleratedOrbit 15 28675 = 5744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28675) = 3 ^ 8 * m + 5744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28675.1, data_15_28675.2]

/-- Complete interval computation for depth 15, residue 28676. -/
theorem bounds_15_28676 : exactInterval 15 28676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28676 : oddCount 28676 15 = 7 ∧ acceleratedOrbit 15 28676 = 1916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28676) = 3 ^ 7 * m + 1916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28676.1, data_15_28676.2]

/-- Complete interval computation for depth 15, residue 28677. -/
theorem bounds_15_28677 : exactInterval 15 28677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28677 : oddCount 28677 15 = 7 ∧ acceleratedOrbit 15 28677 = 1916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28677) = 3 ^ 7 * m + 1916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28677.1, data_15_28677.2]

/-- Complete interval computation for depth 15, residue 28678. -/
theorem bounds_15_28678 : exactInterval 15 28678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28678 : oddCount 28678 15 = 7 ∧ acceleratedOrbit 15 28678 = 1916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28678) = 3 ^ 7 * m + 1916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28678.1, data_15_28678.2]

/-- Complete interval computation for depth 15, residue 28679. -/
theorem bounds_15_28679 : exactInterval 15 28679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28679 : oddCount 28679 15 = 8 ∧ acceleratedOrbit 15 28679 = 5744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28679) = 3 ^ 8 * m + 5744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28679.1, data_15_28679.2]

/-- Complete interval computation for depth 15, residue 28680. -/
theorem bounds_15_28680 : exactInterval 15 28680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28680 : oddCount 28680 15 = 8 ∧ acceleratedOrbit 15 28680 = 5750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28680) = 3 ^ 8 * m + 5750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28680.1, data_15_28680.2]

/-- Complete interval computation for depth 15, residue 28681. -/
theorem bounds_15_28681 : exactInterval 15 28681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28681 : oddCount 28681 15 = 8 ∧ acceleratedOrbit 15 28681 = 5744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28681) = 3 ^ 8 * m + 5744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28681.1, data_15_28681.2]

/-- Complete interval computation for depth 15, residue 28682. -/
theorem bounds_15_28682 : exactInterval 15 28682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28682 : oddCount 28682 15 = 8 ∧ acceleratedOrbit 15 28682 = 5750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28682) = 3 ^ 8 * m + 5750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28682.1, data_15_28682.2]

/-- Complete interval computation for depth 15, residue 28683. -/
theorem bounds_15_28683 : exactInterval 15 28683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28683 : oddCount 28683 15 = 7 ∧ acceleratedOrbit 15 28683 = 1916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28683) = 3 ^ 7 * m + 1916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28683.1, data_15_28683.2]

/-- Complete interval computation for depth 15, residue 28684. -/
theorem bounds_15_28684 : exactInterval 15 28684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28684 : oddCount 28684 15 = 8 ∧ acceleratedOrbit 15 28684 = 5750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28684) = 3 ^ 8 * m + 5750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28684.1, data_15_28684.2]

/-- Complete interval computation for depth 15, residue 28685. -/
theorem bounds_15_28685 : exactInterval 15 28685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28685 : oddCount 28685 15 = 8 ∧ acceleratedOrbit 15 28685 = 5750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28685) = 3 ^ 8 * m + 5750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28685.1, data_15_28685.2]

/-- Complete interval computation for depth 15, residue 28686. -/
theorem bounds_15_28686 : exactInterval 15 28686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28686 : oddCount 28686 15 = 7 ∧ acceleratedOrbit 15 28686 = 1916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28686) = 3 ^ 7 * m + 1916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28686.1, data_15_28686.2]

/-- Complete interval computation for depth 15, residue 28687. -/
theorem bounds_15_28687 : exactInterval 15 28687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28687 : oddCount 28687 15 = 7 ∧ acceleratedOrbit 15 28687 = 1916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28687) = 3 ^ 7 * m + 1916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28687.1, data_15_28687.2]

/-- Complete interval computation for depth 15, residue 28688. -/
theorem bounds_15_28688 : exactInterval 15 28688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28688 : oddCount 28688 15 = 4 ∧ acceleratedOrbit 15 28688 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28688) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28688.1, data_15_28688.2]

/-- Complete interval computation for depth 15, residue 28689. -/
theorem bounds_15_28689 : exactInterval 15 28689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28689 : oddCount 28689 15 = 8 ∧ acceleratedOrbit 15 28689 = 5750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28689) = 3 ^ 8 * m + 5750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28689.1, data_15_28689.2]

/-- Complete interval computation for depth 15, residue 28690. -/
theorem bounds_15_28690 : exactInterval 15 28690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28690 : oddCount 28690 15 = 8 ∧ acceleratedOrbit 15 28690 = 5746 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28690) = 3 ^ 8 * m + 5746 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28690.1, data_15_28690.2]

/-- Complete interval computation for depth 15, residue 28691. -/
theorem bounds_15_28691 : exactInterval 15 28691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28691 : oddCount 28691 15 = 8 ∧ acceleratedOrbit 15 28691 = 5746 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28691) = 3 ^ 8 * m + 5746 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28691.1, data_15_28691.2]

/-- Complete interval computation for depth 15, residue 28692. -/
theorem bounds_15_28692 : exactInterval 15 28692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28692 : oddCount 28692 15 = 4 ∧ acceleratedOrbit 15 28692 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28692) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28692.1, data_15_28692.2]

/-- Complete interval computation for depth 15, residue 28693. -/
theorem bounds_15_28693 : exactInterval 15 28693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28693 : oddCount 28693 15 = 4 ∧ acceleratedOrbit 15 28693 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28693) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28693.1, data_15_28693.2]

/-- Complete interval computation for depth 15, residue 28694. -/
theorem bounds_15_28694 : exactInterval 15 28694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28694 : oddCount 28694 15 = 8 ∧ acceleratedOrbit 15 28694 = 5750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28694) = 3 ^ 8 * m + 5750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28694.1, data_15_28694.2]

/-- Complete interval computation for depth 15, residue 28695. -/
theorem bounds_15_28695 : exactInterval 15 28695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28695 : oddCount 28695 15 = 8 ∧ acceleratedOrbit 15 28695 = 5750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28695) = 3 ^ 8 * m + 5750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28695.1, data_15_28695.2]

/-- Complete interval computation for depth 15, residue 28696. -/
theorem bounds_15_28696 : exactInterval 15 28696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28696 : oddCount 28696 15 = 4 ∧ acceleratedOrbit 15 28696 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28696) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28696.1, data_15_28696.2]

/-- Complete interval computation for depth 15, residue 28697. -/
theorem bounds_15_28697 : exactInterval 15 28697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28697 : oddCount 28697 15 = 7 ∧ acceleratedOrbit 15 28697 = 1916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28697) = 3 ^ 7 * m + 1916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28697.1, data_15_28697.2]

/-- Complete interval computation for depth 15, residue 28698. -/
theorem bounds_15_28698 : exactInterval 15 28698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28698 : oddCount 28698 15 = 4 ∧ acceleratedOrbit 15 28698 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28698) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28698.1, data_15_28698.2]

/-- Complete interval computation for depth 15, residue 28699. -/
theorem bounds_15_28699 : exactInterval 15 28699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28699 : oddCount 28699 15 = 11 ∧ acceleratedOrbit 15 28699 = 155159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28699) = 3 ^ 11 * m + 155159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28699.1, data_15_28699.2]

/-- Complete interval computation for depth 15, residue 28700. -/
theorem bounds_15_28700 : exactInterval 15 28700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28700 : oddCount 28700 15 = 8 ∧ acceleratedOrbit 15 28700 = 5750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28700) = 3 ^ 8 * m + 5750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28700.1, data_15_28700.2]

/-- Complete interval computation for depth 15, residue 28701. -/
theorem bounds_15_28701 : exactInterval 15 28701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28701 : oddCount 28701 15 = 8 ∧ acceleratedOrbit 15 28701 = 5750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28701) = 3 ^ 8 * m + 5750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28701.1, data_15_28701.2]

/-- Complete interval computation for depth 15, residue 28702. -/
theorem bounds_15_28702 : exactInterval 15 28702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28702 : oddCount 28702 15 = 8 ∧ acceleratedOrbit 15 28702 = 5750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28702) = 3 ^ 8 * m + 5750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28702.1, data_15_28702.2]

/-- Complete interval computation for depth 15, residue 28703. -/
theorem bounds_15_28703 : exactInterval 15 28703 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28703) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28703 : oddCount 28703 15 = 9 ∧ acceleratedOrbit 15 28703 = 17242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28703) = 3 ^ 9 * m + 17242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28703.1, data_15_28703.2]

end Collatz.Research.PassageAtlas.Batch0876
