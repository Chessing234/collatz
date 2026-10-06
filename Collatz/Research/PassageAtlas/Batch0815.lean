import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0815

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26673. -/
theorem bounds_15_26673 : exactInterval 15 26673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26673 : oddCount 26673 15 = 9 ∧ acceleratedOrbit 15 26673 = 16028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26673) = 3 ^ 9 * m + 16028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26673.1, data_15_26673.2]

/-- Complete interval computation for depth 15, residue 26674. -/
theorem bounds_15_26674 : exactInterval 15 26674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26674 : oddCount 26674 15 = 9 ∧ acceleratedOrbit 15 26674 = 16028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26674) = 3 ^ 9 * m + 16028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26674.1, data_15_26674.2]

/-- Complete interval computation for depth 15, residue 26675. -/
theorem bounds_15_26675 : exactInterval 15 26675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26675 : oddCount 26675 15 = 9 ∧ acceleratedOrbit 15 26675 = 16028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26675) = 3 ^ 9 * m + 16028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26675.1, data_15_26675.2]

/-- Complete interval computation for depth 15, residue 26676. -/
theorem bounds_15_26676 : exactInterval 15 26676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26676 : oddCount 26676 15 = 3 ∧ acceleratedOrbit 15 26676 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26676) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26676.1, data_15_26676.2]

/-- Complete interval computation for depth 15, residue 26677. -/
theorem bounds_15_26677 : exactInterval 15 26677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26677 : oddCount 26677 15 = 3 ∧ acceleratedOrbit 15 26677 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26677) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26677.1, data_15_26677.2]

/-- Complete interval computation for depth 15, residue 26678. -/
theorem bounds_15_26678 : exactInterval 15 26678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26678 : oddCount 26678 15 = 10 ∧ acceleratedOrbit 15 26678 = 48080 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26678) = 3 ^ 10 * m + 48080 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26678.1, data_15_26678.2]

/-- Complete interval computation for depth 15, residue 26679. -/
theorem bounds_15_26679 : exactInterval 15 26679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26679 : oddCount 26679 15 = 10 ∧ acceleratedOrbit 15 26679 = 48080 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26679) = 3 ^ 10 * m + 48080 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26679.1, data_15_26679.2]

/-- Complete interval computation for depth 15, residue 26680. -/
theorem bounds_15_26680 : exactInterval 15 26680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26680 : oddCount 26680 15 = 9 ∧ acceleratedOrbit 15 26680 = 16037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26680) = 3 ^ 9 * m + 16037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26680.1, data_15_26680.2]

/-- Complete interval computation for depth 15, residue 26681. -/
theorem bounds_15_26681 : exactInterval 15 26681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26681 : oddCount 26681 15 = 8 ∧ acceleratedOrbit 15 26681 = 5345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26681) = 3 ^ 8 * m + 5345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26681.1, data_15_26681.2]

/-- Complete interval computation for depth 15, residue 26682. -/
theorem bounds_15_26682 : exactInterval 15 26682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26682 : oddCount 26682 15 = 9 ∧ acceleratedOrbit 15 26682 = 16037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26682) = 3 ^ 9 * m + 16037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26682.1, data_15_26682.2]

/-- Complete interval computation for depth 15, residue 26683. -/
theorem bounds_15_26683 : exactInterval 15 26683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26683 : oddCount 26683 15 = 9 ∧ acceleratedOrbit 15 26683 = 16031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26683) = 3 ^ 9 * m + 16031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26683.1, data_15_26683.2]

/-- Complete interval computation for depth 15, residue 26684. -/
theorem bounds_15_26684 : exactInterval 15 26684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26684 : oddCount 26684 15 = 9 ∧ acceleratedOrbit 15 26684 = 16037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26684) = 3 ^ 9 * m + 16037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26684.1, data_15_26684.2]

/-- Complete interval computation for depth 15, residue 26685. -/
theorem bounds_15_26685 : exactInterval 15 26685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26685 : oddCount 26685 15 = 9 ∧ acceleratedOrbit 15 26685 = 16037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26685) = 3 ^ 9 * m + 16037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26685.1, data_15_26685.2]

/-- Complete interval computation for depth 15, residue 26686. -/
theorem bounds_15_26686 : exactInterval 15 26686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26686 : oddCount 26686 15 = 11 ∧ acceleratedOrbit 15 26686 = 144281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26686) = 3 ^ 11 * m + 144281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26686.1, data_15_26686.2]

/-- Complete interval computation for depth 15, residue 26687. -/
theorem bounds_15_26687 : exactInterval 15 26687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26687 : oddCount 26687 15 = 11 ∧ acceleratedOrbit 15 26687 = 144281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26687) = 3 ^ 11 * m + 144281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26687.1, data_15_26687.2]

/-- Complete interval computation for depth 15, residue 26688. -/
theorem bounds_15_26688 : exactInterval 15 26688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26688 : oddCount 26688 15 = 5 ∧ acceleratedOrbit 15 26688 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26688) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26688.1, data_15_26688.2]

/-- Complete interval computation for depth 15, residue 26689. -/
theorem bounds_15_26689 : exactInterval 15 26689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26689 : oddCount 26689 15 = 10 ∧ acceleratedOrbit 15 26689 = 48113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26689) = 3 ^ 10 * m + 48113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26689.1, data_15_26689.2]

/-- Complete interval computation for depth 15, residue 26690. -/
theorem bounds_15_26690 : exactInterval 15 26690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26690 : oddCount 26690 15 = 10 ∧ acceleratedOrbit 15 26690 = 48113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26690) = 3 ^ 10 * m + 48113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26690.1, data_15_26690.2]

/-- Complete interval computation for depth 15, residue 26691. -/
theorem bounds_15_26691 : exactInterval 15 26691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26691 : oddCount 26691 15 = 10 ∧ acceleratedOrbit 15 26691 = 48113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26691) = 3 ^ 10 * m + 48113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26691.1, data_15_26691.2]

/-- Complete interval computation for depth 15, residue 26692. -/
theorem bounds_15_26692 : exactInterval 15 26692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26692 : oddCount 26692 15 = 3 ∧ acceleratedOrbit 15 26692 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26692) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26692.1, data_15_26692.2]

/-- Complete interval computation for depth 15, residue 26693. -/
theorem bounds_15_26693 : exactInterval 15 26693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26693 : oddCount 26693 15 = 3 ∧ acceleratedOrbit 15 26693 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26693) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26693.1, data_15_26693.2]

/-- Complete interval computation for depth 15, residue 26694. -/
theorem bounds_15_26694 : exactInterval 15 26694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26694 : oddCount 26694 15 = 3 ∧ acceleratedOrbit 15 26694 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26694) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26694.1, data_15_26694.2]

/-- Complete interval computation for depth 15, residue 26695. -/
theorem bounds_15_26695 : exactInterval 15 26695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26695 : oddCount 26695 15 = 10 ∧ acceleratedOrbit 15 26695 = 48109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26695) = 3 ^ 10 * m + 48109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26695.1, data_15_26695.2]

/-- Complete interval computation for depth 15, residue 26696. -/
theorem bounds_15_26696 : exactInterval 15 26696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26696 : oddCount 26696 15 = 7 ∧ acceleratedOrbit 15 26696 = 1783 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26696) = 3 ^ 7 * m + 1783 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26696.1, data_15_26696.2]

/-- Complete interval computation for depth 15, residue 26697. -/
theorem bounds_15_26697 : exactInterval 15 26697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26697 : oddCount 26697 15 = 12 ∧ acceleratedOrbit 15 26697 = 433025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26697) = 3 ^ 12 * m + 433025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26697.1, data_15_26697.2]

/-- Complete interval computation for depth 15, residue 26698. -/
theorem bounds_15_26698 : exactInterval 15 26698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26698 : oddCount 26698 15 = 7 ∧ acceleratedOrbit 15 26698 = 1783 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26698) = 3 ^ 7 * m + 1783 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26698.1, data_15_26698.2]

/-- Complete interval computation for depth 15, residue 26699. -/
theorem bounds_15_26699 : exactInterval 15 26699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26699 : oddCount 26699 15 = 3 ∧ acceleratedOrbit 15 26699 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26699) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26699.1, data_15_26699.2]

/-- Complete interval computation for depth 15, residue 26700. -/
theorem bounds_15_26700 : exactInterval 15 26700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26700 : oddCount 26700 15 = 7 ∧ acceleratedOrbit 15 26700 = 1783 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26700) = 3 ^ 7 * m + 1783 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26700.1, data_15_26700.2]

/-- Complete interval computation for depth 15, residue 26701. -/
theorem bounds_15_26701 : exactInterval 15 26701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26701 : oddCount 26701 15 = 7 ∧ acceleratedOrbit 15 26701 = 1783 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26701) = 3 ^ 7 * m + 1783 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26701.1, data_15_26701.2]

/-- Complete interval computation for depth 15, residue 26702. -/
theorem bounds_15_26702 : exactInterval 15 26702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26702 : oddCount 26702 15 = 8 ∧ acceleratedOrbit 15 26702 = 5348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26702) = 3 ^ 8 * m + 5348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26702.1, data_15_26702.2]

/-- Complete interval computation for depth 15, residue 26703. -/
theorem bounds_15_26703 : exactInterval 15 26703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26703 : oddCount 26703 15 = 8 ∧ acceleratedOrbit 15 26703 = 5348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26703) = 3 ^ 8 * m + 5348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26703.1, data_15_26703.2]

/-- Complete interval computation for depth 15, residue 26704. -/
theorem bounds_15_26704 : exactInterval 15 26704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26704 : oddCount 26704 15 = 5 ∧ acceleratedOrbit 15 26704 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26704) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26704.1, data_15_26704.2]

end Collatz.Research.PassageAtlas.Batch0815
