import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0693

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22675. -/
theorem bounds_15_22675 : exactInterval 15 22675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22675 : oddCount 22675 15 = 8 ∧ acceleratedOrbit 15 22675 = 4541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22675) = 3 ^ 8 * m + 4541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22675.1, data_15_22675.2]

/-- Complete interval computation for depth 15, residue 22676. -/
theorem bounds_15_22676 : exactInterval 15 22676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22676 : oddCount 22676 15 = 6 ∧ acceleratedOrbit 15 22676 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22676) = 3 ^ 6 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22676.1, data_15_22676.2]

/-- Complete interval computation for depth 15, residue 22677. -/
theorem bounds_15_22677 : exactInterval 15 22677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22677 : oddCount 22677 15 = 6 ∧ acceleratedOrbit 15 22677 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22677) = 3 ^ 6 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22677.1, data_15_22677.2]

/-- Complete interval computation for depth 15, residue 22678. -/
theorem bounds_15_22678 : exactInterval 15 22678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22678 : oddCount 22678 15 = 6 ∧ acceleratedOrbit 15 22678 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22678) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22678.1, data_15_22678.2]

/-- Complete interval computation for depth 15, residue 22679. -/
theorem bounds_15_22679 : exactInterval 15 22679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22679 : oddCount 22679 15 = 6 ∧ acceleratedOrbit 15 22679 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22679) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22679.1, data_15_22679.2]

/-- Complete interval computation for depth 15, residue 22680. -/
theorem bounds_15_22680 : exactInterval 15 22680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22680 : oddCount 22680 15 = 6 ∧ acceleratedOrbit 15 22680 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22680) = 3 ^ 6 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22680.1, data_15_22680.2]

/-- Complete interval computation for depth 15, residue 22681. -/
theorem bounds_15_22681 : exactInterval 15 22681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22681 : oddCount 22681 15 = 9 ∧ acceleratedOrbit 15 22681 = 13628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22681) = 3 ^ 9 * m + 13628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22681.1, data_15_22681.2]

/-- Complete interval computation for depth 15, residue 22682. -/
theorem bounds_15_22682 : exactInterval 15 22682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22682 : oddCount 22682 15 = 6 ∧ acceleratedOrbit 15 22682 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22682) = 3 ^ 6 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22682.1, data_15_22682.2]

/-- Complete interval computation for depth 15, residue 22683. -/
theorem bounds_15_22683 : exactInterval 15 22683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22683 : oddCount 22683 15 = 7 ∧ acceleratedOrbit 15 22683 = 1514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22683) = 3 ^ 7 * m + 1514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22683.1, data_15_22683.2]

/-- Complete interval computation for depth 15, residue 22684. -/
theorem bounds_15_22684 : exactInterval 15 22684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22684 : oddCount 22684 15 = 6 ∧ acceleratedOrbit 15 22684 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22684) = 3 ^ 6 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22684.1, data_15_22684.2]

/-- Complete interval computation for depth 15, residue 22685. -/
theorem bounds_15_22685 : exactInterval 15 22685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22685 : oddCount 22685 15 = 6 ∧ acceleratedOrbit 15 22685 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22685) = 3 ^ 6 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22685.1, data_15_22685.2]

/-- Complete interval computation for depth 15, residue 22686. -/
theorem bounds_15_22686 : exactInterval 15 22686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22686 : oddCount 22686 15 = 6 ∧ acceleratedOrbit 15 22686 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22686) = 3 ^ 6 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22686.1, data_15_22686.2]

/-- Complete interval computation for depth 15, residue 22687. -/
theorem bounds_15_22687 : exactInterval 15 22687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22687 : oddCount 22687 15 = 13 ∧ acceleratedOrbit 15 22687 = 1103888 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22687) = 3 ^ 13 * m + 1103888 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22687.1, data_15_22687.2]

/-- Complete interval computation for depth 15, residue 22688. -/
theorem bounds_15_22688 : exactInterval 15 22688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22688 : oddCount 22688 15 = 3 ∧ acceleratedOrbit 15 22688 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22688) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22688.1, data_15_22688.2]

/-- Complete interval computation for depth 15, residue 22689. -/
theorem bounds_15_22689 : exactInterval 15 22689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22689 : oddCount 22689 15 = 8 ∧ acceleratedOrbit 15 22689 = 4544 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22689) = 3 ^ 8 * m + 4544 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22689.1, data_15_22689.2]

/-- Complete interval computation for depth 15, residue 22690. -/
theorem bounds_15_22690 : exactInterval 15 22690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22690 : oddCount 22690 15 = 6 ∧ acceleratedOrbit 15 22690 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22690) = 3 ^ 6 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22690.1, data_15_22690.2]

/-- Complete interval computation for depth 15, residue 22691. -/
theorem bounds_15_22691 : exactInterval 15 22691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22691 : oddCount 22691 15 = 6 ∧ acceleratedOrbit 15 22691 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22691) = 3 ^ 6 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22691.1, data_15_22691.2]

/-- Complete interval computation for depth 15, residue 22692. -/
theorem bounds_15_22692 : exactInterval 15 22692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22692 : oddCount 22692 15 = 11 ∧ acceleratedOrbit 15 22692 = 122714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22692) = 3 ^ 11 * m + 122714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22692.1, data_15_22692.2]

/-- Complete interval computation for depth 15, residue 22693. -/
theorem bounds_15_22693 : exactInterval 15 22693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22693 : oddCount 22693 15 = 11 ∧ acceleratedOrbit 15 22693 = 122714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22693) = 3 ^ 11 * m + 122714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22693.1, data_15_22693.2]

/-- Complete interval computation for depth 15, residue 22694. -/
theorem bounds_15_22694 : exactInterval 15 22694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22694 : oddCount 22694 15 = 11 ∧ acceleratedOrbit 15 22694 = 122714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22694) = 3 ^ 11 * m + 122714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22694.1, data_15_22694.2]

/-- Complete interval computation for depth 15, residue 22695. -/
theorem bounds_15_22695 : exactInterval 15 22695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22695 : oddCount 22695 15 = 10 ∧ acceleratedOrbit 15 22695 = 40900 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22695) = 3 ^ 10 * m + 40900 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22695.1, data_15_22695.2]

/-- Complete interval computation for depth 15, residue 22696. -/
theorem bounds_15_22696 : exactInterval 15 22696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22696 : oddCount 22696 15 = 3 ∧ acceleratedOrbit 15 22696 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22696) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22696.1, data_15_22696.2]

/-- Complete interval computation for depth 15, residue 22697. -/
theorem bounds_15_22697 : exactInterval 15 22697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22697 : oddCount 22697 15 = 12 ∧ acceleratedOrbit 15 22697 = 368135 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22697) = 3 ^ 12 * m + 368135 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22697.1, data_15_22697.2]

/-- Complete interval computation for depth 15, residue 22698. -/
theorem bounds_15_22698 : exactInterval 15 22698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22698 : oddCount 22698 15 = 3 ∧ acceleratedOrbit 15 22698 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22698) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22698.1, data_15_22698.2]

/-- Complete interval computation for depth 15, residue 22699. -/
theorem bounds_15_22699 : exactInterval 15 22699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22699 : oddCount 22699 15 = 8 ∧ acceleratedOrbit 15 22699 = 4546 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22699) = 3 ^ 8 * m + 4546 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22699.1, data_15_22699.2]

/-- Complete interval computation for depth 15, residue 22700. -/
theorem bounds_15_22700 : exactInterval 15 22700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22700 : oddCount 22700 15 = 6 ∧ acceleratedOrbit 15 22700 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22700) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22700.1, data_15_22700.2]

/-- Complete interval computation for depth 15, residue 22701. -/
theorem bounds_15_22701 : exactInterval 15 22701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22701 : oddCount 22701 15 = 6 ∧ acceleratedOrbit 15 22701 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22701) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22701.1, data_15_22701.2]

/-- Complete interval computation for depth 15, residue 22702. -/
theorem bounds_15_22702 : exactInterval 15 22702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22702 : oddCount 22702 15 = 6 ∧ acceleratedOrbit 15 22702 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22702) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22702.1, data_15_22702.2]

/-- Complete interval computation for depth 15, residue 22703. -/
theorem bounds_15_22703 : exactInterval 15 22703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22703 : oddCount 22703 15 = 10 ∧ acceleratedOrbit 15 22703 = 40915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22703) = 3 ^ 10 * m + 40915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22703.1, data_15_22703.2]

/-- Complete interval computation for depth 15, residue 22704. -/
theorem bounds_15_22704 : exactInterval 15 22704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22704 : oddCount 22704 15 = 6 ∧ acceleratedOrbit 15 22704 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22704) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22704.1, data_15_22704.2]

/-- Complete interval computation for depth 15, residue 22705. -/
theorem bounds_15_22705 : exactInterval 15 22705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22705 : oddCount 22705 15 = 8 ∧ acceleratedOrbit 15 22705 = 4549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22705) = 3 ^ 8 * m + 4549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22705.1, data_15_22705.2]

/-- Complete interval computation for depth 15, residue 22706. -/
theorem bounds_15_22706 : exactInterval 15 22706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22706 : oddCount 22706 15 = 8 ∧ acceleratedOrbit 15 22706 = 4549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22706) = 3 ^ 8 * m + 4549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22706.1, data_15_22706.2]

/-- Complete interval computation for depth 15, residue 22707. -/
theorem bounds_15_22707 : exactInterval 15 22707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22707 : oddCount 22707 15 = 8 ∧ acceleratedOrbit 15 22707 = 4549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22707) = 3 ^ 8 * m + 4549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22707.1, data_15_22707.2]

end Collatz.Research.PassageAtlas.Batch0693
