import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0541

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17694. -/
theorem bounds_15_17694 : exactInterval 15 17694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17694 : oddCount 17694 15 = 9 ∧ acceleratedOrbit 15 17694 = 10631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17694) = 3 ^ 9 * m + 10631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17694.1, data_15_17694.2]

/-- Complete interval computation for depth 15, residue 17695. -/
theorem bounds_15_17695 : exactInterval 15 17695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17695 : oddCount 17695 15 = 9 ∧ acceleratedOrbit 15 17695 = 10631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17695) = 3 ^ 9 * m + 10631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17695.1, data_15_17695.2]

/-- Complete interval computation for depth 15, residue 17696. -/
theorem bounds_15_17696 : exactInterval 15 17696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17696 : oddCount 17696 15 = 8 ∧ acceleratedOrbit 15 17696 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17696) = 3 ^ 8 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17696.1, data_15_17696.2]

/-- Complete interval computation for depth 15, residue 17697. -/
theorem bounds_15_17697 : exactInterval 15 17697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17697 : oddCount 17697 15 = 6 ∧ acceleratedOrbit 15 17697 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17697) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17697.1, data_15_17697.2]

/-- Complete interval computation for depth 15, residue 17698. -/
theorem bounds_15_17698 : exactInterval 15 17698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17698 : oddCount 17698 15 = 6 ∧ acceleratedOrbit 15 17698 = 394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17698) = 3 ^ 6 * m + 394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17698.1, data_15_17698.2]

/-- Complete interval computation for depth 15, residue 17699. -/
theorem bounds_15_17699 : exactInterval 15 17699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17699 : oddCount 17699 15 = 6 ∧ acceleratedOrbit 15 17699 = 394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17699) = 3 ^ 6 * m + 394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17699.1, data_15_17699.2]

/-- Complete interval computation for depth 15, residue 17700. -/
theorem bounds_15_17700 : exactInterval 15 17700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17700 : oddCount 17700 15 = 6 ∧ acceleratedOrbit 15 17700 = 394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17700) = 3 ^ 6 * m + 394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17700.1, data_15_17700.2]

/-- Complete interval computation for depth 15, residue 17701. -/
theorem bounds_15_17701 : exactInterval 15 17701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17701 : oddCount 17701 15 = 6 ∧ acceleratedOrbit 15 17701 = 394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17701) = 3 ^ 6 * m + 394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17701.1, data_15_17701.2]

/-- Complete interval computation for depth 15, residue 17702. -/
theorem bounds_15_17702 : exactInterval 15 17702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17702 : oddCount 17702 15 = 6 ∧ acceleratedOrbit 15 17702 = 394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17702) = 3 ^ 6 * m + 394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17702.1, data_15_17702.2]

/-- Complete interval computation for depth 15, residue 17703. -/
theorem bounds_15_17703 : exactInterval 15 17703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17703 : oddCount 17703 15 = 9 ∧ acceleratedOrbit 15 17703 = 10637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17703) = 3 ^ 9 * m + 10637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17703.1, data_15_17703.2]

/-- Complete interval computation for depth 15, residue 17704. -/
theorem bounds_15_17704 : exactInterval 15 17704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17704 : oddCount 17704 15 = 8 ∧ acceleratedOrbit 15 17704 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17704) = 3 ^ 8 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17704.1, data_15_17704.2]

/-- Complete interval computation for depth 15, residue 17705. -/
theorem bounds_15_17705 : exactInterval 15 17705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17705 : oddCount 17705 15 = 10 ∧ acceleratedOrbit 15 17705 = 31909 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17705) = 3 ^ 10 * m + 31909 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17705.1, data_15_17705.2]

/-- Complete interval computation for depth 15, residue 17706. -/
theorem bounds_15_17706 : exactInterval 15 17706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17706 : oddCount 17706 15 = 8 ∧ acceleratedOrbit 15 17706 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17706) = 3 ^ 8 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17706.1, data_15_17706.2]

/-- Complete interval computation for depth 15, residue 17707. -/
theorem bounds_15_17707 : exactInterval 15 17707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17707 : oddCount 17707 15 = 6 ∧ acceleratedOrbit 15 17707 = 394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17707) = 3 ^ 6 * m + 394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17707.1, data_15_17707.2]

/-- Complete interval computation for depth 15, residue 17708. -/
theorem bounds_15_17708 : exactInterval 15 17708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17708 : oddCount 17708 15 = 6 ∧ acceleratedOrbit 15 17708 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17708) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17708.1, data_15_17708.2]

/-- Complete interval computation for depth 15, residue 17709. -/
theorem bounds_15_17709 : exactInterval 15 17709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17709 : oddCount 17709 15 = 6 ∧ acceleratedOrbit 15 17709 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17709) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17709.1, data_15_17709.2]

/-- Complete interval computation for depth 15, residue 17710. -/
theorem bounds_15_17710 : exactInterval 15 17710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17710 : oddCount 17710 15 = 6 ∧ acceleratedOrbit 15 17710 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17710) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17710.1, data_15_17710.2]

/-- Complete interval computation for depth 15, residue 17711. -/
theorem bounds_15_17711 : exactInterval 15 17711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17711 : oddCount 17711 15 = 9 ∧ acceleratedOrbit 15 17711 = 10640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17711) = 3 ^ 9 * m + 10640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17711.1, data_15_17711.2]

/-- Complete interval computation for depth 15, residue 17712. -/
theorem bounds_15_17712 : exactInterval 15 17712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17712 : oddCount 17712 15 = 8 ∧ acceleratedOrbit 15 17712 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17712) = 3 ^ 8 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17712.1, data_15_17712.2]

/-- Complete interval computation for depth 15, residue 17713. -/
theorem bounds_15_17713 : exactInterval 15 17713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17713 : oddCount 17713 15 = 7 ∧ acceleratedOrbit 15 17713 = 1183 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17713) = 3 ^ 7 * m + 1183 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17713.1, data_15_17713.2]

/-- Complete interval computation for depth 15, residue 17714. -/
theorem bounds_15_17714 : exactInterval 15 17714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17714 : oddCount 17714 15 = 7 ∧ acceleratedOrbit 15 17714 = 1183 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17714) = 3 ^ 7 * m + 1183 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17714.1, data_15_17714.2]

/-- Complete interval computation for depth 15, residue 17715. -/
theorem bounds_15_17715 : exactInterval 15 17715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17715 : oddCount 17715 15 = 7 ∧ acceleratedOrbit 15 17715 = 1183 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17715) = 3 ^ 7 * m + 1183 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17715.1, data_15_17715.2]

/-- Complete interval computation for depth 15, residue 17716. -/
theorem bounds_15_17716 : exactInterval 15 17716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17716 : oddCount 17716 15 = 8 ∧ acceleratedOrbit 15 17716 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17716) = 3 ^ 8 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17716.1, data_15_17716.2]

/-- Complete interval computation for depth 15, residue 17717. -/
theorem bounds_15_17717 : exactInterval 15 17717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17717 : oddCount 17717 15 = 8 ∧ acceleratedOrbit 15 17717 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17717) = 3 ^ 8 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17717.1, data_15_17717.2]

/-- Complete interval computation for depth 15, residue 17718. -/
theorem bounds_15_17718 : exactInterval 15 17718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17718 : oddCount 17718 15 = 10 ∧ acceleratedOrbit 15 17718 = 31934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17718) = 3 ^ 10 * m + 31934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17718.1, data_15_17718.2]

/-- Complete interval computation for depth 15, residue 17719. -/
theorem bounds_15_17719 : exactInterval 15 17719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17719 : oddCount 17719 15 = 10 ∧ acceleratedOrbit 15 17719 = 31934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17719) = 3 ^ 10 * m + 31934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17719.1, data_15_17719.2]

/-- Complete interval computation for depth 15, residue 17720. -/
theorem bounds_15_17720 : exactInterval 15 17720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17720 : oddCount 17720 15 = 9 ∧ acceleratedOrbit 15 17720 = 10651 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17720) = 3 ^ 9 * m + 10651 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17720.1, data_15_17720.2]

/-- Complete interval computation for depth 15, residue 17721. -/
theorem bounds_15_17721 : exactInterval 15 17721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17721 : oddCount 17721 15 = 10 ∧ acceleratedOrbit 15 17721 = 31940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17721) = 3 ^ 10 * m + 31940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17721.1, data_15_17721.2]

/-- Complete interval computation for depth 15, residue 17722. -/
theorem bounds_15_17722 : exactInterval 15 17722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17722 : oddCount 17722 15 = 9 ∧ acceleratedOrbit 15 17722 = 10651 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17722) = 3 ^ 9 * m + 10651 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17722.1, data_15_17722.2]

/-- Complete interval computation for depth 15, residue 17723. -/
theorem bounds_15_17723 : exactInterval 15 17723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17723 : oddCount 17723 15 = 6 ∧ acceleratedOrbit 15 17723 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17723) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17723.1, data_15_17723.2]

/-- Complete interval computation for depth 15, residue 17724. -/
theorem bounds_15_17724 : exactInterval 15 17724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17724 : oddCount 17724 15 = 9 ∧ acceleratedOrbit 15 17724 = 10651 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17724) = 3 ^ 9 * m + 10651 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17724.1, data_15_17724.2]

/-- Complete interval computation for depth 15, residue 17725. -/
theorem bounds_15_17725 : exactInterval 15 17725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17725 : oddCount 17725 15 = 9 ∧ acceleratedOrbit 15 17725 = 10651 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17725) = 3 ^ 9 * m + 10651 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17725.1, data_15_17725.2]

/-- Complete interval computation for depth 15, residue 17726. -/
theorem bounds_15_17726 : exactInterval 15 17726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17726 : oddCount 17726 15 = 9 ∧ acceleratedOrbit 15 17726 = 10649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17726) = 3 ^ 9 * m + 10649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17726.1, data_15_17726.2]

end Collatz.Research.PassageAtlas.Batch0541
