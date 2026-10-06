import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0483

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15794. -/
theorem bounds_15_15794 : exactInterval 15 15794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15794 : oddCount 15794 15 = 6 ∧ acceleratedOrbit 15 15794 = 352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15794) = 3 ^ 6 * m + 352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15794.1, data_15_15794.2]

/-- Complete interval computation for depth 15, residue 15795. -/
theorem bounds_15_15795 : exactInterval 15 15795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15795 : oddCount 15795 15 = 6 ∧ acceleratedOrbit 15 15795 = 352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15795) = 3 ^ 6 * m + 352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15795.1, data_15_15795.2]

/-- Complete interval computation for depth 15, residue 15796. -/
theorem bounds_15_15796 : exactInterval 15 15796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15796 : oddCount 15796 15 = 6 ∧ acceleratedOrbit 15 15796 = 352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15796) = 3 ^ 6 * m + 352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15796.1, data_15_15796.2]

/-- Complete interval computation for depth 15, residue 15797. -/
theorem bounds_15_15797 : exactInterval 15 15797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15797 : oddCount 15797 15 = 6 ∧ acceleratedOrbit 15 15797 = 352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15797) = 3 ^ 6 * m + 352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15797.1, data_15_15797.2]

/-- Complete interval computation for depth 15, residue 15798. -/
theorem bounds_15_15798 : exactInterval 15 15798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15798 : oddCount 15798 15 = 8 ∧ acceleratedOrbit 15 15798 = 3164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15798) = 3 ^ 8 * m + 3164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15798.1, data_15_15798.2]

/-- Complete interval computation for depth 15, residue 15799. -/
theorem bounds_15_15799 : exactInterval 15 15799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15799 : oddCount 15799 15 = 8 ∧ acceleratedOrbit 15 15799 = 3164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15799) = 3 ^ 8 * m + 3164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15799.1, data_15_15799.2]

/-- Complete interval computation for depth 15, residue 15800. -/
theorem bounds_15_15800 : exactInterval 15 15800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15800 : oddCount 15800 15 = 6 ∧ acceleratedOrbit 15 15800 = 352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15800) = 3 ^ 6 * m + 352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15800.1, data_15_15800.2]

/-- Complete interval computation for depth 15, residue 15801. -/
theorem bounds_15_15801 : exactInterval 15 15801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15801 : oddCount 15801 15 = 6 ∧ acceleratedOrbit 15 15801 = 352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15801) = 3 ^ 6 * m + 352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15801.1, data_15_15801.2]

/-- Complete interval computation for depth 15, residue 15802. -/
theorem bounds_15_15802 : exactInterval 15 15802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15802 : oddCount 15802 15 = 6 ∧ acceleratedOrbit 15 15802 = 352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15802) = 3 ^ 6 * m + 352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15802.1, data_15_15802.2]

/-- Complete interval computation for depth 15, residue 15803. -/
theorem bounds_15_15803 : exactInterval 15 15803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15803 : oddCount 15803 15 = 7 ∧ acceleratedOrbit 15 15803 = 1055 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15803) = 3 ^ 7 * m + 1055 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15803.1, data_15_15803.2]

/-- Complete interval computation for depth 15, residue 15804. -/
theorem bounds_15_15804 : exactInterval 15 15804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15804 : oddCount 15804 15 = 9 ∧ acceleratedOrbit 15 15804 = 9497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15804) = 3 ^ 9 * m + 9497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15804.1, data_15_15804.2]

/-- Complete interval computation for depth 15, residue 15805. -/
theorem bounds_15_15805 : exactInterval 15 15805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15805 : oddCount 15805 15 = 9 ∧ acceleratedOrbit 15 15805 = 9497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15805) = 3 ^ 9 * m + 9497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15805.1, data_15_15805.2]

/-- Complete interval computation for depth 15, residue 15806. -/
theorem bounds_15_15806 : exactInterval 15 15806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15806 : oddCount 15806 15 = 9 ∧ acceleratedOrbit 15 15806 = 9497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15806) = 3 ^ 9 * m + 9497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15806.1, data_15_15806.2]

/-- Complete interval computation for depth 15, residue 15807. -/
theorem bounds_15_15807 : exactInterval 15 15807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15807 : oddCount 15807 15 = 11 ∧ acceleratedOrbit 15 15807 = 85460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15807) = 3 ^ 11 * m + 85460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15807.1, data_15_15807.2]

/-- Complete interval computation for depth 15, residue 15808. -/
theorem bounds_15_15808 : exactInterval 15 15808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15808 : oddCount 15808 15 = 5 ∧ acceleratedOrbit 15 15808 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15808) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15808.1, data_15_15808.2]

/-- Complete interval computation for depth 15, residue 15809. -/
theorem bounds_15_15809 : exactInterval 15 15809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15809 : oddCount 15809 15 = 8 ∧ acceleratedOrbit 15 15809 = 3167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15809) = 3 ^ 8 * m + 3167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15809.1, data_15_15809.2]

/-- Complete interval computation for depth 15, residue 15810. -/
theorem bounds_15_15810 : exactInterval 15 15810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15810 : oddCount 15810 15 = 8 ∧ acceleratedOrbit 15 15810 = 3167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15810) = 3 ^ 8 * m + 3167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15810.1, data_15_15810.2]

/-- Complete interval computation for depth 15, residue 15811. -/
theorem bounds_15_15811 : exactInterval 15 15811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15811 : oddCount 15811 15 = 8 ∧ acceleratedOrbit 15 15811 = 3167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15811) = 3 ^ 8 * m + 3167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15811.1, data_15_15811.2]

/-- Complete interval computation for depth 15, residue 15812. -/
theorem bounds_15_15812 : exactInterval 15 15812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15812 : oddCount 15812 15 = 5 ∧ acceleratedOrbit 15 15812 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15812) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15812.1, data_15_15812.2]

/-- Complete interval computation for depth 15, residue 15813. -/
theorem bounds_15_15813 : exactInterval 15 15813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15813 : oddCount 15813 15 = 5 ∧ acceleratedOrbit 15 15813 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15813) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15813.1, data_15_15813.2]

/-- Complete interval computation for depth 15, residue 15814. -/
theorem bounds_15_15814 : exactInterval 15 15814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15814 : oddCount 15814 15 = 5 ∧ acceleratedOrbit 15 15814 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15814) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15814.1, data_15_15814.2]

/-- Complete interval computation for depth 15, residue 15815. -/
theorem bounds_15_15815 : exactInterval 15 15815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15815 : oddCount 15815 15 = 9 ∧ acceleratedOrbit 15 15815 = 9503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15815) = 3 ^ 9 * m + 9503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15815.1, data_15_15815.2]

/-- Complete interval computation for depth 15, residue 15816. -/
theorem bounds_15_15816 : exactInterval 15 15816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15816 : oddCount 15816 15 = 6 ∧ acceleratedOrbit 15 15816 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15816) = 3 ^ 6 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15816.1, data_15_15816.2]

/-- Complete interval computation for depth 15, residue 15817. -/
theorem bounds_15_15817 : exactInterval 15 15817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15817 : oddCount 15817 15 = 6 ∧ acceleratedOrbit 15 15817 = 352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15817) = 3 ^ 6 * m + 352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15817.1, data_15_15817.2]

/-- Complete interval computation for depth 15, residue 15818. -/
theorem bounds_15_15818 : exactInterval 15 15818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15818 : oddCount 15818 15 = 6 ∧ acceleratedOrbit 15 15818 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15818) = 3 ^ 6 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15818.1, data_15_15818.2]

/-- Complete interval computation for depth 15, residue 15819. -/
theorem bounds_15_15819 : exactInterval 15 15819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15819 : oddCount 15819 15 = 8 ∧ acceleratedOrbit 15 15819 = 3169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15819) = 3 ^ 8 * m + 3169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15819.1, data_15_15819.2]

/-- Complete interval computation for depth 15, residue 15820. -/
theorem bounds_15_15820 : exactInterval 15 15820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15820 : oddCount 15820 15 = 6 ∧ acceleratedOrbit 15 15820 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15820) = 3 ^ 6 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15820.1, data_15_15820.2]

/-- Complete interval computation for depth 15, residue 15821. -/
theorem bounds_15_15821 : exactInterval 15 15821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15821 : oddCount 15821 15 = 6 ∧ acceleratedOrbit 15 15821 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15821) = 3 ^ 6 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15821.1, data_15_15821.2]

/-- Complete interval computation for depth 15, residue 15822. -/
theorem bounds_15_15822 : exactInterval 15 15822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15822 : oddCount 15822 15 = 9 ∧ acceleratedOrbit 15 15822 = 9506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15822) = 3 ^ 9 * m + 9506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15822.1, data_15_15822.2]

/-- Complete interval computation for depth 15, residue 15823. -/
theorem bounds_15_15823 : exactInterval 15 15823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15823 : oddCount 15823 15 = 9 ∧ acceleratedOrbit 15 15823 = 9506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15823) = 3 ^ 9 * m + 9506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15823.1, data_15_15823.2]

/-- Complete interval computation for depth 15, residue 15824. -/
theorem bounds_15_15824 : exactInterval 15 15824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15824 : oddCount 15824 15 = 5 ∧ acceleratedOrbit 15 15824 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15824) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15824.1, data_15_15824.2]

/-- Complete interval computation for depth 15, residue 15825. -/
theorem bounds_15_15825 : exactInterval 15 15825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15825 : oddCount 15825 15 = 6 ∧ acceleratedOrbit 15 15825 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15825) = 3 ^ 6 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15825.1, data_15_15825.2]

end Collatz.Research.PassageAtlas.Batch0483
