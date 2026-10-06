import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0086

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2785. -/
theorem bounds_15_2785 : exactInterval 15 2785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2785 : oddCount 2785 15 = 10 ∧ acceleratedOrbit 15 2785 = 5024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2785) = 3 ^ 10 * m + 5024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2785.1, data_15_2785.2]

/-- Complete interval computation for depth 15, residue 2786. -/
theorem bounds_15_2786 : exactInterval 15 2786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2786 : oddCount 2786 15 = 4 ∧ acceleratedOrbit 15 2786 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2786) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2786.1, data_15_2786.2]

/-- Complete interval computation for depth 15, residue 2787. -/
theorem bounds_15_2787 : exactInterval 15 2787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2787 : oddCount 2787 15 = 4 ∧ acceleratedOrbit 15 2787 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2787) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2787.1, data_15_2787.2]

/-- Complete interval computation for depth 15, residue 2788. -/
theorem bounds_15_2788 : exactInterval 15 2788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2788 : oddCount 2788 15 = 7 ∧ acceleratedOrbit 15 2788 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2788) = 3 ^ 7 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2788.1, data_15_2788.2]

/-- Complete interval computation for depth 15, residue 2789. -/
theorem bounds_15_2789 : exactInterval 15 2789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2789 : oddCount 2789 15 = 7 ∧ acceleratedOrbit 15 2789 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2789) = 3 ^ 7 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2789.1, data_15_2789.2]

/-- Complete interval computation for depth 15, residue 2790. -/
theorem bounds_15_2790 : exactInterval 15 2790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2790 : oddCount 2790 15 = 7 ∧ acceleratedOrbit 15 2790 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2790) = 3 ^ 7 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2790.1, data_15_2790.2]

/-- Complete interval computation for depth 15, residue 2791. -/
theorem bounds_15_2791 : exactInterval 15 2791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2791 : oddCount 2791 15 = 10 ∧ acceleratedOrbit 15 2791 = 5032 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2791) = 3 ^ 10 * m + 5032 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2791.1, data_15_2791.2]

/-- Complete interval computation for depth 15, residue 2792. -/
theorem bounds_15_2792 : exactInterval 15 2792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2792 : oddCount 2792 15 = 4 ∧ acceleratedOrbit 15 2792 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2792) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2792.1, data_15_2792.2]

/-- Complete interval computation for depth 15, residue 2793. -/
theorem bounds_15_2793 : exactInterval 15 2793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2793 : oddCount 2793 15 = 9 ∧ acceleratedOrbit 15 2793 = 1679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2793) = 3 ^ 9 * m + 1679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2793.1, data_15_2793.2]

/-- Complete interval computation for depth 15, residue 2794. -/
theorem bounds_15_2794 : exactInterval 15 2794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2794 : oddCount 2794 15 = 4 ∧ acceleratedOrbit 15 2794 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2794) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2794.1, data_15_2794.2]

/-- Complete interval computation for depth 15, residue 2795. -/
theorem bounds_15_2795 : exactInterval 15 2795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2795 : oddCount 2795 15 = 10 ∧ acceleratedOrbit 15 2795 = 5042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2795) = 3 ^ 10 * m + 5042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2795.1, data_15_2795.2]

/-- Complete interval computation for depth 15, residue 2796. -/
theorem bounds_15_2796 : exactInterval 15 2796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2796 : oddCount 2796 15 = 8 ∧ acceleratedOrbit 15 2796 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2796) = 3 ^ 8 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2796.1, data_15_2796.2]

/-- Complete interval computation for depth 15, residue 2797. -/
theorem bounds_15_2797 : exactInterval 15 2797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2797 : oddCount 2797 15 = 8 ∧ acceleratedOrbit 15 2797 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2797) = 3 ^ 8 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2797.1, data_15_2797.2]

/-- Complete interval computation for depth 15, residue 2798. -/
theorem bounds_15_2798 : exactInterval 15 2798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2798 : oddCount 2798 15 = 8 ∧ acceleratedOrbit 15 2798 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2798) = 3 ^ 8 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2798.1, data_15_2798.2]

/-- Complete interval computation for depth 15, residue 2799. -/
theorem bounds_15_2799 : exactInterval 15 2799 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2799) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2799 : oddCount 2799 15 = 9 ∧ acceleratedOrbit 15 2799 = 1682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2799) = 3 ^ 9 * m + 1682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2799.1, data_15_2799.2]

/-- Complete interval computation for depth 15, residue 2800. -/
theorem bounds_15_2800 : exactInterval 15 2800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2800 : oddCount 2800 15 = 8 ∧ acceleratedOrbit 15 2800 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2800) = 3 ^ 8 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2800.1, data_15_2800.2]

/-- Complete interval computation for depth 15, residue 2801. -/
theorem bounds_15_2801 : exactInterval 15 2801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2801 : oddCount 2801 15 = 4 ∧ acceleratedOrbit 15 2801 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2801) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2801.1, data_15_2801.2]

/-- Complete interval computation for depth 15, residue 2802. -/
theorem bounds_15_2802 : exactInterval 15 2802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2802 : oddCount 2802 15 = 11 ∧ acceleratedOrbit 15 2802 = 15173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2802) = 3 ^ 11 * m + 15173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2802.1, data_15_2802.2]

/-- Complete interval computation for depth 15, residue 2803. -/
theorem bounds_15_2803 : exactInterval 15 2803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2803 : oddCount 2803 15 = 11 ∧ acceleratedOrbit 15 2803 = 15173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2803) = 3 ^ 11 * m + 15173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2803.1, data_15_2803.2]

/-- Complete interval computation for depth 15, residue 2804. -/
theorem bounds_15_2804 : exactInterval 15 2804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2804 : oddCount 2804 15 = 8 ∧ acceleratedOrbit 15 2804 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2804) = 3 ^ 8 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2804.1, data_15_2804.2]

/-- Complete interval computation for depth 15, residue 2805. -/
theorem bounds_15_2805 : exactInterval 15 2805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2805 : oddCount 2805 15 = 8 ∧ acceleratedOrbit 15 2805 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2805) = 3 ^ 8 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2805.1, data_15_2805.2]

/-- Complete interval computation for depth 15, residue 2806. -/
theorem bounds_15_2806 : exactInterval 15 2806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2806 : oddCount 2806 15 = 7 ∧ acceleratedOrbit 15 2806 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2806) = 3 ^ 7 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2806.1, data_15_2806.2]

/-- Complete interval computation for depth 15, residue 2807. -/
theorem bounds_15_2807 : exactInterval 15 2807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2807 : oddCount 2807 15 = 7 ∧ acceleratedOrbit 15 2807 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2807) = 3 ^ 7 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2807.1, data_15_2807.2]

/-- Complete interval computation for depth 15, residue 2808. -/
theorem bounds_15_2808 : exactInterval 15 2808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2808 : oddCount 2808 15 = 8 ∧ acceleratedOrbit 15 2808 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2808) = 3 ^ 8 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2808.1, data_15_2808.2]

/-- Complete interval computation for depth 15, residue 2809. -/
theorem bounds_15_2809 : exactInterval 15 2809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2809 : oddCount 2809 15 = 9 ∧ acceleratedOrbit 15 2809 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2809) = 3 ^ 9 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2809.1, data_15_2809.2]

/-- Complete interval computation for depth 15, residue 2810. -/
theorem bounds_15_2810 : exactInterval 15 2810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2810 : oddCount 2810 15 = 8 ∧ acceleratedOrbit 15 2810 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2810) = 3 ^ 8 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2810.1, data_15_2810.2]

/-- Complete interval computation for depth 15, residue 2811. -/
theorem bounds_15_2811 : exactInterval 15 2811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2811 : oddCount 2811 15 = 10 ∧ acceleratedOrbit 15 2811 = 5069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2811) = 3 ^ 10 * m + 5069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2811.1, data_15_2811.2]

/-- Complete interval computation for depth 15, residue 2812. -/
theorem bounds_15_2812 : exactInterval 15 2812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2812 : oddCount 2812 15 = 11 ∧ acceleratedOrbit 15 2812 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2812) = 3 ^ 11 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2812.1, data_15_2812.2]

/-- Complete interval computation for depth 15, residue 2813. -/
theorem bounds_15_2813 : exactInterval 15 2813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2813 : oddCount 2813 15 = 11 ∧ acceleratedOrbit 15 2813 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2813) = 3 ^ 11 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2813.1, data_15_2813.2]

/-- Complete interval computation for depth 15, residue 2814. -/
theorem bounds_15_2814 : exactInterval 15 2814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2814 : oddCount 2814 15 = 11 ∧ acceleratedOrbit 15 2814 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2814) = 3 ^ 11 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2814.1, data_15_2814.2]

/-- Complete interval computation for depth 15, residue 2815. -/
theorem bounds_15_2815 : exactInterval 15 2815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2815 : oddCount 2815 15 = 10 ∧ acceleratedOrbit 15 2815 = 5075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2815) = 3 ^ 10 * m + 5075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2815.1, data_15_2815.2]

/-- Complete interval computation for depth 15, residue 2816. -/
theorem bounds_15_2816 : exactInterval 15 2816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2816 : oddCount 2816 15 = 4 ∧ acceleratedOrbit 15 2816 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2816) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2816.1, data_15_2816.2]

/-- Complete interval computation for depth 15, residue 2817. -/
theorem bounds_15_2817 : exactInterval 15 2817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2817 : oddCount 2817 15 = 9 ∧ acceleratedOrbit 15 2817 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2817) = 3 ^ 9 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2817.1, data_15_2817.2]

end Collatz.Research.PassageAtlas.Batch0086
