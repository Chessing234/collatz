import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch1000

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32735. -/
theorem bounds_15_32735 : exactInterval 15 32735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32735 : oddCount 32735 15 = 10 ∧ acceleratedOrbit 15 32735 = 58994 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32735) = 3 ^ 10 * m + 58994 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32735.1, data_15_32735.2]

/-- Complete interval computation for depth 15, residue 32736. -/
theorem bounds_15_32736 : exactInterval 15 32736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32736 : oddCount 32736 15 = 10 ∧ acceleratedOrbit 15 32736 = 59048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32736) = 3 ^ 10 * m + 59048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32736.1, data_15_32736.2]

/-- Complete interval computation for depth 15, residue 32737. -/
theorem bounds_15_32737 : exactInterval 15 32737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32737 : oddCount 32737 15 = 9 ∧ acceleratedOrbit 15 32737 = 19666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32737) = 3 ^ 9 * m + 19666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32737.1, data_15_32737.2]

/-- Complete interval computation for depth 15, residue 32738. -/
theorem bounds_15_32738 : exactInterval 15 32738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32738 : oddCount 32738 15 = 9 ∧ acceleratedOrbit 15 32738 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32738) = 3 ^ 9 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32738.1, data_15_32738.2]

/-- Complete interval computation for depth 15, residue 32739. -/
theorem bounds_15_32739 : exactInterval 15 32739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32739 : oddCount 32739 15 = 9 ∧ acceleratedOrbit 15 32739 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32739) = 3 ^ 9 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32739.1, data_15_32739.2]

/-- Complete interval computation for depth 15, residue 32740. -/
theorem bounds_15_32740 : exactInterval 15 32740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32740 : oddCount 32740 15 = 9 ∧ acceleratedOrbit 15 32740 = 19673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32740) = 3 ^ 9 * m + 19673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32740.1, data_15_32740.2]

/-- Complete interval computation for depth 15, residue 32741. -/
theorem bounds_15_32741 : exactInterval 15 32741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32741 : oddCount 32741 15 = 9 ∧ acceleratedOrbit 15 32741 = 19673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32741) = 3 ^ 9 * m + 19673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32741.1, data_15_32741.2]

/-- Complete interval computation for depth 15, residue 32742. -/
theorem bounds_15_32742 : exactInterval 15 32742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32742 : oddCount 32742 15 = 9 ∧ acceleratedOrbit 15 32742 = 19673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32742) = 3 ^ 9 * m + 19673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32742.1, data_15_32742.2]

/-- Complete interval computation for depth 15, residue 32743. -/
theorem bounds_15_32743 : exactInterval 15 32743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32743 : oddCount 32743 15 = 10 ∧ acceleratedOrbit 15 32743 = 59008 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32743) = 3 ^ 10 * m + 59008 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32743.1, data_15_32743.2]

/-- Complete interval computation for depth 15, residue 32744. -/
theorem bounds_15_32744 : exactInterval 15 32744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32744 : oddCount 32744 15 = 10 ∧ acceleratedOrbit 15 32744 = 59048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32744) = 3 ^ 10 * m + 59048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32744.1, data_15_32744.2]

/-- Complete interval computation for depth 15, residue 32745. -/
theorem bounds_15_32745 : exactInterval 15 32745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32745 : oddCount 32745 15 = 10 ∧ acceleratedOrbit 15 32745 = 59012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32745) = 3 ^ 10 * m + 59012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32745.1, data_15_32745.2]

/-- Complete interval computation for depth 15, residue 32746. -/
theorem bounds_15_32746 : exactInterval 15 32746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32746 : oddCount 32746 15 = 10 ∧ acceleratedOrbit 15 32746 = 59048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32746) = 3 ^ 10 * m + 59048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32746.1, data_15_32746.2]

/-- Complete interval computation for depth 15, residue 32747. -/
theorem bounds_15_32747 : exactInterval 15 32747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32747 : oddCount 32747 15 = 10 ∧ acceleratedOrbit 15 32747 = 59015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32747) = 3 ^ 10 * m + 59015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32747.1, data_15_32747.2]

/-- Complete interval computation for depth 15, residue 32748. -/
theorem bounds_15_32748 : exactInterval 15 32748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32748 : oddCount 32748 15 = 9 ∧ acceleratedOrbit 15 32748 = 19676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32748) = 3 ^ 9 * m + 19676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32748.1, data_15_32748.2]

/-- Complete interval computation for depth 15, residue 32749. -/
theorem bounds_15_32749 : exactInterval 15 32749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32749 : oddCount 32749 15 = 9 ∧ acceleratedOrbit 15 32749 = 19676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32749) = 3 ^ 9 * m + 19676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32749.1, data_15_32749.2]

/-- Complete interval computation for depth 15, residue 32750. -/
theorem bounds_15_32750 : exactInterval 15 32750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32750 : oddCount 32750 15 = 9 ∧ acceleratedOrbit 15 32750 = 19676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32750) = 3 ^ 9 * m + 19676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32750.1, data_15_32750.2]

/-- Complete interval computation for depth 15, residue 32751. -/
theorem bounds_15_32751 : exactInterval 15 32751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32751 : oddCount 32751 15 = 11 ∧ acceleratedOrbit 15 32751 = 177065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32751) = 3 ^ 11 * m + 177065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32751.1, data_15_32751.2]

/-- Complete interval computation for depth 15, residue 32752. -/
theorem bounds_15_32752 : exactInterval 15 32752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32752 : oddCount 32752 15 = 11 ∧ acceleratedOrbit 15 32752 = 177146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32752) = 3 ^ 11 * m + 177146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32752.1, data_15_32752.2]

/-- Complete interval computation for depth 15, residue 32753. -/
theorem bounds_15_32753 : exactInterval 15 32753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32753 : oddCount 32753 15 = 10 ∧ acceleratedOrbit 15 32753 = 59048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32753) = 3 ^ 10 * m + 59048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32753.1, data_15_32753.2]

/-- Complete interval computation for depth 15, residue 32754. -/
theorem bounds_15_32754 : exactInterval 15 32754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32754 : oddCount 32754 15 = 9 ∧ acceleratedOrbit 15 32754 = 19678 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32754) = 3 ^ 9 * m + 19678 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32754.1, data_15_32754.2]

/-- Complete interval computation for depth 15, residue 32755. -/
theorem bounds_15_32755 : exactInterval 15 32755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32755 : oddCount 32755 15 = 9 ∧ acceleratedOrbit 15 32755 = 19678 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32755) = 3 ^ 9 * m + 19678 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32755.1, data_15_32755.2]

/-- Complete interval computation for depth 15, residue 32756. -/
theorem bounds_15_32756 : exactInterval 15 32756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32756 : oddCount 32756 15 = 11 ∧ acceleratedOrbit 15 32756 = 177146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32756) = 3 ^ 11 * m + 177146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32756.1, data_15_32756.2]

/-- Complete interval computation for depth 15, residue 32757. -/
theorem bounds_15_32757 : exactInterval 15 32757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32757 : oddCount 32757 15 = 11 ∧ acceleratedOrbit 15 32757 = 177146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32757) = 3 ^ 11 * m + 177146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32757.1, data_15_32757.2]

/-- Complete interval computation for depth 15, residue 32758. -/
theorem bounds_15_32758 : exactInterval 15 32758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32758 : oddCount 32758 15 = 10 ∧ acceleratedOrbit 15 32758 = 59039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32758) = 3 ^ 10 * m + 59039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32758.1, data_15_32758.2]

/-- Complete interval computation for depth 15, residue 32759. -/
theorem bounds_15_32759 : exactInterval 15 32759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32759 : oddCount 32759 15 = 10 ∧ acceleratedOrbit 15 32759 = 59039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32759) = 3 ^ 10 * m + 59039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32759.1, data_15_32759.2]

/-- Complete interval computation for depth 15, residue 32760. -/
theorem bounds_15_32760 : exactInterval 15 32760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32760 : oddCount 32760 15 = 12 ∧ acceleratedOrbit 15 32760 = 531440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32760) = 3 ^ 12 * m + 531440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32760.1, data_15_32760.2]

/-- Complete interval computation for depth 15, residue 32761. -/
theorem bounds_15_32761 : exactInterval 15 32761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32761 : oddCount 32761 15 = 10 ∧ acceleratedOrbit 15 32761 = 59042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32761) = 3 ^ 10 * m + 59042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32761.1, data_15_32761.2]

/-- Complete interval computation for depth 15, residue 32762. -/
theorem bounds_15_32762 : exactInterval 15 32762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32762 : oddCount 32762 15 = 12 ∧ acceleratedOrbit 15 32762 = 531440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32762) = 3 ^ 12 * m + 531440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32762.1, data_15_32762.2]

/-- Complete interval computation for depth 15, residue 32763. -/
theorem bounds_15_32763 : exactInterval 15 32763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32763 : oddCount 32763 15 = 10 ∧ acceleratedOrbit 15 32763 = 59044 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32763) = 3 ^ 10 * m + 59044 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32763.1, data_15_32763.2]

/-- Complete interval computation for depth 15, residue 32764. -/
theorem bounds_15_32764 : exactInterval 15 32764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32764 : oddCount 32764 15 = 13 ∧ acceleratedOrbit 15 32764 = 1594322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32764) = 3 ^ 13 * m + 1594322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32764.1, data_15_32764.2]

/-- Complete interval computation for depth 15, residue 32765. -/
theorem bounds_15_32765 : exactInterval 15 32765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32765 : oddCount 32765 15 = 13 ∧ acceleratedOrbit 15 32765 = 1594322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32765) = 3 ^ 13 * m + 1594322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32765.1, data_15_32765.2]

/-- Complete interval computation for depth 15, residue 32766. -/
theorem bounds_15_32766 : exactInterval 15 32766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32766 : oddCount 32766 15 = 14 ∧ acceleratedOrbit 15 32766 = 4782968 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32766) = 3 ^ 14 * m + 4782968 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32766.1, data_15_32766.2]

/-- Complete interval computation for depth 15, residue 32767. -/
theorem bounds_15_32767 : exactInterval 15 32767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32767 : oddCount 32767 15 = 15 ∧ acceleratedOrbit 15 32767 = 14348906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32767) = 3 ^ 15 * m + 14348906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32767.1, data_15_32767.2]

end Collatz.Research.PassageAtlas.Batch1000
