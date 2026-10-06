import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0391

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12779. -/
theorem bounds_15_12779 : exactInterval 15 12779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12779 : oddCount 12779 15 = 10 ∧ acceleratedOrbit 15 12779 = 23032 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12779) = 3 ^ 10 * m + 23032 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12779.1, data_15_12779.2]

/-- Complete interval computation for depth 15, residue 12780. -/
theorem bounds_15_12780 : exactInterval 15 12780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12780 : oddCount 12780 15 = 7 ∧ acceleratedOrbit 15 12780 = 854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12780) = 3 ^ 7 * m + 854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12780.1, data_15_12780.2]

/-- Complete interval computation for depth 15, residue 12781. -/
theorem bounds_15_12781 : exactInterval 15 12781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12781 : oddCount 12781 15 = 7 ∧ acceleratedOrbit 15 12781 = 854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12781) = 3 ^ 7 * m + 854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12781.1, data_15_12781.2]

/-- Complete interval computation for depth 15, residue 12782. -/
theorem bounds_15_12782 : exactInterval 15 12782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12782 : oddCount 12782 15 = 7 ∧ acceleratedOrbit 15 12782 = 854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12782) = 3 ^ 7 * m + 854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12782.1, data_15_12782.2]

/-- Complete interval computation for depth 15, residue 12783. -/
theorem bounds_15_12783 : exactInterval 15 12783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12783 : oddCount 12783 15 = 11 ∧ acceleratedOrbit 15 12783 = 69113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12783) = 3 ^ 11 * m + 69113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12783.1, data_15_12783.2]

/-- Complete interval computation for depth 15, residue 12784. -/
theorem bounds_15_12784 : exactInterval 15 12784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12784 : oddCount 12784 15 = 8 ∧ acceleratedOrbit 15 12784 = 2564 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12784) = 3 ^ 8 * m + 2564 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12784.1, data_15_12784.2]

/-- Complete interval computation for depth 15, residue 12785. -/
theorem bounds_15_12785 : exactInterval 15 12785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12785 : oddCount 12785 15 = 5 ∧ acceleratedOrbit 15 12785 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12785) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12785.1, data_15_12785.2]

/-- Complete interval computation for depth 15, residue 12786. -/
theorem bounds_15_12786 : exactInterval 15 12786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12786 : oddCount 12786 15 = 9 ∧ acceleratedOrbit 15 12786 = 7685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12786) = 3 ^ 9 * m + 7685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12786.1, data_15_12786.2]

/-- Complete interval computation for depth 15, residue 12787. -/
theorem bounds_15_12787 : exactInterval 15 12787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12787 : oddCount 12787 15 = 9 ∧ acceleratedOrbit 15 12787 = 7685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12787) = 3 ^ 9 * m + 7685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12787.1, data_15_12787.2]

/-- Complete interval computation for depth 15, residue 12788. -/
theorem bounds_15_12788 : exactInterval 15 12788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12788 : oddCount 12788 15 = 8 ∧ acceleratedOrbit 15 12788 = 2564 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12788) = 3 ^ 8 * m + 2564 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12788.1, data_15_12788.2]

/-- Complete interval computation for depth 15, residue 12789. -/
theorem bounds_15_12789 : exactInterval 15 12789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12789 : oddCount 12789 15 = 8 ∧ acceleratedOrbit 15 12789 = 2564 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12789) = 3 ^ 8 * m + 2564 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12789.1, data_15_12789.2]

/-- Complete interval computation for depth 15, residue 12790. -/
theorem bounds_15_12790 : exactInterval 15 12790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12790 : oddCount 12790 15 = 11 ∧ acceleratedOrbit 15 12790 = 69164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12790) = 3 ^ 11 * m + 69164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12790.1, data_15_12790.2]

/-- Complete interval computation for depth 15, residue 12791. -/
theorem bounds_15_12791 : exactInterval 15 12791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12791 : oddCount 12791 15 = 11 ∧ acceleratedOrbit 15 12791 = 69164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12791) = 3 ^ 11 * m + 69164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12791.1, data_15_12791.2]

/-- Complete interval computation for depth 15, residue 12792. -/
theorem bounds_15_12792 : exactInterval 15 12792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12792 : oddCount 12792 15 = 8 ∧ acceleratedOrbit 15 12792 = 2564 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12792) = 3 ^ 8 * m + 2564 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12792.1, data_15_12792.2]

/-- Complete interval computation for depth 15, residue 12793. -/
theorem bounds_15_12793 : exactInterval 15 12793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12793 : oddCount 12793 15 = 7 ∧ acceleratedOrbit 15 12793 = 854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12793) = 3 ^ 7 * m + 854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12793.1, data_15_12793.2]

/-- Complete interval computation for depth 15, residue 12794. -/
theorem bounds_15_12794 : exactInterval 15 12794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12794 : oddCount 12794 15 = 8 ∧ acceleratedOrbit 15 12794 = 2564 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12794) = 3 ^ 8 * m + 2564 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12794.1, data_15_12794.2]

/-- Complete interval computation for depth 15, residue 12795. -/
theorem bounds_15_12795 : exactInterval 15 12795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12795 : oddCount 12795 15 = 9 ∧ acceleratedOrbit 15 12795 = 7688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12795) = 3 ^ 9 * m + 7688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12795.1, data_15_12795.2]

/-- Complete interval computation for depth 15, residue 12796. -/
theorem bounds_15_12796 : exactInterval 15 12796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12796 : oddCount 12796 15 = 11 ∧ acceleratedOrbit 15 12796 = 69200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12796) = 3 ^ 11 * m + 69200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12796.1, data_15_12796.2]

/-- Complete interval computation for depth 15, residue 12797. -/
theorem bounds_15_12797 : exactInterval 15 12797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12797 : oddCount 12797 15 = 11 ∧ acceleratedOrbit 15 12797 = 69200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12797) = 3 ^ 11 * m + 69200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12797.1, data_15_12797.2]

/-- Complete interval computation for depth 15, residue 12798. -/
theorem bounds_15_12798 : exactInterval 15 12798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12798 : oddCount 12798 15 = 11 ∧ acceleratedOrbit 15 12798 = 69200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12798) = 3 ^ 11 * m + 69200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12798.1, data_15_12798.2]

/-- Complete interval computation for depth 15, residue 12799. -/
theorem bounds_15_12799 : exactInterval 15 12799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12799 : oddCount 12799 15 = 10 ∧ acceleratedOrbit 15 12799 = 23066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12799) = 3 ^ 10 * m + 23066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12799.1, data_15_12799.2]

/-- Complete interval computation for depth 15, residue 12800. -/
theorem bounds_15_12800 : exactInterval 15 12800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12800 : oddCount 12800 15 = 3 ∧ acceleratedOrbit 15 12800 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12800) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12800.1, data_15_12800.2]

/-- Complete interval computation for depth 15, residue 12801. -/
theorem bounds_15_12801 : exactInterval 15 12801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12801 : oddCount 12801 15 = 9 ∧ acceleratedOrbit 15 12801 = 7694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12801) = 3 ^ 9 * m + 7694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12801.1, data_15_12801.2]

/-- Complete interval computation for depth 15, residue 12802. -/
theorem bounds_15_12802 : exactInterval 15 12802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12802 : oddCount 12802 15 = 5 ∧ acceleratedOrbit 15 12802 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12802) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12802.1, data_15_12802.2]

/-- Complete interval computation for depth 15, residue 12803. -/
theorem bounds_15_12803 : exactInterval 15 12803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12803 : oddCount 12803 15 = 5 ∧ acceleratedOrbit 15 12803 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12803) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12803.1, data_15_12803.2]

/-- Complete interval computation for depth 15, residue 12804. -/
theorem bounds_15_12804 : exactInterval 15 12804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12804 : oddCount 12804 15 = 8 ∧ acceleratedOrbit 15 12804 = 2567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12804) = 3 ^ 8 * m + 2567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12804.1, data_15_12804.2]

/-- Complete interval computation for depth 15, residue 12805. -/
theorem bounds_15_12805 : exactInterval 15 12805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12805 : oddCount 12805 15 = 8 ∧ acceleratedOrbit 15 12805 = 2567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12805) = 3 ^ 8 * m + 2567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12805.1, data_15_12805.2]

/-- Complete interval computation for depth 15, residue 12806. -/
theorem bounds_15_12806 : exactInterval 15 12806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12806 : oddCount 12806 15 = 8 ∧ acceleratedOrbit 15 12806 = 2567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12806) = 3 ^ 8 * m + 2567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12806.1, data_15_12806.2]

/-- Complete interval computation for depth 15, residue 12807. -/
theorem bounds_15_12807 : exactInterval 15 12807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12807 : oddCount 12807 15 = 11 ∧ acceleratedOrbit 15 12807 = 69254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12807) = 3 ^ 11 * m + 69254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12807.1, data_15_12807.2]

/-- Complete interval computation for depth 15, residue 12808. -/
theorem bounds_15_12808 : exactInterval 15 12808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12808 : oddCount 12808 15 = 6 ∧ acceleratedOrbit 15 12808 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12808) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12808.1, data_15_12808.2]

/-- Complete interval computation for depth 15, residue 12809. -/
theorem bounds_15_12809 : exactInterval 15 12809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12809 : oddCount 12809 15 = 5 ∧ acceleratedOrbit 15 12809 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12809) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12809.1, data_15_12809.2]

/-- Complete interval computation for depth 15, residue 12810. -/
theorem bounds_15_12810 : exactInterval 15 12810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12810 : oddCount 12810 15 = 6 ∧ acceleratedOrbit 15 12810 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12810) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12810.1, data_15_12810.2]

/-- Complete interval computation for depth 15, residue 12811. -/
theorem bounds_15_12811 : exactInterval 15 12811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12811 : oddCount 12811 15 = 8 ∧ acceleratedOrbit 15 12811 = 2567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12811) = 3 ^ 8 * m + 2567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12811.1, data_15_12811.2]

end Collatz.Research.PassageAtlas.Batch0391
