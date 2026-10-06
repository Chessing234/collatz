import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0940

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30769. -/
theorem bounds_15_30769 : exactInterval 15 30769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30769 : oddCount 30769 15 = 9 ∧ acceleratedOrbit 15 30769 = 18488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30769) = 3 ^ 9 * m + 18488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30769.1, data_15_30769.2]

/-- Complete interval computation for depth 15, residue 30770. -/
theorem bounds_15_30770 : exactInterval 15 30770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30770 : oddCount 30770 15 = 9 ∧ acceleratedOrbit 15 30770 = 18488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30770) = 3 ^ 9 * m + 18488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30770.1, data_15_30770.2]

/-- Complete interval computation for depth 15, residue 30771. -/
theorem bounds_15_30771 : exactInterval 15 30771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30771 : oddCount 30771 15 = 9 ∧ acceleratedOrbit 15 30771 = 18488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30771) = 3 ^ 9 * m + 18488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30771.1, data_15_30771.2]

/-- Complete interval computation for depth 15, residue 30772. -/
theorem bounds_15_30772 : exactInterval 15 30772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30772 : oddCount 30772 15 = 5 ∧ acceleratedOrbit 15 30772 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30772) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30772.1, data_15_30772.2]

/-- Complete interval computation for depth 15, residue 30773. -/
theorem bounds_15_30773 : exactInterval 15 30773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30773 : oddCount 30773 15 = 5 ∧ acceleratedOrbit 15 30773 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30773) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30773.1, data_15_30773.2]

/-- Complete interval computation for depth 15, residue 30774. -/
theorem bounds_15_30774 : exactInterval 15 30774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30774 : oddCount 30774 15 = 9 ∧ acceleratedOrbit 15 30774 = 18487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30774) = 3 ^ 9 * m + 18487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30774.1, data_15_30774.2]

/-- Complete interval computation for depth 15, residue 30775. -/
theorem bounds_15_30775 : exactInterval 15 30775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30775 : oddCount 30775 15 = 9 ∧ acceleratedOrbit 15 30775 = 18487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30775) = 3 ^ 9 * m + 18487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30775.1, data_15_30775.2]

/-- Complete interval computation for depth 15, residue 30776. -/
theorem bounds_15_30776 : exactInterval 15 30776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30776 : oddCount 30776 15 = 6 ∧ acceleratedOrbit 15 30776 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30776) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30776.1, data_15_30776.2]

/-- Complete interval computation for depth 15, residue 30777. -/
theorem bounds_15_30777 : exactInterval 15 30777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30777 : oddCount 30777 15 = 6 ∧ acceleratedOrbit 15 30777 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30777) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30777.1, data_15_30777.2]

/-- Complete interval computation for depth 15, residue 30778. -/
theorem bounds_15_30778 : exactInterval 15 30778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30778 : oddCount 30778 15 = 6 ∧ acceleratedOrbit 15 30778 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30778) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30778.1, data_15_30778.2]

/-- Complete interval computation for depth 15, residue 30779. -/
theorem bounds_15_30779 : exactInterval 15 30779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30779 : oddCount 30779 15 = 8 ∧ acceleratedOrbit 15 30779 = 6164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30779) = 3 ^ 8 * m + 6164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30779.1, data_15_30779.2]

/-- Complete interval computation for depth 15, residue 30780. -/
theorem bounds_15_30780 : exactInterval 15 30780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30780 : oddCount 30780 15 = 6 ∧ acceleratedOrbit 15 30780 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30780) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30780.1, data_15_30780.2]

/-- Complete interval computation for depth 15, residue 30781. -/
theorem bounds_15_30781 : exactInterval 15 30781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30781 : oddCount 30781 15 = 6 ∧ acceleratedOrbit 15 30781 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30781) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30781.1, data_15_30781.2]

/-- Complete interval computation for depth 15, residue 30782. -/
theorem bounds_15_30782 : exactInterval 15 30782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30782 : oddCount 30782 15 = 10 ∧ acceleratedOrbit 15 30782 = 55475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30782) = 3 ^ 10 * m + 55475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30782.1, data_15_30782.2]

/-- Complete interval computation for depth 15, residue 30783. -/
theorem bounds_15_30783 : exactInterval 15 30783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30783 : oddCount 30783 15 = 10 ∧ acceleratedOrbit 15 30783 = 55475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30783) = 3 ^ 10 * m + 55475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30783.1, data_15_30783.2]

/-- Complete interval computation for depth 15, residue 30784. -/
theorem bounds_15_30784 : exactInterval 15 30784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30784 : oddCount 30784 15 = 6 ∧ acceleratedOrbit 15 30784 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30784) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30784.1, data_15_30784.2]

/-- Complete interval computation for depth 15, residue 30785. -/
theorem bounds_15_30785 : exactInterval 15 30785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30785 : oddCount 30785 15 = 8 ∧ acceleratedOrbit 15 30785 = 6166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30785) = 3 ^ 8 * m + 6166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30785.1, data_15_30785.2]

/-- Complete interval computation for depth 15, residue 30786. -/
theorem bounds_15_30786 : exactInterval 15 30786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30786 : oddCount 30786 15 = 8 ∧ acceleratedOrbit 15 30786 = 6166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30786) = 3 ^ 8 * m + 6166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30786.1, data_15_30786.2]

/-- Complete interval computation for depth 15, residue 30787. -/
theorem bounds_15_30787 : exactInterval 15 30787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30787 : oddCount 30787 15 = 8 ∧ acceleratedOrbit 15 30787 = 6166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30787) = 3 ^ 8 * m + 6166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30787.1, data_15_30787.2]

/-- Complete interval computation for depth 15, residue 30788. -/
theorem bounds_15_30788 : exactInterval 15 30788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30788 : oddCount 30788 15 = 5 ∧ acceleratedOrbit 15 30788 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30788) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30788.1, data_15_30788.2]

/-- Complete interval computation for depth 15, residue 30789. -/
theorem bounds_15_30789 : exactInterval 15 30789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30789 : oddCount 30789 15 = 5 ∧ acceleratedOrbit 15 30789 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30789) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30789.1, data_15_30789.2]

/-- Complete interval computation for depth 15, residue 30790. -/
theorem bounds_15_30790 : exactInterval 15 30790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30790 : oddCount 30790 15 = 5 ∧ acceleratedOrbit 15 30790 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30790) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30790.1, data_15_30790.2]

/-- Complete interval computation for depth 15, residue 30791. -/
theorem bounds_15_30791 : exactInterval 15 30791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30791 : oddCount 30791 15 = 9 ∧ acceleratedOrbit 15 30791 = 18497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30791) = 3 ^ 9 * m + 18497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30791.1, data_15_30791.2]

/-- Complete interval computation for depth 15, residue 30792. -/
theorem bounds_15_30792 : exactInterval 15 30792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30792 : oddCount 30792 15 = 8 ∧ acceleratedOrbit 15 30792 = 6169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30792) = 3 ^ 8 * m + 6169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30792.1, data_15_30792.2]

/-- Complete interval computation for depth 15, residue 30793. -/
theorem bounds_15_30793 : exactInterval 15 30793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30793 : oddCount 30793 15 = 10 ∧ acceleratedOrbit 15 30793 = 55495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30793) = 3 ^ 10 * m + 55495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30793.1, data_15_30793.2]

/-- Complete interval computation for depth 15, residue 30794. -/
theorem bounds_15_30794 : exactInterval 15 30794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30794 : oddCount 30794 15 = 8 ∧ acceleratedOrbit 15 30794 = 6169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30794) = 3 ^ 8 * m + 6169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30794.1, data_15_30794.2]

/-- Complete interval computation for depth 15, residue 30795. -/
theorem bounds_15_30795 : exactInterval 15 30795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30795 : oddCount 30795 15 = 5 ∧ acceleratedOrbit 15 30795 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30795) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30795.1, data_15_30795.2]

/-- Complete interval computation for depth 15, residue 30796. -/
theorem bounds_15_30796 : exactInterval 15 30796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30796 : oddCount 30796 15 = 8 ∧ acceleratedOrbit 15 30796 = 6169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30796) = 3 ^ 8 * m + 6169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30796.1, data_15_30796.2]

/-- Complete interval computation for depth 15, residue 30797. -/
theorem bounds_15_30797 : exactInterval 15 30797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30797 : oddCount 30797 15 = 8 ∧ acceleratedOrbit 15 30797 = 6169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30797) = 3 ^ 8 * m + 6169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30797.1, data_15_30797.2]

/-- Complete interval computation for depth 15, residue 30798. -/
theorem bounds_15_30798 : exactInterval 15 30798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30798 : oddCount 30798 15 = 7 ∧ acceleratedOrbit 15 30798 = 2056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30798) = 3 ^ 7 * m + 2056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30798.1, data_15_30798.2]

/-- Complete interval computation for depth 15, residue 30799. -/
theorem bounds_15_30799 : exactInterval 15 30799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30799 : oddCount 30799 15 = 7 ∧ acceleratedOrbit 15 30799 = 2056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30799) = 3 ^ 7 * m + 2056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30799.1, data_15_30799.2]

/-- Complete interval computation for depth 15, residue 30800. -/
theorem bounds_15_30800 : exactInterval 15 30800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30800 : oddCount 30800 15 = 6 ∧ acceleratedOrbit 15 30800 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30800) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30800.1, data_15_30800.2]

end Collatz.Research.PassageAtlas.Batch0940
