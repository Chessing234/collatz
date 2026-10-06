import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0360

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11763. -/
theorem bounds_15_11763 : exactInterval 15 11763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11763 : oddCount 11763 15 = 6 ∧ acceleratedOrbit 15 11763 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11763) = 3 ^ 6 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11763.1, data_15_11763.2]

/-- Complete interval computation for depth 15, residue 11764. -/
theorem bounds_15_11764 : exactInterval 15 11764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11764 : oddCount 11764 15 = 6 ∧ acceleratedOrbit 15 11764 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11764) = 3 ^ 6 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11764.1, data_15_11764.2]

/-- Complete interval computation for depth 15, residue 11765. -/
theorem bounds_15_11765 : exactInterval 15 11765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11765 : oddCount 11765 15 = 6 ∧ acceleratedOrbit 15 11765 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11765) = 3 ^ 6 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11765.1, data_15_11765.2]

/-- Complete interval computation for depth 15, residue 11766. -/
theorem bounds_15_11766 : exactInterval 15 11766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11766 : oddCount 11766 15 = 8 ∧ acceleratedOrbit 15 11766 = 2357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11766) = 3 ^ 8 * m + 2357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11766.1, data_15_11766.2]

/-- Complete interval computation for depth 15, residue 11767. -/
theorem bounds_15_11767 : exactInterval 15 11767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11767 : oddCount 11767 15 = 8 ∧ acceleratedOrbit 15 11767 = 2357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11767) = 3 ^ 8 * m + 2357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11767.1, data_15_11767.2]

/-- Complete interval computation for depth 15, residue 11768. -/
theorem bounds_15_11768 : exactInterval 15 11768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11768 : oddCount 11768 15 = 11 ∧ acceleratedOrbit 15 11768 = 63665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11768) = 3 ^ 11 * m + 63665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11768.1, data_15_11768.2]

/-- Complete interval computation for depth 15, residue 11769. -/
theorem bounds_15_11769 : exactInterval 15 11769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11769 : oddCount 11769 15 = 9 ∧ acceleratedOrbit 15 11769 = 7073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11769) = 3 ^ 9 * m + 7073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11769.1, data_15_11769.2]

/-- Complete interval computation for depth 15, residue 11770. -/
theorem bounds_15_11770 : exactInterval 15 11770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11770 : oddCount 11770 15 = 11 ∧ acceleratedOrbit 15 11770 = 63665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11770) = 3 ^ 11 * m + 63665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11770.1, data_15_11770.2]

/-- Complete interval computation for depth 15, residue 11771. -/
theorem bounds_15_11771 : exactInterval 15 11771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11771 : oddCount 11771 15 = 9 ∧ acceleratedOrbit 15 11771 = 7073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11771) = 3 ^ 9 * m + 7073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11771.1, data_15_11771.2]

/-- Complete interval computation for depth 15, residue 11772. -/
theorem bounds_15_11772 : exactInterval 15 11772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11772 : oddCount 11772 15 = 11 ∧ acceleratedOrbit 15 11772 = 63665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11772) = 3 ^ 11 * m + 63665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11772.1, data_15_11772.2]

/-- Complete interval computation for depth 15, residue 11773. -/
theorem bounds_15_11773 : exactInterval 15 11773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11773 : oddCount 11773 15 = 11 ∧ acceleratedOrbit 15 11773 = 63665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11773) = 3 ^ 11 * m + 63665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11773.1, data_15_11773.2]

/-- Complete interval computation for depth 15, residue 11774. -/
theorem bounds_15_11774 : exactInterval 15 11774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11774 : oddCount 11774 15 = 12 ∧ acceleratedOrbit 15 11774 = 190988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11774) = 3 ^ 12 * m + 190988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11774.1, data_15_11774.2]

/-- Complete interval computation for depth 15, residue 11775. -/
theorem bounds_15_11775 : exactInterval 15 11775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11775 : oddCount 11775 15 = 12 ∧ acceleratedOrbit 15 11775 = 190988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11775) = 3 ^ 12 * m + 190988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11775.1, data_15_11775.2]

/-- Complete interval computation for depth 15, residue 11776. -/
theorem bounds_15_11776 : exactInterval 15 11776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11776 : oddCount 11776 15 = 3 ∧ acceleratedOrbit 15 11776 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11776) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11776.1, data_15_11776.2]

/-- Complete interval computation for depth 15, residue 11777. -/
theorem bounds_15_11777 : exactInterval 15 11777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11777 : oddCount 11777 15 = 8 ∧ acceleratedOrbit 15 11777 = 2359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11777) = 3 ^ 8 * m + 2359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11777.1, data_15_11777.2]

/-- Complete interval computation for depth 15, residue 11778. -/
theorem bounds_15_11778 : exactInterval 15 11778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11778 : oddCount 11778 15 = 6 ∧ acceleratedOrbit 15 11778 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11778) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11778.1, data_15_11778.2]

/-- Complete interval computation for depth 15, residue 11779. -/
theorem bounds_15_11779 : exactInterval 15 11779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11779 : oddCount 11779 15 = 6 ∧ acceleratedOrbit 15 11779 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11779) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11779.1, data_15_11779.2]

/-- Complete interval computation for depth 15, residue 11780. -/
theorem bounds_15_11780 : exactInterval 15 11780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11780 : oddCount 11780 15 = 8 ∧ acceleratedOrbit 15 11780 = 2362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11780) = 3 ^ 8 * m + 2362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11780.1, data_15_11780.2]

/-- Complete interval computation for depth 15, residue 11781. -/
theorem bounds_15_11781 : exactInterval 15 11781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11781 : oddCount 11781 15 = 8 ∧ acceleratedOrbit 15 11781 = 2362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11781) = 3 ^ 8 * m + 2362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11781.1, data_15_11781.2]

/-- Complete interval computation for depth 15, residue 11782. -/
theorem bounds_15_11782 : exactInterval 15 11782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11782 : oddCount 11782 15 = 8 ∧ acceleratedOrbit 15 11782 = 2362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11782) = 3 ^ 8 * m + 2362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11782.1, data_15_11782.2]

/-- Complete interval computation for depth 15, residue 11783. -/
theorem bounds_15_11783 : exactInterval 15 11783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11783 : oddCount 11783 15 = 8 ∧ acceleratedOrbit 15 11783 = 2360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11783) = 3 ^ 8 * m + 2360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11783.1, data_15_11783.2]

/-- Complete interval computation for depth 15, residue 11784. -/
theorem bounds_15_11784 : exactInterval 15 11784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11784 : oddCount 11784 15 = 6 ∧ acceleratedOrbit 15 11784 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11784) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11784.1, data_15_11784.2]

/-- Complete interval computation for depth 15, residue 11785. -/
theorem bounds_15_11785 : exactInterval 15 11785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11785 : oddCount 11785 15 = 7 ∧ acceleratedOrbit 15 11785 = 787 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11785) = 3 ^ 7 * m + 787 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11785.1, data_15_11785.2]

/-- Complete interval computation for depth 15, residue 11786. -/
theorem bounds_15_11786 : exactInterval 15 11786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11786 : oddCount 11786 15 = 6 ∧ acceleratedOrbit 15 11786 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11786) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11786.1, data_15_11786.2]

/-- Complete interval computation for depth 15, residue 11787. -/
theorem bounds_15_11787 : exactInterval 15 11787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11787 : oddCount 11787 15 = 8 ∧ acceleratedOrbit 15 11787 = 2362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11787) = 3 ^ 8 * m + 2362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11787.1, data_15_11787.2]

/-- Complete interval computation for depth 15, residue 11788. -/
theorem bounds_15_11788 : exactInterval 15 11788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11788 : oddCount 11788 15 = 6 ∧ acceleratedOrbit 15 11788 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11788) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11788.1, data_15_11788.2]

/-- Complete interval computation for depth 15, residue 11789. -/
theorem bounds_15_11789 : exactInterval 15 11789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11789 : oddCount 11789 15 = 6 ∧ acceleratedOrbit 15 11789 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11789) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11789.1, data_15_11789.2]

/-- Complete interval computation for depth 15, residue 11790. -/
theorem bounds_15_11790 : exactInterval 15 11790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11790 : oddCount 11790 15 = 8 ∧ acceleratedOrbit 15 11790 = 2362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11790) = 3 ^ 8 * m + 2362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11790.1, data_15_11790.2]

/-- Complete interval computation for depth 15, residue 11791. -/
theorem bounds_15_11791 : exactInterval 15 11791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11791 : oddCount 11791 15 = 8 ∧ acceleratedOrbit 15 11791 = 2362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11791) = 3 ^ 8 * m + 2362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11791.1, data_15_11791.2]

/-- Complete interval computation for depth 15, residue 11792. -/
theorem bounds_15_11792 : exactInterval 15 11792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11792 : oddCount 11792 15 = 8 ∧ acceleratedOrbit 15 11792 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11792) = 3 ^ 8 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11792.1, data_15_11792.2]

/-- Complete interval computation for depth 15, residue 11793. -/
theorem bounds_15_11793 : exactInterval 15 11793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11793 : oddCount 11793 15 = 6 ∧ acceleratedOrbit 15 11793 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11793) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11793.1, data_15_11793.2]

/-- Complete interval computation for depth 15, residue 11794. -/
theorem bounds_15_11794 : exactInterval 15 11794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11794 : oddCount 11794 15 = 10 ∧ acceleratedOrbit 15 11794 = 21262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11794) = 3 ^ 10 * m + 21262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11794.1, data_15_11794.2]

/-- Complete interval computation for depth 15, residue 11795. -/
theorem bounds_15_11795 : exactInterval 15 11795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11795 : oddCount 11795 15 = 10 ∧ acceleratedOrbit 15 11795 = 21262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11795) = 3 ^ 10 * m + 21262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11795.1, data_15_11795.2]

end Collatz.Research.PassageAtlas.Batch0360
