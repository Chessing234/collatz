import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0757

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24772. -/
theorem bounds_15_24772 : exactInterval 15 24772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24772 : oddCount 24772 15 = 8 ∧ acceleratedOrbit 15 24772 = 4967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24772) = 3 ^ 8 * m + 4967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24772.1, data_15_24772.2]

/-- Complete interval computation for depth 15, residue 24773. -/
theorem bounds_15_24773 : exactInterval 15 24773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24773 : oddCount 24773 15 = 8 ∧ acceleratedOrbit 15 24773 = 4967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24773) = 3 ^ 8 * m + 4967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24773.1, data_15_24773.2]

/-- Complete interval computation for depth 15, residue 24774. -/
theorem bounds_15_24774 : exactInterval 15 24774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24774 : oddCount 24774 15 = 8 ∧ acceleratedOrbit 15 24774 = 4967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24774) = 3 ^ 8 * m + 4967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24774.1, data_15_24774.2]

/-- Complete interval computation for depth 15, residue 24775. -/
theorem bounds_15_24775 : exactInterval 15 24775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24775 : oddCount 24775 15 = 10 ∧ acceleratedOrbit 15 24775 = 44651 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24775) = 3 ^ 10 * m + 44651 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24775.1, data_15_24775.2]

/-- Complete interval computation for depth 15, residue 24776. -/
theorem bounds_15_24776 : exactInterval 15 24776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24776 : oddCount 24776 15 = 8 ∧ acceleratedOrbit 15 24776 = 4967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24776) = 3 ^ 8 * m + 4967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24776.1, data_15_24776.2]

/-- Complete interval computation for depth 15, residue 24777. -/
theorem bounds_15_24777 : exactInterval 15 24777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24777 : oddCount 24777 15 = 5 ∧ acceleratedOrbit 15 24777 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24777) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24777.1, data_15_24777.2]

/-- Complete interval computation for depth 15, residue 24778. -/
theorem bounds_15_24778 : exactInterval 15 24778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24778 : oddCount 24778 15 = 8 ∧ acceleratedOrbit 15 24778 = 4967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24778) = 3 ^ 8 * m + 4967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24778.1, data_15_24778.2]

/-- Complete interval computation for depth 15, residue 24779. -/
theorem bounds_15_24779 : exactInterval 15 24779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24779 : oddCount 24779 15 = 8 ∧ acceleratedOrbit 15 24779 = 4963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24779) = 3 ^ 8 * m + 4963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24779.1, data_15_24779.2]

/-- Complete interval computation for depth 15, residue 24780. -/
theorem bounds_15_24780 : exactInterval 15 24780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24780 : oddCount 24780 15 = 8 ∧ acceleratedOrbit 15 24780 = 4967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24780) = 3 ^ 8 * m + 4967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24780.1, data_15_24780.2]

/-- Complete interval computation for depth 15, residue 24781. -/
theorem bounds_15_24781 : exactInterval 15 24781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24781 : oddCount 24781 15 = 8 ∧ acceleratedOrbit 15 24781 = 4967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24781) = 3 ^ 8 * m + 4967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24781.1, data_15_24781.2]

/-- Complete interval computation for depth 15, residue 24782. -/
theorem bounds_15_24782 : exactInterval 15 24782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24782 : oddCount 24782 15 = 9 ∧ acceleratedOrbit 15 24782 = 14888 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24782) = 3 ^ 9 * m + 14888 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24782.1, data_15_24782.2]

/-- Complete interval computation for depth 15, residue 24783. -/
theorem bounds_15_24783 : exactInterval 15 24783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24783 : oddCount 24783 15 = 9 ∧ acceleratedOrbit 15 24783 = 14888 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24783) = 3 ^ 9 * m + 14888 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24783.1, data_15_24783.2]

/-- Complete interval computation for depth 15, residue 24784. -/
theorem bounds_15_24784 : exactInterval 15 24784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24784 : oddCount 24784 15 = 4 ∧ acceleratedOrbit 15 24784 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24784) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24784.1, data_15_24784.2]

/-- Complete interval computation for depth 15, residue 24785. -/
theorem bounds_15_24785 : exactInterval 15 24785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24785 : oddCount 24785 15 = 7 ∧ acceleratedOrbit 15 24785 = 1655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24785) = 3 ^ 7 * m + 1655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24785.1, data_15_24785.2]

/-- Complete interval computation for depth 15, residue 24786. -/
theorem bounds_15_24786 : exactInterval 15 24786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24786 : oddCount 24786 15 = 7 ∧ acceleratedOrbit 15 24786 = 1655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24786) = 3 ^ 7 * m + 1655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24786.1, data_15_24786.2]

/-- Complete interval computation for depth 15, residue 24787. -/
theorem bounds_15_24787 : exactInterval 15 24787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24787 : oddCount 24787 15 = 7 ∧ acceleratedOrbit 15 24787 = 1655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24787) = 3 ^ 7 * m + 1655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24787.1, data_15_24787.2]

/-- Complete interval computation for depth 15, residue 24788. -/
theorem bounds_15_24788 : exactInterval 15 24788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24788 : oddCount 24788 15 = 4 ∧ acceleratedOrbit 15 24788 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24788) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24788.1, data_15_24788.2]

/-- Complete interval computation for depth 15, residue 24789. -/
theorem bounds_15_24789 : exactInterval 15 24789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24789 : oddCount 24789 15 = 4 ∧ acceleratedOrbit 15 24789 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24789) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24789.1, data_15_24789.2]

/-- Complete interval computation for depth 15, residue 24790. -/
theorem bounds_15_24790 : exactInterval 15 24790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24790 : oddCount 24790 15 = 9 ∧ acceleratedOrbit 15 24790 = 14894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24790) = 3 ^ 9 * m + 14894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24790.1, data_15_24790.2]

/-- Complete interval computation for depth 15, residue 24791. -/
theorem bounds_15_24791 : exactInterval 15 24791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24791 : oddCount 24791 15 = 9 ∧ acceleratedOrbit 15 24791 = 14894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24791) = 3 ^ 9 * m + 14894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24791.1, data_15_24791.2]

/-- Complete interval computation for depth 15, residue 24792. -/
theorem bounds_15_24792 : exactInterval 15 24792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24792 : oddCount 24792 15 = 9 ∧ acceleratedOrbit 15 24792 = 14899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24792) = 3 ^ 9 * m + 14899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24792.1, data_15_24792.2]

/-- Complete interval computation for depth 15, residue 24793. -/
theorem bounds_15_24793 : exactInterval 15 24793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24793 : oddCount 24793 15 = 8 ∧ acceleratedOrbit 15 24793 = 4967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24793) = 3 ^ 8 * m + 4967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24793.1, data_15_24793.2]

/-- Complete interval computation for depth 15, residue 24794. -/
theorem bounds_15_24794 : exactInterval 15 24794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24794 : oddCount 24794 15 = 9 ∧ acceleratedOrbit 15 24794 = 14899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24794) = 3 ^ 9 * m + 14899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24794.1, data_15_24794.2]

/-- Complete interval computation for depth 15, residue 24795. -/
theorem bounds_15_24795 : exactInterval 15 24795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24795 : oddCount 24795 15 = 7 ∧ acceleratedOrbit 15 24795 = 1655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24795) = 3 ^ 7 * m + 1655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24795.1, data_15_24795.2]

/-- Complete interval computation for depth 15, residue 24796. -/
theorem bounds_15_24796 : exactInterval 15 24796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24796 : oddCount 24796 15 = 9 ∧ acceleratedOrbit 15 24796 = 14899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24796) = 3 ^ 9 * m + 14899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24796.1, data_15_24796.2]

/-- Complete interval computation for depth 15, residue 24797. -/
theorem bounds_15_24797 : exactInterval 15 24797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24797 : oddCount 24797 15 = 9 ∧ acceleratedOrbit 15 24797 = 14899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24797) = 3 ^ 9 * m + 14899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24797.1, data_15_24797.2]

/-- Complete interval computation for depth 15, residue 24798. -/
theorem bounds_15_24798 : exactInterval 15 24798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24798 : oddCount 24798 15 = 11 ∧ acceleratedOrbit 15 24798 = 134075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24798) = 3 ^ 11 * m + 134075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24798.1, data_15_24798.2]

/-- Complete interval computation for depth 15, residue 24799. -/
theorem bounds_15_24799 : exactInterval 15 24799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24799 : oddCount 24799 15 = 11 ∧ acceleratedOrbit 15 24799 = 134075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24799) = 3 ^ 11 * m + 134075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24799.1, data_15_24799.2]

/-- Complete interval computation for depth 15, residue 24800. -/
theorem bounds_15_24800 : exactInterval 15 24800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24800 : oddCount 24800 15 = 6 ∧ acceleratedOrbit 15 24800 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24800) = 3 ^ 6 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24800.1, data_15_24800.2]

/-- Complete interval computation for depth 15, residue 24801. -/
theorem bounds_15_24801 : exactInterval 15 24801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24801 : oddCount 24801 15 = 12 ∧ acceleratedOrbit 15 24801 = 402272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24801) = 3 ^ 12 * m + 402272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24801.1, data_15_24801.2]

/-- Complete interval computation for depth 15, residue 24802. -/
theorem bounds_15_24802 : exactInterval 15 24802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24802 : oddCount 24802 15 = 4 ∧ acceleratedOrbit 15 24802 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24802) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24802.1, data_15_24802.2]

/-- Complete interval computation for depth 15, residue 24803. -/
theorem bounds_15_24803 : exactInterval 15 24803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24803 : oddCount 24803 15 = 4 ∧ acceleratedOrbit 15 24803 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24803) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24803.1, data_15_24803.2]

/-- Complete interval computation for depth 15, residue 24804. -/
theorem bounds_15_24804 : exactInterval 15 24804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24804 : oddCount 24804 15 = 5 ∧ acceleratedOrbit 15 24804 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24804) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24804.1, data_15_24804.2]

end Collatz.Research.PassageAtlas.Batch0757
