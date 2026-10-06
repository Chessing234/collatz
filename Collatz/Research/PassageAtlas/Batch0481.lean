import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0481

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15728. -/
theorem bounds_15_15728 : exactInterval 15 15728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15728 : oddCount 15728 15 = 8 ∧ acceleratedOrbit 15 15728 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15728) = 3 ^ 8 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15728.1, data_15_15728.2]

/-- Complete interval computation for depth 15, residue 15729. -/
theorem bounds_15_15729 : exactInterval 15 15729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15729 : oddCount 15729 15 = 8 ∧ acceleratedOrbit 15 15729 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15729) = 3 ^ 8 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15729.1, data_15_15729.2]

/-- Complete interval computation for depth 15, residue 15730. -/
theorem bounds_15_15730 : exactInterval 15 15730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15730 : oddCount 15730 15 = 8 ∧ acceleratedOrbit 15 15730 = 3152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15730) = 3 ^ 8 * m + 3152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15730.1, data_15_15730.2]

/-- Complete interval computation for depth 15, residue 15731. -/
theorem bounds_15_15731 : exactInterval 15 15731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15731 : oddCount 15731 15 = 8 ∧ acceleratedOrbit 15 15731 = 3152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15731) = 3 ^ 8 * m + 3152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15731.1, data_15_15731.2]

/-- Complete interval computation for depth 15, residue 15732. -/
theorem bounds_15_15732 : exactInterval 15 15732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15732 : oddCount 15732 15 = 8 ∧ acceleratedOrbit 15 15732 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15732) = 3 ^ 8 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15732.1, data_15_15732.2]

/-- Complete interval computation for depth 15, residue 15733. -/
theorem bounds_15_15733 : exactInterval 15 15733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15733 : oddCount 15733 15 = 8 ∧ acceleratedOrbit 15 15733 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15733) = 3 ^ 8 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15733.1, data_15_15733.2]

/-- Complete interval computation for depth 15, residue 15734. -/
theorem bounds_15_15734 : exactInterval 15 15734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15734 : oddCount 15734 15 = 8 ∧ acceleratedOrbit 15 15734 = 3152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15734) = 3 ^ 8 * m + 3152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15734.1, data_15_15734.2]

/-- Complete interval computation for depth 15, residue 15735. -/
theorem bounds_15_15735 : exactInterval 15 15735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15735 : oddCount 15735 15 = 8 ∧ acceleratedOrbit 15 15735 = 3152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15735) = 3 ^ 8 * m + 3152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15735.1, data_15_15735.2]

/-- Complete interval computation for depth 15, residue 15736. -/
theorem bounds_15_15736 : exactInterval 15 15736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15736 : oddCount 15736 15 = 7 ∧ acceleratedOrbit 15 15736 = 1052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15736) = 3 ^ 7 * m + 1052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15736.1, data_15_15736.2]

/-- Complete interval computation for depth 15, residue 15737. -/
theorem bounds_15_15737 : exactInterval 15 15737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15737 : oddCount 15737 15 = 10 ∧ acceleratedOrbit 15 15737 = 28363 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15737) = 3 ^ 10 * m + 28363 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15737.1, data_15_15737.2]

/-- Complete interval computation for depth 15, residue 15738. -/
theorem bounds_15_15738 : exactInterval 15 15738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15738 : oddCount 15738 15 = 7 ∧ acceleratedOrbit 15 15738 = 1052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15738) = 3 ^ 7 * m + 1052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15738.1, data_15_15738.2]

/-- Complete interval computation for depth 15, residue 15739. -/
theorem bounds_15_15739 : exactInterval 15 15739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15739 : oddCount 15739 15 = 8 ∧ acceleratedOrbit 15 15739 = 3152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15739) = 3 ^ 8 * m + 3152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15739.1, data_15_15739.2]

/-- Complete interval computation for depth 15, residue 15740. -/
theorem bounds_15_15740 : exactInterval 15 15740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15740 : oddCount 15740 15 = 7 ∧ acceleratedOrbit 15 15740 = 1052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15740) = 3 ^ 7 * m + 1052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15740.1, data_15_15740.2]

/-- Complete interval computation for depth 15, residue 15741. -/
theorem bounds_15_15741 : exactInterval 15 15741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15741 : oddCount 15741 15 = 7 ∧ acceleratedOrbit 15 15741 = 1052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15741) = 3 ^ 7 * m + 1052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15741.1, data_15_15741.2]

/-- Complete interval computation for depth 15, residue 15742. -/
theorem bounds_15_15742 : exactInterval 15 15742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15742 : oddCount 15742 15 = 10 ∧ acceleratedOrbit 15 15742 = 28372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15742) = 3 ^ 10 * m + 28372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15742.1, data_15_15742.2]

/-- Complete interval computation for depth 15, residue 15743. -/
theorem bounds_15_15743 : exactInterval 15 15743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15743 : oddCount 15743 15 = 10 ∧ acceleratedOrbit 15 15743 = 28372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15743) = 3 ^ 10 * m + 28372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15743.1, data_15_15743.2]

/-- Complete interval computation for depth 15, residue 15744. -/
theorem bounds_15_15744 : exactInterval 15 15744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15744 : oddCount 15744 15 = 5 ∧ acceleratedOrbit 15 15744 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15744) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15744.1, data_15_15744.2]

/-- Complete interval computation for depth 15, residue 15745. -/
theorem bounds_15_15745 : exactInterval 15 15745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15745 : oddCount 15745 15 = 8 ∧ acceleratedOrbit 15 15745 = 3154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15745) = 3 ^ 8 * m + 3154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15745.1, data_15_15745.2]

/-- Complete interval computation for depth 15, residue 15746. -/
theorem bounds_15_15746 : exactInterval 15 15746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15746 : oddCount 15746 15 = 8 ∧ acceleratedOrbit 15 15746 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15746) = 3 ^ 8 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15746.1, data_15_15746.2]

/-- Complete interval computation for depth 15, residue 15747. -/
theorem bounds_15_15747 : exactInterval 15 15747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15747 : oddCount 15747 15 = 8 ∧ acceleratedOrbit 15 15747 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15747) = 3 ^ 8 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15747.1, data_15_15747.2]

/-- Complete interval computation for depth 15, residue 15748. -/
theorem bounds_15_15748 : exactInterval 15 15748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15748 : oddCount 15748 15 = 9 ∧ acceleratedOrbit 15 15748 = 9467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15748) = 3 ^ 9 * m + 9467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15748.1, data_15_15748.2]

/-- Complete interval computation for depth 15, residue 15749. -/
theorem bounds_15_15749 : exactInterval 15 15749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15749 : oddCount 15749 15 = 9 ∧ acceleratedOrbit 15 15749 = 9467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15749) = 3 ^ 9 * m + 9467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15749.1, data_15_15749.2]

/-- Complete interval computation for depth 15, residue 15750. -/
theorem bounds_15_15750 : exactInterval 15 15750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15750 : oddCount 15750 15 = 9 ∧ acceleratedOrbit 15 15750 = 9467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15750) = 3 ^ 9 * m + 9467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15750.1, data_15_15750.2]

/-- Complete interval computation for depth 15, residue 15751. -/
theorem bounds_15_15751 : exactInterval 15 15751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15751 : oddCount 15751 15 = 8 ∧ acceleratedOrbit 15 15751 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15751) = 3 ^ 8 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15751.1, data_15_15751.2]

/-- Complete interval computation for depth 15, residue 15752. -/
theorem bounds_15_15752 : exactInterval 15 15752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15752 : oddCount 15752 15 = 3 ∧ acceleratedOrbit 15 15752 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15752) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15752.1, data_15_15752.2]

/-- Complete interval computation for depth 15, residue 15753. -/
theorem bounds_15_15753 : exactInterval 15 15753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15753 : oddCount 15753 15 = 7 ∧ acceleratedOrbit 15 15753 = 1052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15753) = 3 ^ 7 * m + 1052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15753.1, data_15_15753.2]

/-- Complete interval computation for depth 15, residue 15754. -/
theorem bounds_15_15754 : exactInterval 15 15754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15754 : oddCount 15754 15 = 3 ∧ acceleratedOrbit 15 15754 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15754) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15754.1, data_15_15754.2]

/-- Complete interval computation for depth 15, residue 15755. -/
theorem bounds_15_15755 : exactInterval 15 15755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15755 : oddCount 15755 15 = 9 ∧ acceleratedOrbit 15 15755 = 9467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15755) = 3 ^ 9 * m + 9467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15755.1, data_15_15755.2]

/-- Complete interval computation for depth 15, residue 15756. -/
theorem bounds_15_15756 : exactInterval 15 15756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15756 : oddCount 15756 15 = 3 ∧ acceleratedOrbit 15 15756 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15756) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15756.1, data_15_15756.2]

/-- Complete interval computation for depth 15, residue 15757. -/
theorem bounds_15_15757 : exactInterval 15 15757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15757 : oddCount 15757 15 = 3 ∧ acceleratedOrbit 15 15757 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15757) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15757.1, data_15_15757.2]

/-- Complete interval computation for depth 15, residue 15758. -/
theorem bounds_15_15758 : exactInterval 15 15758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15758 : oddCount 15758 15 = 8 ∧ acceleratedOrbit 15 15758 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15758) = 3 ^ 8 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15758.1, data_15_15758.2]

/-- Complete interval computation for depth 15, residue 15759. -/
theorem bounds_15_15759 : exactInterval 15 15759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15759 : oddCount 15759 15 = 8 ∧ acceleratedOrbit 15 15759 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15759) = 3 ^ 8 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15759.1, data_15_15759.2]

/-- Complete interval computation for depth 15, residue 15760. -/
theorem bounds_15_15760 : exactInterval 15 15760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15760 : oddCount 15760 15 = 3 ∧ acceleratedOrbit 15 15760 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15760) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15760.1, data_15_15760.2]

end Collatz.Research.PassageAtlas.Batch0481
