import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0969

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31719. -/
theorem bounds_15_31719 : exactInterval 15 31719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31719 : oddCount 31719 15 = 9 ∧ acceleratedOrbit 15 31719 = 19055 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31719) = 3 ^ 9 * m + 19055 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31719.1, data_15_31719.2]

/-- Complete interval computation for depth 15, residue 31720. -/
theorem bounds_15_31720 : exactInterval 15 31720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31720 : oddCount 31720 15 = 7 ∧ acceleratedOrbit 15 31720 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31720) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31720.1, data_15_31720.2]

/-- Complete interval computation for depth 15, residue 31721. -/
theorem bounds_15_31721 : exactInterval 15 31721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31721 : oddCount 31721 15 = 11 ∧ acceleratedOrbit 15 31721 = 171497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31721) = 3 ^ 11 * m + 171497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31721.1, data_15_31721.2]

/-- Complete interval computation for depth 15, residue 31722. -/
theorem bounds_15_31722 : exactInterval 15 31722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31722 : oddCount 31722 15 = 7 ∧ acceleratedOrbit 15 31722 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31722) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31722.1, data_15_31722.2]

/-- Complete interval computation for depth 15, residue 31723. -/
theorem bounds_15_31723 : exactInterval 15 31723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31723 : oddCount 31723 15 = 9 ∧ acceleratedOrbit 15 31723 = 19057 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31723) = 3 ^ 9 * m + 19057 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31723.1, data_15_31723.2]

/-- Complete interval computation for depth 15, residue 31724. -/
theorem bounds_15_31724 : exactInterval 15 31724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31724 : oddCount 31724 15 = 9 ∧ acceleratedOrbit 15 31724 = 19061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31724) = 3 ^ 9 * m + 19061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31724.1, data_15_31724.2]

/-- Complete interval computation for depth 15, residue 31725. -/
theorem bounds_15_31725 : exactInterval 15 31725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31725 : oddCount 31725 15 = 9 ∧ acceleratedOrbit 15 31725 = 19061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31725) = 3 ^ 9 * m + 19061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31725.1, data_15_31725.2]

/-- Complete interval computation for depth 15, residue 31726. -/
theorem bounds_15_31726 : exactInterval 15 31726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31726 : oddCount 31726 15 = 9 ∧ acceleratedOrbit 15 31726 = 19061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31726) = 3 ^ 9 * m + 19061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31726.1, data_15_31726.2]

/-- Complete interval computation for depth 15, residue 31727. -/
theorem bounds_15_31727 : exactInterval 15 31727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31727 : oddCount 31727 15 = 10 ∧ acceleratedOrbit 15 31727 = 57176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31727) = 3 ^ 10 * m + 57176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31727.1, data_15_31727.2]

/-- Complete interval computation for depth 15, residue 31728. -/
theorem bounds_15_31728 : exactInterval 15 31728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31728 : oddCount 31728 15 = 8 ∧ acceleratedOrbit 15 31728 = 6356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31728) = 3 ^ 8 * m + 6356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31728.1, data_15_31728.2]

/-- Complete interval computation for depth 15, residue 31729. -/
theorem bounds_15_31729 : exactInterval 15 31729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31729 : oddCount 31729 15 = 7 ∧ acceleratedOrbit 15 31729 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31729) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31729.1, data_15_31729.2]

/-- Complete interval computation for depth 15, residue 31730. -/
theorem bounds_15_31730 : exactInterval 15 31730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31730 : oddCount 31730 15 = 6 ∧ acceleratedOrbit 15 31730 = 706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31730) = 3 ^ 6 * m + 706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31730.1, data_15_31730.2]

/-- Complete interval computation for depth 15, residue 31731. -/
theorem bounds_15_31731 : exactInterval 15 31731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31731 : oddCount 31731 15 = 6 ∧ acceleratedOrbit 15 31731 = 706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31731) = 3 ^ 6 * m + 706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31731.1, data_15_31731.2]

/-- Complete interval computation for depth 15, residue 31732. -/
theorem bounds_15_31732 : exactInterval 15 31732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31732 : oddCount 31732 15 = 8 ∧ acceleratedOrbit 15 31732 = 6356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31732) = 3 ^ 8 * m + 6356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31732.1, data_15_31732.2]

/-- Complete interval computation for depth 15, residue 31733. -/
theorem bounds_15_31733 : exactInterval 15 31733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31733 : oddCount 31733 15 = 8 ∧ acceleratedOrbit 15 31733 = 6356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31733) = 3 ^ 8 * m + 6356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31733.1, data_15_31733.2]

/-- Complete interval computation for depth 15, residue 31734. -/
theorem bounds_15_31734 : exactInterval 15 31734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31734 : oddCount 31734 15 = 8 ∧ acceleratedOrbit 15 31734 = 6355 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31734) = 3 ^ 8 * m + 6355 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31734.1, data_15_31734.2]

/-- Complete interval computation for depth 15, residue 31735. -/
theorem bounds_15_31735 : exactInterval 15 31735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31735 : oddCount 31735 15 = 8 ∧ acceleratedOrbit 15 31735 = 6355 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31735) = 3 ^ 8 * m + 6355 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31735.1, data_15_31735.2]

/-- Complete interval computation for depth 15, residue 31736. -/
theorem bounds_15_31736 : exactInterval 15 31736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31736 : oddCount 31736 15 = 8 ∧ acceleratedOrbit 15 31736 = 6356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31736) = 3 ^ 8 * m + 6356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31736.1, data_15_31736.2]

/-- Complete interval computation for depth 15, residue 31737. -/
theorem bounds_15_31737 : exactInterval 15 31737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31737 : oddCount 31737 15 = 10 ∧ acceleratedOrbit 15 31737 = 57196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31737) = 3 ^ 10 * m + 57196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31737.1, data_15_31737.2]

/-- Complete interval computation for depth 15, residue 31738. -/
theorem bounds_15_31738 : exactInterval 15 31738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31738 : oddCount 31738 15 = 8 ∧ acceleratedOrbit 15 31738 = 6356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31738) = 3 ^ 8 * m + 6356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31738.1, data_15_31738.2]

/-- Complete interval computation for depth 15, residue 31739. -/
theorem bounds_15_31739 : exactInterval 15 31739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31739 : oddCount 31739 15 = 10 ∧ acceleratedOrbit 15 31739 = 57199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31739) = 3 ^ 10 * m + 57199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31739.1, data_15_31739.2]

/-- Complete interval computation for depth 15, residue 31740. -/
theorem bounds_15_31740 : exactInterval 15 31740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31740 : oddCount 31740 15 = 12 ∧ acceleratedOrbit 15 31740 = 514835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31740) = 3 ^ 12 * m + 514835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31740.1, data_15_31740.2]

/-- Complete interval computation for depth 15, residue 31741. -/
theorem bounds_15_31741 : exactInterval 15 31741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31741 : oddCount 31741 15 = 12 ∧ acceleratedOrbit 15 31741 = 514835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31741) = 3 ^ 12 * m + 514835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31741.1, data_15_31741.2]

/-- Complete interval computation for depth 15, residue 31742. -/
theorem bounds_15_31742 : exactInterval 15 31742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31742 : oddCount 31742 15 = 12 ∧ acceleratedOrbit 15 31742 = 514835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31742) = 3 ^ 12 * m + 514835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31742.1, data_15_31742.2]

/-- Complete interval computation for depth 15, residue 31743. -/
theorem bounds_15_31743 : exactInterval 15 31743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31743 : oddCount 31743 15 = 13 ∧ acceleratedOrbit 15 31743 = 1544501 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31743) = 3 ^ 13 * m + 1544501 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31743.1, data_15_31743.2]

/-- Complete interval computation for depth 15, residue 31744. -/
theorem bounds_15_31744 : exactInterval 15 31744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31744 : oddCount 31744 15 = 5 ∧ acceleratedOrbit 15 31744 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31744) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31744.1, data_15_31744.2]

/-- Complete interval computation for depth 15, residue 31745. -/
theorem bounds_15_31745 : exactInterval 15 31745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31745 : oddCount 31745 15 = 8 ∧ acceleratedOrbit 15 31745 = 6358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31745) = 3 ^ 8 * m + 6358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31745.1, data_15_31745.2]

/-- Complete interval computation for depth 15, residue 31746. -/
theorem bounds_15_31746 : exactInterval 15 31746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31746 : oddCount 31746 15 = 9 ∧ acceleratedOrbit 15 31746 = 19075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31746) = 3 ^ 9 * m + 19075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31746.1, data_15_31746.2]

/-- Complete interval computation for depth 15, residue 31747. -/
theorem bounds_15_31747 : exactInterval 15 31747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31747 : oddCount 31747 15 = 9 ∧ acceleratedOrbit 15 31747 = 19075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31747) = 3 ^ 9 * m + 19075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31747.1, data_15_31747.2]

/-- Complete interval computation for depth 15, residue 31748. -/
theorem bounds_15_31748 : exactInterval 15 31748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31748 : oddCount 31748 15 = 5 ∧ acceleratedOrbit 15 31748 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31748) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31748.1, data_15_31748.2]

/-- Complete interval computation for depth 15, residue 31749. -/
theorem bounds_15_31749 : exactInterval 15 31749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31749 : oddCount 31749 15 = 5 ∧ acceleratedOrbit 15 31749 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31749) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31749.1, data_15_31749.2]

/-- Complete interval computation for depth 15, residue 31750. -/
theorem bounds_15_31750 : exactInterval 15 31750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31750 : oddCount 31750 15 = 5 ∧ acceleratedOrbit 15 31750 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31750) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31750.1, data_15_31750.2]

/-- Complete interval computation for depth 15, residue 31751. -/
theorem bounds_15_31751 : exactInterval 15 31751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31751 : oddCount 31751 15 = 9 ∧ acceleratedOrbit 15 31751 = 19075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31751) = 3 ^ 9 * m + 19075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31751.1, data_15_31751.2]

end Collatz.Research.PassageAtlas.Batch0969
