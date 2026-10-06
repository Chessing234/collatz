import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0511

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16711. -/
theorem bounds_15_16711 : exactInterval 15 16711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16711 : oddCount 16711 15 = 12 ∧ acceleratedOrbit 15 16711 = 271052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16711) = 3 ^ 12 * m + 271052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16711.1, data_15_16711.2]

/-- Complete interval computation for depth 15, residue 16712. -/
theorem bounds_15_16712 : exactInterval 15 16712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16712 : oddCount 16712 15 = 8 ∧ acceleratedOrbit 15 16712 = 3349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16712) = 3 ^ 8 * m + 3349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16712.1, data_15_16712.2]

/-- Complete interval computation for depth 15, residue 16713. -/
theorem bounds_15_16713 : exactInterval 15 16713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16713 : oddCount 16713 15 = 9 ∧ acceleratedOrbit 15 16713 = 10043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16713) = 3 ^ 9 * m + 10043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16713.1, data_15_16713.2]

/-- Complete interval computation for depth 15, residue 16714. -/
theorem bounds_15_16714 : exactInterval 15 16714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16714 : oddCount 16714 15 = 8 ∧ acceleratedOrbit 15 16714 = 3349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16714) = 3 ^ 8 * m + 3349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16714.1, data_15_16714.2]

/-- Complete interval computation for depth 15, residue 16715. -/
theorem bounds_15_16715 : exactInterval 15 16715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16715 : oddCount 16715 15 = 5 ∧ acceleratedOrbit 15 16715 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16715) = 3 ^ 5 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16715.1, data_15_16715.2]

/-- Complete interval computation for depth 15, residue 16716. -/
theorem bounds_15_16716 : exactInterval 15 16716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16716 : oddCount 16716 15 = 8 ∧ acceleratedOrbit 15 16716 = 3349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16716) = 3 ^ 8 * m + 3349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16716.1, data_15_16716.2]

/-- Complete interval computation for depth 15, residue 16717. -/
theorem bounds_15_16717 : exactInterval 15 16717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16717 : oddCount 16717 15 = 8 ∧ acceleratedOrbit 15 16717 = 3349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16717) = 3 ^ 8 * m + 3349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16717.1, data_15_16717.2]

/-- Complete interval computation for depth 15, residue 16718. -/
theorem bounds_15_16718 : exactInterval 15 16718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16718 : oddCount 16718 15 = 12 ∧ acceleratedOrbit 15 16718 = 271187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16718) = 3 ^ 12 * m + 271187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16718.1, data_15_16718.2]

/-- Complete interval computation for depth 15, residue 16719. -/
theorem bounds_15_16719 : exactInterval 15 16719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16719 : oddCount 16719 15 = 12 ∧ acceleratedOrbit 15 16719 = 271187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16719) = 3 ^ 12 * m + 271187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16719.1, data_15_16719.2]

/-- Complete interval computation for depth 15, residue 16720. -/
theorem bounds_15_16720 : exactInterval 15 16720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16720 : oddCount 16720 15 = 3 ∧ acceleratedOrbit 15 16720 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16720) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16720.1, data_15_16720.2]

/-- Complete interval computation for depth 15, residue 16721. -/
theorem bounds_15_16721 : exactInterval 15 16721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16721 : oddCount 16721 15 = 8 ∧ acceleratedOrbit 15 16721 = 3349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16721) = 3 ^ 8 * m + 3349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16721.1, data_15_16721.2]

/-- Complete interval computation for depth 15, residue 16722. -/
theorem bounds_15_16722 : exactInterval 15 16722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16722 : oddCount 16722 15 = 10 ∧ acceleratedOrbit 15 16722 = 30140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16722) = 3 ^ 10 * m + 30140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16722.1, data_15_16722.2]

/-- Complete interval computation for depth 15, residue 16723. -/
theorem bounds_15_16723 : exactInterval 15 16723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16723 : oddCount 16723 15 = 10 ∧ acceleratedOrbit 15 16723 = 30140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16723) = 3 ^ 10 * m + 30140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16723.1, data_15_16723.2]

/-- Complete interval computation for depth 15, residue 16724. -/
theorem bounds_15_16724 : exactInterval 15 16724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16724 : oddCount 16724 15 = 3 ∧ acceleratedOrbit 15 16724 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16724) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16724.1, data_15_16724.2]

/-- Complete interval computation for depth 15, residue 16725. -/
theorem bounds_15_16725 : exactInterval 15 16725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16725 : oddCount 16725 15 = 3 ∧ acceleratedOrbit 15 16725 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16725) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16725.1, data_15_16725.2]

/-- Complete interval computation for depth 15, residue 16726. -/
theorem bounds_15_16726 : exactInterval 15 16726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16726 : oddCount 16726 15 = 7 ∧ acceleratedOrbit 15 16726 = 1117 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16726) = 3 ^ 7 * m + 1117 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16726.1, data_15_16726.2]

/-- Complete interval computation for depth 15, residue 16727. -/
theorem bounds_15_16727 : exactInterval 15 16727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16727 : oddCount 16727 15 = 7 ∧ acceleratedOrbit 15 16727 = 1117 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16727) = 3 ^ 7 * m + 1117 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16727.1, data_15_16727.2]

/-- Complete interval computation for depth 15, residue 16728. -/
theorem bounds_15_16728 : exactInterval 15 16728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16728 : oddCount 16728 15 = 6 ∧ acceleratedOrbit 15 16728 = 373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16728) = 3 ^ 6 * m + 373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16728.1, data_15_16728.2]

/-- Complete interval computation for depth 15, residue 16729. -/
theorem bounds_15_16729 : exactInterval 15 16729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16729 : oddCount 16729 15 = 7 ∧ acceleratedOrbit 15 16729 = 1117 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16729) = 3 ^ 7 * m + 1117 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16729.1, data_15_16729.2]

/-- Complete interval computation for depth 15, residue 16730. -/
theorem bounds_15_16730 : exactInterval 15 16730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16730 : oddCount 16730 15 = 6 ∧ acceleratedOrbit 15 16730 = 373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16730) = 3 ^ 6 * m + 373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16730.1, data_15_16730.2]

/-- Complete interval computation for depth 15, residue 16731. -/
theorem bounds_15_16731 : exactInterval 15 16731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16731 : oddCount 16731 15 = 7 ∧ acceleratedOrbit 15 16731 = 1117 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16731) = 3 ^ 7 * m + 1117 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16731.1, data_15_16731.2]

/-- Complete interval computation for depth 15, residue 16732. -/
theorem bounds_15_16732 : exactInterval 15 16732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16732 : oddCount 16732 15 = 6 ∧ acceleratedOrbit 15 16732 = 373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16732) = 3 ^ 6 * m + 373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16732.1, data_15_16732.2]

/-- Complete interval computation for depth 15, residue 16733. -/
theorem bounds_15_16733 : exactInterval 15 16733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16733 : oddCount 16733 15 = 6 ∧ acceleratedOrbit 15 16733 = 373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16733) = 3 ^ 6 * m + 373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16733.1, data_15_16733.2]

/-- Complete interval computation for depth 15, residue 16734. -/
theorem bounds_15_16734 : exactInterval 15 16734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16734 : oddCount 16734 15 = 9 ∧ acceleratedOrbit 15 16734 = 10054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16734) = 3 ^ 9 * m + 10054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16734.1, data_15_16734.2]

/-- Complete interval computation for depth 15, residue 16735. -/
theorem bounds_15_16735 : exactInterval 15 16735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16735 : oddCount 16735 15 = 9 ∧ acceleratedOrbit 15 16735 = 10054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16735) = 3 ^ 9 * m + 10054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16735.1, data_15_16735.2]

/-- Complete interval computation for depth 15, residue 16736. -/
theorem bounds_15_16736 : exactInterval 15 16736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16736 : oddCount 16736 15 = 5 ∧ acceleratedOrbit 15 16736 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16736) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16736.1, data_15_16736.2]

/-- Complete interval computation for depth 15, residue 16737. -/
theorem bounds_15_16737 : exactInterval 15 16737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16737 : oddCount 16737 15 = 8 ∧ acceleratedOrbit 15 16737 = 3352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16737) = 3 ^ 8 * m + 3352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16737.1, data_15_16737.2]

/-- Complete interval computation for depth 15, residue 16738. -/
theorem bounds_15_16738 : exactInterval 15 16738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16738 : oddCount 16738 15 = 6 ∧ acceleratedOrbit 15 16738 = 373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16738) = 3 ^ 6 * m + 373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16738.1, data_15_16738.2]

/-- Complete interval computation for depth 15, residue 16739. -/
theorem bounds_15_16739 : exactInterval 15 16739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16739 : oddCount 16739 15 = 6 ∧ acceleratedOrbit 15 16739 = 373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16739) = 3 ^ 6 * m + 373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16739.1, data_15_16739.2]

/-- Complete interval computation for depth 15, residue 16740. -/
theorem bounds_15_16740 : exactInterval 15 16740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16740 : oddCount 16740 15 = 6 ∧ acceleratedOrbit 15 16740 = 373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16740) = 3 ^ 6 * m + 373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16740.1, data_15_16740.2]

/-- Complete interval computation for depth 15, residue 16741. -/
theorem bounds_15_16741 : exactInterval 15 16741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16741 : oddCount 16741 15 = 6 ∧ acceleratedOrbit 15 16741 = 373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16741) = 3 ^ 6 * m + 373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16741.1, data_15_16741.2]

/-- Complete interval computation for depth 15, residue 16742. -/
theorem bounds_15_16742 : exactInterval 15 16742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16742 : oddCount 16742 15 = 6 ∧ acceleratedOrbit 15 16742 = 373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16742) = 3 ^ 6 * m + 373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16742.1, data_15_16742.2]

/-- Complete interval computation for depth 15, residue 16743. -/
theorem bounds_15_16743 : exactInterval 15 16743 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16743) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16743 : oddCount 16743 15 = 9 ∧ acceleratedOrbit 15 16743 = 10058 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16743) = 3 ^ 9 * m + 10058 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16743.1, data_15_16743.2]

end Collatz.Research.PassageAtlas.Batch0511
