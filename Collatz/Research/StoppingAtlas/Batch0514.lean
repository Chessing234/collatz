import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0514

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 711. -/
theorem bounds_13_711 : exactInterval 13 711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_711 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 711) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_711 : oddCount 711 13 = 7 ∧ acceleratedOrbit 13 711 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_711 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 711) = 3 ^ 7 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_711.1, data_13_711.2]

/-- Complete interval computation for depth 13, residue 712. -/
theorem bounds_13_712 : exactInterval 13 712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_712 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 712) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_712 : oddCount 712 13 = 5 ∧ acceleratedOrbit 13 712 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_712 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 712) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_712.1, data_13_712.2]

/-- Complete interval computation for depth 13, residue 713. -/
theorem bounds_13_713 : exactInterval 13 713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_713 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 713) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_713 : oddCount 713 13 = 6 ∧ acceleratedOrbit 13 713 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_713 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 713) = 3 ^ 6 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_713.1, data_13_713.2]

/-- Complete interval computation for depth 13, residue 714. -/
theorem bounds_13_714 : exactInterval 13 714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_714 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 714) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_714 : oddCount 714 13 = 5 ∧ acceleratedOrbit 13 714 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_714 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 714) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_714.1, data_13_714.2]

/-- Complete interval computation for depth 13, residue 715. -/
theorem bounds_13_715 : exactInterval 13 715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_715 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 715) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_715 : oddCount 715 13 = 6 ∧ acceleratedOrbit 13 715 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_715 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 715) = 3 ^ 6 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_715.1, data_13_715.2]

/-- Complete interval computation for depth 13, residue 716. -/
theorem bounds_13_716 : exactInterval 13 716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_716 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 716) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_716 : oddCount 716 13 = 5 ∧ acceleratedOrbit 13 716 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_716 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 716) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_716.1, data_13_716.2]

/-- Complete interval computation for depth 13, residue 717. -/
theorem bounds_13_717 : exactInterval 13 717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_717 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 717) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_717 : oddCount 717 13 = 5 ∧ acceleratedOrbit 13 717 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_717 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 717) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_717.1, data_13_717.2]

/-- Complete interval computation for depth 13, residue 718. -/
theorem bounds_13_718 : exactInterval 13 718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_718 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 718) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_718 : oddCount 718 13 = 8 ∧ acceleratedOrbit 13 718 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_718 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 718) = 3 ^ 8 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_718.1, data_13_718.2]

/-- Complete interval computation for depth 13, residue 719. -/
theorem bounds_13_719 : exactInterval 13 719 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_719 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 719) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_719 : oddCount 719 13 = 8 ∧ acceleratedOrbit 13 719 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_719 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 719) = 3 ^ 8 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_719.1, data_13_719.2]

/-- Complete interval computation for depth 13, residue 720. -/
theorem bounds_13_720 : exactInterval 13 720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_720 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 720) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_720 : oddCount 720 13 = 4 ∧ acceleratedOrbit 13 720 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_720 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 720) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_720.1, data_13_720.2]

/-- Complete interval computation for depth 13, residue 721. -/
theorem bounds_13_721 : exactInterval 13 721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_721 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 721) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_721 : oddCount 721 13 = 6 ∧ acceleratedOrbit 13 721 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_721 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 721) = 3 ^ 6 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_721.1, data_13_721.2]

/-- Complete interval computation for depth 13, residue 722. -/
theorem bounds_13_722 : exactInterval 13 722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_722 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 722) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_722 : oddCount 722 13 = 6 ∧ acceleratedOrbit 13 722 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_722 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 722) = 3 ^ 6 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_722.1, data_13_722.2]

/-- Complete interval computation for depth 13, residue 723. -/
theorem bounds_13_723 : exactInterval 13 723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_723 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 723) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_723 : oddCount 723 13 = 6 ∧ acceleratedOrbit 13 723 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_723 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 723) = 3 ^ 6 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_723.1, data_13_723.2]

/-- Complete interval computation for depth 13, residue 724. -/
theorem bounds_13_724 : exactInterval 13 724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_724 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 724) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_724 : oddCount 724 13 = 4 ∧ acceleratedOrbit 13 724 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_724 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 724) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_724.1, data_13_724.2]

/-- Complete interval computation for depth 13, residue 725. -/
theorem bounds_13_725 : exactInterval 13 725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_725 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 725) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_725 : oddCount 725 13 = 4 ∧ acceleratedOrbit 13 725 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_725 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 725) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_725.1, data_13_725.2]

/-- Complete interval computation for depth 13, residue 726. -/
theorem bounds_13_726 : exactInterval 13 726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_726 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 726) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_726 : oddCount 726 13 = 6 ∧ acceleratedOrbit 13 726 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_726 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 726) = 3 ^ 6 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_726.1, data_13_726.2]

end Collatz.Research.StoppingAtlas.Batch0514
