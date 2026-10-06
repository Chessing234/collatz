import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0114

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 711. -/
theorem bounds_11_711 : exactInterval 11 711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_711 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 711) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_711 : oddCount 711 11 = 6 ∧ acceleratedOrbit 11 711 = 254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_711 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 711) = 3 ^ 6 * m + 254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_711.1, data_11_711.2]

/-- Complete interval computation for depth 11, residue 712. -/
theorem bounds_11_712 : exactInterval 11 712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_712 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 712) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_712 : oddCount 712 11 = 4 ∧ acceleratedOrbit 11 712 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_712 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 712) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_712.1, data_11_712.2]

/-- Complete interval computation for depth 11, residue 713. -/
theorem bounds_11_713 : exactInterval 11 713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_713 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 713) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_713 : oddCount 713 11 = 5 ∧ acceleratedOrbit 11 713 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_713 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 713) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_713.1, data_11_713.2]

/-- Complete interval computation for depth 11, residue 714. -/
theorem bounds_11_714 : exactInterval 11 714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_714 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 714) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_714 : oddCount 714 11 = 4 ∧ acceleratedOrbit 11 714 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_714 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 714) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_714.1, data_11_714.2]

/-- Complete interval computation for depth 11, residue 715. -/
theorem bounds_11_715 : exactInterval 11 715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_715 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 715) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_715 : oddCount 715 11 = 6 ∧ acceleratedOrbit 11 715 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_715 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 715) = 3 ^ 6 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_715.1, data_11_715.2]

/-- Complete interval computation for depth 11, residue 716. -/
theorem bounds_11_716 : exactInterval 11 716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_716 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 716) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_716 : oddCount 716 11 = 4 ∧ acceleratedOrbit 11 716 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_716 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 716) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_716.1, data_11_716.2]

/-- Complete interval computation for depth 11, residue 717. -/
theorem bounds_11_717 : exactInterval 11 717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_717 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 717) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_717 : oddCount 717 11 = 4 ∧ acceleratedOrbit 11 717 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_717 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 717) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_717.1, data_11_717.2]

/-- Complete interval computation for depth 11, residue 718. -/
theorem bounds_11_718 : exactInterval 11 718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_718 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 718) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_718 : oddCount 718 11 = 8 ∧ acceleratedOrbit 11 718 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_718 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 718) = 3 ^ 8 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_718.1, data_11_718.2]

/-- Complete interval computation for depth 11, residue 719. -/
theorem bounds_11_719 : exactInterval 11 719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_719 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 719) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_719 : oddCount 719 11 = 8 ∧ acceleratedOrbit 11 719 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_719 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 719) = 3 ^ 8 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_719.1, data_11_719.2]

/-- Complete interval computation for depth 11, residue 720. -/
theorem bounds_11_720 : exactInterval 11 720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_720 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 720) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_720 : oddCount 720 11 = 3 ∧ acceleratedOrbit 11 720 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_720 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 720) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_720.1, data_11_720.2]

/-- Complete interval computation for depth 11, residue 721. -/
theorem bounds_11_721 : exactInterval 11 721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_721 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 721) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_721 : oddCount 721 11 = 5 ∧ acceleratedOrbit 11 721 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_721 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 721) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_721.1, data_11_721.2]

/-- Complete interval computation for depth 11, residue 722. -/
theorem bounds_11_722 : exactInterval 11 722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_722 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 722) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_722 : oddCount 722 11 = 5 ∧ acceleratedOrbit 11 722 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_722 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 722) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_722.1, data_11_722.2]

/-- Complete interval computation for depth 11, residue 723. -/
theorem bounds_11_723 : exactInterval 11 723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_723 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 723) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_723 : oddCount 723 11 = 5 ∧ acceleratedOrbit 11 723 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_723 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 723) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_723.1, data_11_723.2]

/-- Complete interval computation for depth 11, residue 724. -/
theorem bounds_11_724 : exactInterval 11 724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_724 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 724) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_724 : oddCount 724 11 = 3 ∧ acceleratedOrbit 11 724 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_724 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 724) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_724.1, data_11_724.2]

/-- Complete interval computation for depth 11, residue 725. -/
theorem bounds_11_725 : exactInterval 11 725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_725 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 725) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_725 : oddCount 725 11 = 3 ∧ acceleratedOrbit 11 725 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_725 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 725) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_725.1, data_11_725.2]

/-- Complete interval computation for depth 11, residue 726. -/
theorem bounds_11_726 : exactInterval 11 726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_726 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 726) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_726 : oddCount 726 11 = 6 ∧ acceleratedOrbit 11 726 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_726 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 726) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_726.1, data_11_726.2]

end Collatz.Research.StoppingAtlas.Batch0114
