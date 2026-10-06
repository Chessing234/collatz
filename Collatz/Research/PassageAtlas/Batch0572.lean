import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0572

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18710. -/
theorem bounds_15_18710 : exactInterval 15 18710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18710 : oddCount 18710 15 = 8 ∧ acceleratedOrbit 15 18710 = 3748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18710) = 3 ^ 8 * m + 3748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18710.1, data_15_18710.2]

/-- Complete interval computation for depth 15, residue 18711. -/
theorem bounds_15_18711 : exactInterval 15 18711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18711 : oddCount 18711 15 = 8 ∧ acceleratedOrbit 15 18711 = 3748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18711) = 3 ^ 8 * m + 3748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18711.1, data_15_18711.2]

/-- Complete interval computation for depth 15, residue 18712. -/
theorem bounds_15_18712 : exactInterval 15 18712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18712 : oddCount 18712 15 = 6 ∧ acceleratedOrbit 15 18712 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18712) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18712.1, data_15_18712.2]

/-- Complete interval computation for depth 15, residue 18713. -/
theorem bounds_15_18713 : exactInterval 15 18713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18713 : oddCount 18713 15 = 8 ∧ acceleratedOrbit 15 18713 = 3748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18713) = 3 ^ 8 * m + 3748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18713.1, data_15_18713.2]

/-- Complete interval computation for depth 15, residue 18714. -/
theorem bounds_15_18714 : exactInterval 15 18714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18714 : oddCount 18714 15 = 6 ∧ acceleratedOrbit 15 18714 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18714) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18714.1, data_15_18714.2]

/-- Complete interval computation for depth 15, residue 18715. -/
theorem bounds_15_18715 : exactInterval 15 18715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18715 : oddCount 18715 15 = 9 ∧ acceleratedOrbit 15 18715 = 11243 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18715) = 3 ^ 9 * m + 11243 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18715.1, data_15_18715.2]

/-- Complete interval computation for depth 15, residue 18716. -/
theorem bounds_15_18716 : exactInterval 15 18716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18716 : oddCount 18716 15 = 7 ∧ acceleratedOrbit 15 18716 = 1250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18716) = 3 ^ 7 * m + 1250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18716.1, data_15_18716.2]

/-- Complete interval computation for depth 15, residue 18717. -/
theorem bounds_15_18717 : exactInterval 15 18717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18717 : oddCount 18717 15 = 7 ∧ acceleratedOrbit 15 18717 = 1250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18717) = 3 ^ 7 * m + 1250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18717.1, data_15_18717.2]

/-- Complete interval computation for depth 15, residue 18718. -/
theorem bounds_15_18718 : exactInterval 15 18718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18718 : oddCount 18718 15 = 7 ∧ acceleratedOrbit 15 18718 = 1250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18718) = 3 ^ 7 * m + 1250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18718.1, data_15_18718.2]

/-- Complete interval computation for depth 15, residue 18719. -/
theorem bounds_15_18719 : exactInterval 15 18719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18719 : oddCount 18719 15 = 10 ∧ acceleratedOrbit 15 18719 = 33736 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18719) = 3 ^ 10 * m + 33736 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18719.1, data_15_18719.2]

/-- Complete interval computation for depth 15, residue 18720. -/
theorem bounds_15_18720 : exactInterval 15 18720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18720 : oddCount 18720 15 = 6 ∧ acceleratedOrbit 15 18720 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18720) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18720.1, data_15_18720.2]

/-- Complete interval computation for depth 15, residue 18721. -/
theorem bounds_15_18721 : exactInterval 15 18721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18721 : oddCount 18721 15 = 8 ∧ acceleratedOrbit 15 18721 = 3752 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18721) = 3 ^ 8 * m + 3752 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18721.1, data_15_18721.2]

/-- Complete interval computation for depth 15, residue 18722. -/
theorem bounds_15_18722 : exactInterval 15 18722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18722 : oddCount 18722 15 = 8 ∧ acceleratedOrbit 15 18722 = 3752 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18722) = 3 ^ 8 * m + 3752 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18722.1, data_15_18722.2]

/-- Complete interval computation for depth 15, residue 18723. -/
theorem bounds_15_18723 : exactInterval 15 18723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18723 : oddCount 18723 15 = 8 ∧ acceleratedOrbit 15 18723 = 3752 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18723) = 3 ^ 8 * m + 3752 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18723.1, data_15_18723.2]

/-- Complete interval computation for depth 15, residue 18724. -/
theorem bounds_15_18724 : exactInterval 15 18724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18724 : oddCount 18724 15 = 8 ∧ acceleratedOrbit 15 18724 = 3752 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18724) = 3 ^ 8 * m + 3752 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18724.1, data_15_18724.2]

/-- Complete interval computation for depth 15, residue 18725. -/
theorem bounds_15_18725 : exactInterval 15 18725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18725 : oddCount 18725 15 = 8 ∧ acceleratedOrbit 15 18725 = 3752 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18725) = 3 ^ 8 * m + 3752 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18725.1, data_15_18725.2]

/-- Complete interval computation for depth 15, residue 18726. -/
theorem bounds_15_18726 : exactInterval 15 18726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18726 : oddCount 18726 15 = 8 ∧ acceleratedOrbit 15 18726 = 3752 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18726) = 3 ^ 8 * m + 3752 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18726.1, data_15_18726.2]

/-- Complete interval computation for depth 15, residue 18727. -/
theorem bounds_15_18727 : exactInterval 15 18727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18727 : oddCount 18727 15 = 7 ∧ acceleratedOrbit 15 18727 = 1250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18727) = 3 ^ 7 * m + 1250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18727.1, data_15_18727.2]

/-- Complete interval computation for depth 15, residue 18728. -/
theorem bounds_15_18728 : exactInterval 15 18728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18728 : oddCount 18728 15 = 6 ∧ acceleratedOrbit 15 18728 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18728) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18728.1, data_15_18728.2]

/-- Complete interval computation for depth 15, residue 18729. -/
theorem bounds_15_18729 : exactInterval 15 18729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18729 : oddCount 18729 15 = 9 ∧ acceleratedOrbit 15 18729 = 11252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18729) = 3 ^ 9 * m + 11252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18729.1, data_15_18729.2]

/-- Complete interval computation for depth 15, residue 18730. -/
theorem bounds_15_18730 : exactInterval 15 18730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18730 : oddCount 18730 15 = 6 ∧ acceleratedOrbit 15 18730 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18730) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18730.1, data_15_18730.2]

/-- Complete interval computation for depth 15, residue 18731. -/
theorem bounds_15_18731 : exactInterval 15 18731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18731 : oddCount 18731 15 = 9 ∧ acceleratedOrbit 15 18731 = 11254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18731) = 3 ^ 9 * m + 11254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18731.1, data_15_18731.2]

/-- Complete interval computation for depth 15, residue 18732. -/
theorem bounds_15_18732 : exactInterval 15 18732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18732 : oddCount 18732 15 = 6 ∧ acceleratedOrbit 15 18732 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18732) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18732.1, data_15_18732.2]

/-- Complete interval computation for depth 15, residue 18733. -/
theorem bounds_15_18733 : exactInterval 15 18733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18733 : oddCount 18733 15 = 6 ∧ acceleratedOrbit 15 18733 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18733) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18733.1, data_15_18733.2]

/-- Complete interval computation for depth 15, residue 18734. -/
theorem bounds_15_18734 : exactInterval 15 18734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18734 : oddCount 18734 15 = 6 ∧ acceleratedOrbit 15 18734 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18734) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18734.1, data_15_18734.2]

/-- Complete interval computation for depth 15, residue 18735. -/
theorem bounds_15_18735 : exactInterval 15 18735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18735 : oddCount 18735 15 = 8 ∧ acceleratedOrbit 15 18735 = 3752 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18735) = 3 ^ 8 * m + 3752 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18735.1, data_15_18735.2]

/-- Complete interval computation for depth 15, residue 18736. -/
theorem bounds_15_18736 : exactInterval 15 18736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18736 : oddCount 18736 15 = 6 ∧ acceleratedOrbit 15 18736 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18736) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18736.1, data_15_18736.2]

/-- Complete interval computation for depth 15, residue 18737. -/
theorem bounds_15_18737 : exactInterval 15 18737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18737 : oddCount 18737 15 = 5 ∧ acceleratedOrbit 15 18737 = 139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18737) = 3 ^ 5 * m + 139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18737.1, data_15_18737.2]

/-- Complete interval computation for depth 15, residue 18738. -/
theorem bounds_15_18738 : exactInterval 15 18738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18738 : oddCount 18738 15 = 5 ∧ acceleratedOrbit 15 18738 = 139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18738) = 3 ^ 5 * m + 139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18738.1, data_15_18738.2]

/-- Complete interval computation for depth 15, residue 18739. -/
theorem bounds_15_18739 : exactInterval 15 18739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18739 : oddCount 18739 15 = 5 ∧ acceleratedOrbit 15 18739 = 139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18739) = 3 ^ 5 * m + 139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18739.1, data_15_18739.2]

/-- Complete interval computation for depth 15, residue 18740. -/
theorem bounds_15_18740 : exactInterval 15 18740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18740 : oddCount 18740 15 = 6 ∧ acceleratedOrbit 15 18740 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18740) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18740.1, data_15_18740.2]

/-- Complete interval computation for depth 15, residue 18741. -/
theorem bounds_15_18741 : exactInterval 15 18741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18741 : oddCount 18741 15 = 6 ∧ acceleratedOrbit 15 18741 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18741) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18741.1, data_15_18741.2]

/-- Complete interval computation for depth 15, residue 18742. -/
theorem bounds_15_18742 : exactInterval 15 18742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18742 : oddCount 18742 15 = 9 ∧ acceleratedOrbit 15 18742 = 11260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18742) = 3 ^ 9 * m + 11260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18742.1, data_15_18742.2]

end Collatz.Research.PassageAtlas.Batch0572
