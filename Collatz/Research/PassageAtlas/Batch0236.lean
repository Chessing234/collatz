import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0236

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7700. -/
theorem bounds_15_7700 : exactInterval 15 7700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7700 : oddCount 7700 15 = 6 ∧ acceleratedOrbit 15 7700 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7700) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7700.1, data_15_7700.2]

/-- Complete interval computation for depth 15, residue 7701. -/
theorem bounds_15_7701 : exactInterval 15 7701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7701 : oddCount 7701 15 = 6 ∧ acceleratedOrbit 15 7701 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7701) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7701.1, data_15_7701.2]

/-- Complete interval computation for depth 15, residue 7702. -/
theorem bounds_15_7702 : exactInterval 15 7702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7702 : oddCount 7702 15 = 7 ∧ acceleratedOrbit 15 7702 = 515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7702) = 3 ^ 7 * m + 515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7702.1, data_15_7702.2]

/-- Complete interval computation for depth 15, residue 7703. -/
theorem bounds_15_7703 : exactInterval 15 7703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7703 : oddCount 7703 15 = 7 ∧ acceleratedOrbit 15 7703 = 515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7703) = 3 ^ 7 * m + 515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7703.1, data_15_7703.2]

/-- Complete interval computation for depth 15, residue 7704. -/
theorem bounds_15_7704 : exactInterval 15 7704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7704 : oddCount 7704 15 = 6 ∧ acceleratedOrbit 15 7704 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7704) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7704.1, data_15_7704.2]

/-- Complete interval computation for depth 15, residue 7705. -/
theorem bounds_15_7705 : exactInterval 15 7705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7705 : oddCount 7705 15 = 7 ∧ acceleratedOrbit 15 7705 = 515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7705) = 3 ^ 7 * m + 515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7705.1, data_15_7705.2]

/-- Complete interval computation for depth 15, residue 7706. -/
theorem bounds_15_7706 : exactInterval 15 7706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7706 : oddCount 7706 15 = 6 ∧ acceleratedOrbit 15 7706 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7706) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7706.1, data_15_7706.2]

/-- Complete interval computation for depth 15, residue 7707. -/
theorem bounds_15_7707 : exactInterval 15 7707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7707 : oddCount 7707 15 = 11 ∧ acceleratedOrbit 15 7707 = 41674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7707) = 3 ^ 11 * m + 41674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7707.1, data_15_7707.2]

/-- Complete interval computation for depth 15, residue 7708. -/
theorem bounds_15_7708 : exactInterval 15 7708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7708 : oddCount 7708 15 = 6 ∧ acceleratedOrbit 15 7708 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7708) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7708.1, data_15_7708.2]

/-- Complete interval computation for depth 15, residue 7709. -/
theorem bounds_15_7709 : exactInterval 15 7709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7709 : oddCount 7709 15 = 6 ∧ acceleratedOrbit 15 7709 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7709) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7709.1, data_15_7709.2]

/-- Complete interval computation for depth 15, residue 7710. -/
theorem bounds_15_7710 : exactInterval 15 7710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7710 : oddCount 7710 15 = 6 ∧ acceleratedOrbit 15 7710 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7710) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7710.1, data_15_7710.2]

/-- Complete interval computation for depth 15, residue 7711. -/
theorem bounds_15_7711 : exactInterval 15 7711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7711 : oddCount 7711 15 = 10 ∧ acceleratedOrbit 15 7711 = 13898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7711) = 3 ^ 10 * m + 13898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7711.1, data_15_7711.2]

/-- Complete interval computation for depth 15, residue 7712. -/
theorem bounds_15_7712 : exactInterval 15 7712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7712 : oddCount 7712 15 = 4 ∧ acceleratedOrbit 15 7712 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7712) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7712.1, data_15_7712.2]

/-- Complete interval computation for depth 15, residue 7713. -/
theorem bounds_15_7713 : exactInterval 15 7713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7713 : oddCount 7713 15 = 9 ∧ acceleratedOrbit 15 7713 = 4637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7713) = 3 ^ 9 * m + 4637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7713.1, data_15_7713.2]

/-- Complete interval computation for depth 15, residue 7714. -/
theorem bounds_15_7714 : exactInterval 15 7714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7714 : oddCount 7714 15 = 6 ∧ acceleratedOrbit 15 7714 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7714) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7714.1, data_15_7714.2]

/-- Complete interval computation for depth 15, residue 7715. -/
theorem bounds_15_7715 : exactInterval 15 7715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7715 : oddCount 7715 15 = 6 ∧ acceleratedOrbit 15 7715 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7715) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7715.1, data_15_7715.2]

/-- Complete interval computation for depth 15, residue 7716. -/
theorem bounds_15_7716 : exactInterval 15 7716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7716 : oddCount 7716 15 = 8 ∧ acceleratedOrbit 15 7716 = 1547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7716) = 3 ^ 8 * m + 1547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7716.1, data_15_7716.2]

/-- Complete interval computation for depth 15, residue 7717. -/
theorem bounds_15_7717 : exactInterval 15 7717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7717 : oddCount 7717 15 = 8 ∧ acceleratedOrbit 15 7717 = 1547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7717) = 3 ^ 8 * m + 1547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7717.1, data_15_7717.2]

/-- Complete interval computation for depth 15, residue 7718. -/
theorem bounds_15_7718 : exactInterval 15 7718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7718 : oddCount 7718 15 = 8 ∧ acceleratedOrbit 15 7718 = 1547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7718) = 3 ^ 8 * m + 1547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7718.1, data_15_7718.2]

/-- Complete interval computation for depth 15, residue 7719. -/
theorem bounds_15_7719 : exactInterval 15 7719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7719 : oddCount 7719 15 = 6 ∧ acceleratedOrbit 15 7719 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7719) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7719.1, data_15_7719.2]

/-- Complete interval computation for depth 15, residue 7720. -/
theorem bounds_15_7720 : exactInterval 15 7720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7720 : oddCount 7720 15 = 4 ∧ acceleratedOrbit 15 7720 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7720) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7720.1, data_15_7720.2]

/-- Complete interval computation for depth 15, residue 7721. -/
theorem bounds_15_7721 : exactInterval 15 7721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7721 : oddCount 7721 15 = 12 ∧ acceleratedOrbit 15 7721 = 125252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7721) = 3 ^ 12 * m + 125252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7721.1, data_15_7721.2]

/-- Complete interval computation for depth 15, residue 7722. -/
theorem bounds_15_7722 : exactInterval 15 7722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7722 : oddCount 7722 15 = 4 ∧ acceleratedOrbit 15 7722 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7722) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7722.1, data_15_7722.2]

/-- Complete interval computation for depth 15, residue 7723. -/
theorem bounds_15_7723 : exactInterval 15 7723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7723 : oddCount 7723 15 = 6 ∧ acceleratedOrbit 15 7723 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7723) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7723.1, data_15_7723.2]

/-- Complete interval computation for depth 15, residue 7724. -/
theorem bounds_15_7724 : exactInterval 15 7724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7724 : oddCount 7724 15 = 8 ∧ acceleratedOrbit 15 7724 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7724) = 3 ^ 8 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7724.1, data_15_7724.2]

/-- Complete interval computation for depth 15, residue 7725. -/
theorem bounds_15_7725 : exactInterval 15 7725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7725 : oddCount 7725 15 = 8 ∧ acceleratedOrbit 15 7725 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7725) = 3 ^ 8 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7725.1, data_15_7725.2]

/-- Complete interval computation for depth 15, residue 7726. -/
theorem bounds_15_7726 : exactInterval 15 7726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7726 : oddCount 7726 15 = 8 ∧ acceleratedOrbit 15 7726 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7726) = 3 ^ 8 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7726.1, data_15_7726.2]

/-- Complete interval computation for depth 15, residue 7727. -/
theorem bounds_15_7727 : exactInterval 15 7727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7727 : oddCount 7727 15 = 10 ∧ acceleratedOrbit 15 7727 = 13927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7727) = 3 ^ 10 * m + 13927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7727.1, data_15_7727.2]

/-- Complete interval computation for depth 15, residue 7728. -/
theorem bounds_15_7728 : exactInterval 15 7728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7728 : oddCount 7728 15 = 4 ∧ acceleratedOrbit 15 7728 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7728) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7728.1, data_15_7728.2]

/-- Complete interval computation for depth 15, residue 7729. -/
theorem bounds_15_7729 : exactInterval 15 7729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7729 : oddCount 7729 15 = 8 ∧ acceleratedOrbit 15 7729 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7729) = 3 ^ 8 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7729.1, data_15_7729.2]

/-- Complete interval computation for depth 15, residue 7730. -/
theorem bounds_15_7730 : exactInterval 15 7730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7730 : oddCount 7730 15 = 8 ∧ acceleratedOrbit 15 7730 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7730) = 3 ^ 8 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7730.1, data_15_7730.2]

/-- Complete interval computation for depth 15, residue 7731. -/
theorem bounds_15_7731 : exactInterval 15 7731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7731 : oddCount 7731 15 = 8 ∧ acceleratedOrbit 15 7731 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7731) = 3 ^ 8 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7731.1, data_15_7731.2]

/-- Complete interval computation for depth 15, residue 7732. -/
theorem bounds_15_7732 : exactInterval 15 7732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7732 : oddCount 7732 15 = 4 ∧ acceleratedOrbit 15 7732 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7732) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7732.1, data_15_7732.2]

end Collatz.Research.PassageAtlas.Batch0236
