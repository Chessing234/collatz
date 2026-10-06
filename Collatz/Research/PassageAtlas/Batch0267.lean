import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0267

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8716. -/
theorem bounds_15_8716 : exactInterval 15 8716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8716 : oddCount 8716 15 = 5 ∧ acceleratedOrbit 15 8716 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8716) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8716.1, data_15_8716.2]

/-- Complete interval computation for depth 15, residue 8717. -/
theorem bounds_15_8717 : exactInterval 15 8717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8717 : oddCount 8717 15 = 5 ∧ acceleratedOrbit 15 8717 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8717) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8717.1, data_15_8717.2]

/-- Complete interval computation for depth 15, residue 8718. -/
theorem bounds_15_8718 : exactInterval 15 8718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8718 : oddCount 8718 15 = 9 ∧ acceleratedOrbit 15 8718 = 5240 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8718) = 3 ^ 9 * m + 5240 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8718.1, data_15_8718.2]

/-- Complete interval computation for depth 15, residue 8719. -/
theorem bounds_15_8719 : exactInterval 15 8719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8719 : oddCount 8719 15 = 9 ∧ acceleratedOrbit 15 8719 = 5240 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8719) = 3 ^ 9 * m + 5240 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8719.1, data_15_8719.2]

/-- Complete interval computation for depth 15, residue 8720. -/
theorem bounds_15_8720 : exactInterval 15 8720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8720 : oddCount 8720 15 = 5 ∧ acceleratedOrbit 15 8720 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8720) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8720.1, data_15_8720.2]

/-- Complete interval computation for depth 15, residue 8721. -/
theorem bounds_15_8721 : exactInterval 15 8721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8721 : oddCount 8721 15 = 5 ∧ acceleratedOrbit 15 8721 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8721) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8721.1, data_15_8721.2]

/-- Complete interval computation for depth 15, residue 8722. -/
theorem bounds_15_8722 : exactInterval 15 8722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8722 : oddCount 8722 15 = 8 ∧ acceleratedOrbit 15 8722 = 1748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8722) = 3 ^ 8 * m + 1748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8722.1, data_15_8722.2]

/-- Complete interval computation for depth 15, residue 8723. -/
theorem bounds_15_8723 : exactInterval 15 8723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8723 : oddCount 8723 15 = 8 ∧ acceleratedOrbit 15 8723 = 1748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8723) = 3 ^ 8 * m + 1748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8723.1, data_15_8723.2]

/-- Complete interval computation for depth 15, residue 8724. -/
theorem bounds_15_8724 : exactInterval 15 8724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8724 : oddCount 8724 15 = 5 ∧ acceleratedOrbit 15 8724 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8724) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8724.1, data_15_8724.2]

/-- Complete interval computation for depth 15, residue 8725. -/
theorem bounds_15_8725 : exactInterval 15 8725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8725 : oddCount 8725 15 = 5 ∧ acceleratedOrbit 15 8725 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8725) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8725.1, data_15_8725.2]

/-- Complete interval computation for depth 15, residue 8726. -/
theorem bounds_15_8726 : exactInterval 15 8726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8726 : oddCount 8726 15 = 7 ∧ acceleratedOrbit 15 8726 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8726) = 3 ^ 7 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8726.1, data_15_8726.2]

/-- Complete interval computation for depth 15, residue 8727. -/
theorem bounds_15_8727 : exactInterval 15 8727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8727 : oddCount 8727 15 = 7 ∧ acceleratedOrbit 15 8727 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8727) = 3 ^ 7 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8727.1, data_15_8727.2]

/-- Complete interval computation for depth 15, residue 8728. -/
theorem bounds_15_8728 : exactInterval 15 8728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8728 : oddCount 8728 15 = 5 ∧ acceleratedOrbit 15 8728 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8728) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8728.1, data_15_8728.2]

/-- Complete interval computation for depth 15, residue 8729. -/
theorem bounds_15_8729 : exactInterval 15 8729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8729 : oddCount 8729 15 = 7 ∧ acceleratedOrbit 15 8729 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8729) = 3 ^ 7 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8729.1, data_15_8729.2]

/-- Complete interval computation for depth 15, residue 8730. -/
theorem bounds_15_8730 : exactInterval 15 8730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8730 : oddCount 8730 15 = 5 ∧ acceleratedOrbit 15 8730 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8730) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8730.1, data_15_8730.2]

/-- Complete interval computation for depth 15, residue 8731. -/
theorem bounds_15_8731 : exactInterval 15 8731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8731 : oddCount 8731 15 = 9 ∧ acceleratedOrbit 15 8731 = 5246 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8731) = 3 ^ 9 * m + 5246 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8731.1, data_15_8731.2]

/-- Complete interval computation for depth 15, residue 8732. -/
theorem bounds_15_8732 : exactInterval 15 8732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8732 : oddCount 8732 15 = 7 ∧ acceleratedOrbit 15 8732 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8732) = 3 ^ 7 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8732.1, data_15_8732.2]

/-- Complete interval computation for depth 15, residue 8733. -/
theorem bounds_15_8733 : exactInterval 15 8733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8733 : oddCount 8733 15 = 7 ∧ acceleratedOrbit 15 8733 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8733) = 3 ^ 7 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8733.1, data_15_8733.2]

/-- Complete interval computation for depth 15, residue 8734. -/
theorem bounds_15_8734 : exactInterval 15 8734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8734 : oddCount 8734 15 = 7 ∧ acceleratedOrbit 15 8734 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8734) = 3 ^ 7 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8734.1, data_15_8734.2]

/-- Complete interval computation for depth 15, residue 8735. -/
theorem bounds_15_8735 : exactInterval 15 8735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8735 : oddCount 8735 15 = 9 ∧ acceleratedOrbit 15 8735 = 5248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8735) = 3 ^ 9 * m + 5248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8735.1, data_15_8735.2]

/-- Complete interval computation for depth 15, residue 8736. -/
theorem bounds_15_8736 : exactInterval 15 8736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8736 : oddCount 8736 15 = 4 ∧ acceleratedOrbit 15 8736 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8736) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8736.1, data_15_8736.2]

/-- Complete interval computation for depth 15, residue 8737. -/
theorem bounds_15_8737 : exactInterval 15 8737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8737 : oddCount 8737 15 = 7 ∧ acceleratedOrbit 15 8737 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8737) = 3 ^ 7 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8737.1, data_15_8737.2]

/-- Complete interval computation for depth 15, residue 8738. -/
theorem bounds_15_8738 : exactInterval 15 8738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8738 : oddCount 8738 15 = 5 ∧ acceleratedOrbit 15 8738 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8738) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8738.1, data_15_8738.2]

/-- Complete interval computation for depth 15, residue 8739. -/
theorem bounds_15_8739 : exactInterval 15 8739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8739 : oddCount 8739 15 = 5 ∧ acceleratedOrbit 15 8739 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8739) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8739.1, data_15_8739.2]

/-- Complete interval computation for depth 15, residue 8740. -/
theorem bounds_15_8740 : exactInterval 15 8740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8740 : oddCount 8740 15 = 9 ∧ acceleratedOrbit 15 8740 = 5255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8740) = 3 ^ 9 * m + 5255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8740.1, data_15_8740.2]

/-- Complete interval computation for depth 15, residue 8741. -/
theorem bounds_15_8741 : exactInterval 15 8741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8741 : oddCount 8741 15 = 9 ∧ acceleratedOrbit 15 8741 = 5255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8741) = 3 ^ 9 * m + 5255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8741.1, data_15_8741.2]

/-- Complete interval computation for depth 15, residue 8742. -/
theorem bounds_15_8742 : exactInterval 15 8742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8742 : oddCount 8742 15 = 9 ∧ acceleratedOrbit 15 8742 = 5255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8742) = 3 ^ 9 * m + 5255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8742.1, data_15_8742.2]

/-- Complete interval computation for depth 15, residue 8743. -/
theorem bounds_15_8743 : exactInterval 15 8743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8743 : oddCount 8743 15 = 9 ∧ acceleratedOrbit 15 8743 = 5255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8743) = 3 ^ 9 * m + 5255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8743.1, data_15_8743.2]

/-- Complete interval computation for depth 15, residue 8744. -/
theorem bounds_15_8744 : exactInterval 15 8744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8744 : oddCount 8744 15 = 4 ∧ acceleratedOrbit 15 8744 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8744) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8744.1, data_15_8744.2]

/-- Complete interval computation for depth 15, residue 8745. -/
theorem bounds_15_8745 : exactInterval 15 8745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8745 : oddCount 8745 15 = 9 ∧ acceleratedOrbit 15 8745 = 5254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8745) = 3 ^ 9 * m + 5254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8745.1, data_15_8745.2]

/-- Complete interval computation for depth 15, residue 8746. -/
theorem bounds_15_8746 : exactInterval 15 8746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8746 : oddCount 8746 15 = 4 ∧ acceleratedOrbit 15 8746 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8746) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8746.1, data_15_8746.2]

/-- Complete interval computation for depth 15, residue 8747. -/
theorem bounds_15_8747 : exactInterval 15 8747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8747 : oddCount 8747 15 = 5 ∧ acceleratedOrbit 15 8747 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8747) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8747.1, data_15_8747.2]

/-- Complete interval computation for depth 15, residue 8748. -/
theorem bounds_15_8748 : exactInterval 15 8748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8748 : oddCount 8748 15 = 9 ∧ acceleratedOrbit 15 8748 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8748) = 3 ^ 9 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8748.1, data_15_8748.2]

end Collatz.Research.PassageAtlas.Batch0267
