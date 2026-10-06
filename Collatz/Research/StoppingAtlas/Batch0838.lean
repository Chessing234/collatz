import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0838

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5688. -/
theorem bounds_13_5688 : exactInterval 13 5688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5688 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5688) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5688 : oddCount 5688 13 = 5 ∧ acceleratedOrbit 13 5688 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5688 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5688) = 3 ^ 5 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5688.1, data_13_5688.2]

/-- Complete interval computation for depth 13, residue 5689. -/
theorem bounds_13_5689 : exactInterval 13 5689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5689 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5689) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5689 : oddCount 5689 13 = 7 ∧ acceleratedOrbit 13 5689 = 1520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5689 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5689) = 3 ^ 7 * m + 1520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5689.1, data_13_5689.2]

/-- Complete interval computation for depth 13, residue 5690. -/
theorem bounds_13_5690 : exactInterval 13 5690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5690 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5690) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5690 : oddCount 5690 13 = 5 ∧ acceleratedOrbit 13 5690 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5690 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5690) = 3 ^ 5 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5690.1, data_13_5690.2]

/-- Complete interval computation for depth 13, residue 5691. -/
theorem bounds_13_5691 : exactInterval 13 5691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5691 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5691) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5691 : oddCount 5691 13 = 8 ∧ acceleratedOrbit 13 5691 = 4562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5691 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5691) = 3 ^ 8 * m + 4562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5691.1, data_13_5691.2]

/-- Complete interval computation for depth 13, residue 5692. -/
theorem bounds_13_5692 : exactInterval 13 5692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5692 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5692) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5692 : oddCount 5692 13 = 5 ∧ acceleratedOrbit 13 5692 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5692 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5692) = 3 ^ 5 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5692.1, data_13_5692.2]

/-- Complete interval computation for depth 13, residue 5693. -/
theorem bounds_13_5693 : exactInterval 13 5693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5693 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5693) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5693 : oddCount 5693 13 = 5 ∧ acceleratedOrbit 13 5693 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5693 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5693) = 3 ^ 5 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5693.1, data_13_5693.2]

/-- Complete interval computation for depth 13, residue 5694. -/
theorem bounds_13_5694 : exactInterval 13 5694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5694 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5694) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5694 : oddCount 5694 13 = 9 ∧ acceleratedOrbit 13 5694 = 13688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5694 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5694) = 3 ^ 9 * m + 13688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5694.1, data_13_5694.2]

/-- Complete interval computation for depth 13, residue 5695. -/
theorem bounds_13_5695 : exactInterval 13 5695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5695 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5695) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5695 : oddCount 5695 13 = 9 ∧ acceleratedOrbit 13 5695 = 13688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5695 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5695) = 3 ^ 9 * m + 13688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5695.1, data_13_5695.2]

/-- Complete interval computation for depth 13, residue 5696. -/
theorem bounds_13_5696 : exactInterval 13 5696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5696 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5696) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5696 : oddCount 5696 13 = 3 ∧ acceleratedOrbit 13 5696 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5696 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5696) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5696.1, data_13_5696.2]

/-- Complete interval computation for depth 13, residue 5697. -/
theorem bounds_13_5697 : exactInterval 13 5697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5697 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5697) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5697 : oddCount 5697 13 = 6 ∧ acceleratedOrbit 13 5697 = 508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5697 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5697) = 3 ^ 6 * m + 508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5697.1, data_13_5697.2]

/-- Complete interval computation for depth 13, residue 5698. -/
theorem bounds_13_5698 : exactInterval 13 5698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5698 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5698) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5698 : oddCount 5698 13 = 6 ∧ acceleratedOrbit 13 5698 = 508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5698 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5698) = 3 ^ 6 * m + 508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5698.1, data_13_5698.2]

/-- Complete interval computation for depth 13, residue 5699. -/
theorem bounds_13_5699 : exactInterval 13 5699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5699 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5699) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5699 : oddCount 5699 13 = 6 ∧ acceleratedOrbit 13 5699 = 508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5699 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5699) = 3 ^ 6 * m + 508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5699.1, data_13_5699.2]

/-- Complete interval computation for depth 13, residue 5700. -/
theorem bounds_13_5700 : exactInterval 13 5700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5700 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5700) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5700 : oddCount 5700 13 = 5 ∧ acceleratedOrbit 13 5700 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5700 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5700) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5700.1, data_13_5700.2]

/-- Complete interval computation for depth 13, residue 5701. -/
theorem bounds_13_5701 : exactInterval 13 5701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5701 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5701) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5701 : oddCount 5701 13 = 5 ∧ acceleratedOrbit 13 5701 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5701 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5701) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5701.1, data_13_5701.2]

/-- Complete interval computation for depth 13, residue 5702. -/
theorem bounds_13_5702 : exactInterval 13 5702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5702 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5702) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5702 : oddCount 5702 13 = 5 ∧ acceleratedOrbit 13 5702 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5702 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5702) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5702.1, data_13_5702.2]

end Collatz.Research.StoppingAtlas.Batch0838
