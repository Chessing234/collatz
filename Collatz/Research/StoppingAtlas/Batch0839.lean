import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0839

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5703. -/
theorem bounds_13_5703 : exactInterval 13 5703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5703 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5703) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5703 : oddCount 5703 13 = 7 ∧ acceleratedOrbit 13 5703 = 1523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5703 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5703) = 3 ^ 7 * m + 1523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5703.1, data_13_5703.2]

/-- Complete interval computation for depth 13, residue 5704. -/
theorem bounds_13_5704 : exactInterval 13 5704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5704 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5704) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5704 : oddCount 5704 13 = 5 ∧ acceleratedOrbit 13 5704 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5704 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5704) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5704.1, data_13_5704.2]

/-- Complete interval computation for depth 13, residue 5705. -/
theorem bounds_13_5705 : exactInterval 13 5705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5705 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5705) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5705 : oddCount 5705 13 = 9 ∧ acceleratedOrbit 13 5705 = 13715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5705 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5705) = 3 ^ 9 * m + 13715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5705.1, data_13_5705.2]

/-- Complete interval computation for depth 13, residue 5706. -/
theorem bounds_13_5706 : exactInterval 13 5706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5706 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5706) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5706 : oddCount 5706 13 = 5 ∧ acceleratedOrbit 13 5706 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5706 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5706) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5706.1, data_13_5706.2]

/-- Complete interval computation for depth 13, residue 5707. -/
theorem bounds_13_5707 : exactInterval 13 5707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5707 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5707) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5707 : oddCount 5707 13 = 5 ∧ acceleratedOrbit 13 5707 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5707 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5707) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5707.1, data_13_5707.2]

/-- Complete interval computation for depth 13, residue 5708. -/
theorem bounds_13_5708 : exactInterval 13 5708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5708 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5708) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5708 : oddCount 5708 13 = 5 ∧ acceleratedOrbit 13 5708 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5708 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5708) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5708.1, data_13_5708.2]

/-- Complete interval computation for depth 13, residue 5709. -/
theorem bounds_13_5709 : exactInterval 13 5709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5709 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5709) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5709 : oddCount 5709 13 = 5 ∧ acceleratedOrbit 13 5709 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5709 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5709) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5709.1, data_13_5709.2]

/-- Complete interval computation for depth 13, residue 5710. -/
theorem bounds_13_5710 : exactInterval 13 5710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5710 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5710) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5710 : oddCount 5710 13 = 8 ∧ acceleratedOrbit 13 5710 = 4576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5710 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5710) = 3 ^ 8 * m + 4576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5710.1, data_13_5710.2]

/-- Complete interval computation for depth 13, residue 5711. -/
theorem bounds_13_5711 : exactInterval 13 5711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5711 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5711) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5711 : oddCount 5711 13 = 8 ∧ acceleratedOrbit 13 5711 = 4576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5711 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5711) = 3 ^ 8 * m + 4576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5711.1, data_13_5711.2]

/-- Complete interval computation for depth 13, residue 5712. -/
theorem bounds_13_5712 : exactInterval 13 5712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5712 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5712) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5712 : oddCount 5712 13 = 3 ∧ acceleratedOrbit 13 5712 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5712 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5712) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5712.1, data_13_5712.2]

/-- Complete interval computation for depth 13, residue 5713. -/
theorem bounds_13_5713 : exactInterval 13 5713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5713 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5713) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5713 : oddCount 5713 13 = 8 ∧ acceleratedOrbit 13 5713 = 4580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5713 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5713) = 3 ^ 8 * m + 4580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5713.1, data_13_5713.2]

/-- Complete interval computation for depth 13, residue 5714. -/
theorem bounds_13_5714 : exactInterval 13 5714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5714 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5714) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5714 : oddCount 5714 13 = 8 ∧ acceleratedOrbit 13 5714 = 4580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5714 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5714) = 3 ^ 8 * m + 4580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5714.1, data_13_5714.2]

/-- Complete interval computation for depth 13, residue 5715. -/
theorem bounds_13_5715 : exactInterval 13 5715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5715 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5715) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5715 : oddCount 5715 13 = 8 ∧ acceleratedOrbit 13 5715 = 4580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5715 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5715) = 3 ^ 8 * m + 4580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5715.1, data_13_5715.2]

/-- Complete interval computation for depth 13, residue 5716. -/
theorem bounds_13_5716 : exactInterval 13 5716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5716 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5716) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5716 : oddCount 5716 13 = 3 ∧ acceleratedOrbit 13 5716 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5716 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5716) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5716.1, data_13_5716.2]

/-- Complete interval computation for depth 13, residue 5717. -/
theorem bounds_13_5717 : exactInterval 13 5717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5717 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5717) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5717 : oddCount 5717 13 = 3 ∧ acceleratedOrbit 13 5717 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5717 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5717) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5717.1, data_13_5717.2]

/-- Complete interval computation for depth 13, residue 5718. -/
theorem bounds_13_5718 : exactInterval 13 5718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5718 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5718) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5718 : oddCount 5718 13 = 7 ∧ acceleratedOrbit 13 5718 = 1529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5718 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5718) = 3 ^ 7 * m + 1529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5718.1, data_13_5718.2]

end Collatz.Research.StoppingAtlas.Batch0839
