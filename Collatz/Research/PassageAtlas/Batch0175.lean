import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0175

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5701. -/
theorem bounds_15_5701 : exactInterval 15 5701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5701 : oddCount 5701 15 = 6 ∧ acceleratedOrbit 15 5701 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5701) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5701.1, data_15_5701.2]

/-- Complete interval computation for depth 15, residue 5702. -/
theorem bounds_15_5702 : exactInterval 15 5702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5702 : oddCount 5702 15 = 6 ∧ acceleratedOrbit 15 5702 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5702) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5702.1, data_15_5702.2]

/-- Complete interval computation for depth 15, residue 5703. -/
theorem bounds_15_5703 : exactInterval 15 5703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5703 : oddCount 5703 15 = 9 ∧ acceleratedOrbit 15 5703 = 3428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5703) = 3 ^ 9 * m + 3428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5703.1, data_15_5703.2]

/-- Complete interval computation for depth 15, residue 5704. -/
theorem bounds_15_5704 : exactInterval 15 5704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5704 : oddCount 5704 15 = 6 ∧ acceleratedOrbit 15 5704 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5704) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5704.1, data_15_5704.2]

/-- Complete interval computation for depth 15, residue 5705. -/
theorem bounds_15_5705 : exactInterval 15 5705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5705 : oddCount 5705 15 = 11 ∧ acceleratedOrbit 15 5705 = 30860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5705) = 3 ^ 11 * m + 30860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5705.1, data_15_5705.2]

/-- Complete interval computation for depth 15, residue 5706. -/
theorem bounds_15_5706 : exactInterval 15 5706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5706 : oddCount 5706 15 = 6 ∧ acceleratedOrbit 15 5706 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5706) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5706.1, data_15_5706.2]

/-- Complete interval computation for depth 15, residue 5707. -/
theorem bounds_15_5707 : exactInterval 15 5707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5707 : oddCount 5707 15 = 6 ∧ acceleratedOrbit 15 5707 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5707) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5707.1, data_15_5707.2]

/-- Complete interval computation for depth 15, residue 5708. -/
theorem bounds_15_5708 : exactInterval 15 5708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5708 : oddCount 5708 15 = 6 ∧ acceleratedOrbit 15 5708 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5708) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5708.1, data_15_5708.2]

/-- Complete interval computation for depth 15, residue 5709. -/
theorem bounds_15_5709 : exactInterval 15 5709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5709 : oddCount 5709 15 = 6 ∧ acceleratedOrbit 15 5709 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5709) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5709.1, data_15_5709.2]

/-- Complete interval computation for depth 15, residue 5710. -/
theorem bounds_15_5710 : exactInterval 15 5710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5710 : oddCount 5710 15 = 8 ∧ acceleratedOrbit 15 5710 = 1144 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5710) = 3 ^ 8 * m + 1144 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5710.1, data_15_5710.2]

/-- Complete interval computation for depth 15, residue 5711. -/
theorem bounds_15_5711 : exactInterval 15 5711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5711 : oddCount 5711 15 = 8 ∧ acceleratedOrbit 15 5711 = 1144 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5711) = 3 ^ 8 * m + 1144 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5711.1, data_15_5711.2]

/-- Complete interval computation for depth 15, residue 5712. -/
theorem bounds_15_5712 : exactInterval 15 5712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5712 : oddCount 5712 15 = 5 ∧ acceleratedOrbit 15 5712 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5712) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5712.1, data_15_5712.2]

/-- Complete interval computation for depth 15, residue 5713. -/
theorem bounds_15_5713 : exactInterval 15 5713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5713 : oddCount 5713 15 = 8 ∧ acceleratedOrbit 15 5713 = 1145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5713) = 3 ^ 8 * m + 1145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5713.1, data_15_5713.2]

/-- Complete interval computation for depth 15, residue 5714. -/
theorem bounds_15_5714 : exactInterval 15 5714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5714 : oddCount 5714 15 = 8 ∧ acceleratedOrbit 15 5714 = 1145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5714) = 3 ^ 8 * m + 1145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5714.1, data_15_5714.2]

/-- Complete interval computation for depth 15, residue 5715. -/
theorem bounds_15_5715 : exactInterval 15 5715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5715 : oddCount 5715 15 = 8 ∧ acceleratedOrbit 15 5715 = 1145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5715) = 3 ^ 8 * m + 1145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5715.1, data_15_5715.2]

/-- Complete interval computation for depth 15, residue 5716. -/
theorem bounds_15_5716 : exactInterval 15 5716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5716 : oddCount 5716 15 = 5 ∧ acceleratedOrbit 15 5716 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5716) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5716.1, data_15_5716.2]

/-- Complete interval computation for depth 15, residue 5717. -/
theorem bounds_15_5717 : exactInterval 15 5717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5717 : oddCount 5717 15 = 5 ∧ acceleratedOrbit 15 5717 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5717) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5717.1, data_15_5717.2]

/-- Complete interval computation for depth 15, residue 5718. -/
theorem bounds_15_5718 : exactInterval 15 5718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5718 : oddCount 5718 15 = 8 ∧ acceleratedOrbit 15 5718 = 1147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5718) = 3 ^ 8 * m + 1147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5718.1, data_15_5718.2]

/-- Complete interval computation for depth 15, residue 5719. -/
theorem bounds_15_5719 : exactInterval 15 5719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5719 : oddCount 5719 15 = 8 ∧ acceleratedOrbit 15 5719 = 1147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5719) = 3 ^ 8 * m + 1147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5719.1, data_15_5719.2]

/-- Complete interval computation for depth 15, residue 5720. -/
theorem bounds_15_5720 : exactInterval 15 5720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5720 : oddCount 5720 15 = 6 ∧ acceleratedOrbit 15 5720 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5720) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5720.1, data_15_5720.2]

/-- Complete interval computation for depth 15, residue 5721. -/
theorem bounds_15_5721 : exactInterval 15 5721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5721 : oddCount 5721 15 = 8 ∧ acceleratedOrbit 15 5721 = 1147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5721) = 3 ^ 8 * m + 1147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5721.1, data_15_5721.2]

/-- Complete interval computation for depth 15, residue 5722. -/
theorem bounds_15_5722 : exactInterval 15 5722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5722 : oddCount 5722 15 = 6 ∧ acceleratedOrbit 15 5722 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5722) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5722.1, data_15_5722.2]

/-- Complete interval computation for depth 15, residue 5723. -/
theorem bounds_15_5723 : exactInterval 15 5723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5723 : oddCount 5723 15 = 9 ∧ acceleratedOrbit 15 5723 = 3439 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5723) = 3 ^ 9 * m + 3439 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5723.1, data_15_5723.2]

/-- Complete interval computation for depth 15, residue 5724. -/
theorem bounds_15_5724 : exactInterval 15 5724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5724 : oddCount 5724 15 = 6 ∧ acceleratedOrbit 15 5724 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5724) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5724.1, data_15_5724.2]

/-- Complete interval computation for depth 15, residue 5725. -/
theorem bounds_15_5725 : exactInterval 15 5725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5725 : oddCount 5725 15 = 6 ∧ acceleratedOrbit 15 5725 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5725) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5725.1, data_15_5725.2]

/-- Complete interval computation for depth 15, residue 5726. -/
theorem bounds_15_5726 : exactInterval 15 5726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5726 : oddCount 5726 15 = 9 ∧ acceleratedOrbit 15 5726 = 3442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5726) = 3 ^ 9 * m + 3442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5726.1, data_15_5726.2]

/-- Complete interval computation for depth 15, residue 5727. -/
theorem bounds_15_5727 : exactInterval 15 5727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5727 : oddCount 5727 15 = 9 ∧ acceleratedOrbit 15 5727 = 3442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5727) = 3 ^ 9 * m + 3442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5727.1, data_15_5727.2]

/-- Complete interval computation for depth 15, residue 5728. -/
theorem bounds_15_5728 : exactInterval 15 5728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5728 : oddCount 5728 15 = 5 ∧ acceleratedOrbit 15 5728 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5728) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5728.1, data_15_5728.2]

/-- Complete interval computation for depth 15, residue 5729. -/
theorem bounds_15_5729 : exactInterval 15 5729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5729 : oddCount 5729 15 = 6 ∧ acceleratedOrbit 15 5729 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5729) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5729.1, data_15_5729.2]

/-- Complete interval computation for depth 15, residue 5730. -/
theorem bounds_15_5730 : exactInterval 15 5730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5730 : oddCount 5730 15 = 6 ∧ acceleratedOrbit 15 5730 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5730) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5730.1, data_15_5730.2]

/-- Complete interval computation for depth 15, residue 5731. -/
theorem bounds_15_5731 : exactInterval 15 5731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5731 : oddCount 5731 15 = 6 ∧ acceleratedOrbit 15 5731 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5731) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5731.1, data_15_5731.2]

/-- Complete interval computation for depth 15, residue 5732. -/
theorem bounds_15_5732 : exactInterval 15 5732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5732 : oddCount 5732 15 = 6 ∧ acceleratedOrbit 15 5732 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5732) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5732.1, data_15_5732.2]

/-- Complete interval computation for depth 15, residue 5733. -/
theorem bounds_15_5733 : exactInterval 15 5733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5733 : oddCount 5733 15 = 6 ∧ acceleratedOrbit 15 5733 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5733) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5733.1, data_15_5733.2]

end Collatz.Research.PassageAtlas.Batch0175
