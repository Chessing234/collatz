import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0968

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31686. -/
theorem bounds_15_31686 : exactInterval 15 31686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31686 : oddCount 31686 15 = 5 ∧ acceleratedOrbit 15 31686 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31686) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31686.1, data_15_31686.2]

/-- Complete interval computation for depth 15, residue 31687. -/
theorem bounds_15_31687 : exactInterval 15 31687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31687 : oddCount 31687 15 = 12 ∧ acceleratedOrbit 15 31687 = 513944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31687) = 3 ^ 12 * m + 513944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31687.1, data_15_31687.2]

/-- Complete interval computation for depth 15, residue 31688. -/
theorem bounds_15_31688 : exactInterval 15 31688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31688 : oddCount 31688 15 = 7 ∧ acceleratedOrbit 15 31688 = 2116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31688) = 3 ^ 7 * m + 2116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31688.1, data_15_31688.2]

/-- Complete interval computation for depth 15, residue 31689. -/
theorem bounds_15_31689 : exactInterval 15 31689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31689 : oddCount 31689 15 = 8 ∧ acceleratedOrbit 15 31689 = 6346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31689) = 3 ^ 8 * m + 6346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31689.1, data_15_31689.2]

/-- Complete interval computation for depth 15, residue 31690. -/
theorem bounds_15_31690 : exactInterval 15 31690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31690 : oddCount 31690 15 = 7 ∧ acceleratedOrbit 15 31690 = 2116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31690) = 3 ^ 7 * m + 2116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31690.1, data_15_31690.2]

/-- Complete interval computation for depth 15, residue 31691. -/
theorem bounds_15_31691 : exactInterval 15 31691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31691 : oddCount 31691 15 = 7 ∧ acceleratedOrbit 15 31691 = 2116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31691) = 3 ^ 7 * m + 2116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31691.1, data_15_31691.2]

/-- Complete interval computation for depth 15, residue 31692. -/
theorem bounds_15_31692 : exactInterval 15 31692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31692 : oddCount 31692 15 = 7 ∧ acceleratedOrbit 15 31692 = 2116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31692) = 3 ^ 7 * m + 2116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31692.1, data_15_31692.2]

/-- Complete interval computation for depth 15, residue 31693. -/
theorem bounds_15_31693 : exactInterval 15 31693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31693 : oddCount 31693 15 = 7 ∧ acceleratedOrbit 15 31693 = 2116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31693) = 3 ^ 7 * m + 2116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31693.1, data_15_31693.2]

/-- Complete interval computation for depth 15, residue 31694. -/
theorem bounds_15_31694 : exactInterval 15 31694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31694 : oddCount 31694 15 = 8 ∧ acceleratedOrbit 15 31694 = 6347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31694) = 3 ^ 8 * m + 6347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31694.1, data_15_31694.2]

/-- Complete interval computation for depth 15, residue 31695. -/
theorem bounds_15_31695 : exactInterval 15 31695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31695 : oddCount 31695 15 = 8 ∧ acceleratedOrbit 15 31695 = 6347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31695) = 3 ^ 8 * m + 6347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31695.1, data_15_31695.2]

/-- Complete interval computation for depth 15, residue 31696. -/
theorem bounds_15_31696 : exactInterval 15 31696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31696 : oddCount 31696 15 = 7 ∧ acceleratedOrbit 15 31696 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31696) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31696.1, data_15_31696.2]

/-- Complete interval computation for depth 15, residue 31697. -/
theorem bounds_15_31697 : exactInterval 15 31697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31697 : oddCount 31697 15 = 7 ∧ acceleratedOrbit 15 31697 = 2116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31697) = 3 ^ 7 * m + 2116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31697.1, data_15_31697.2]

/-- Complete interval computation for depth 15, residue 31698. -/
theorem bounds_15_31698 : exactInterval 15 31698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31698 : oddCount 31698 15 = 9 ∧ acceleratedOrbit 15 31698 = 19043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31698) = 3 ^ 9 * m + 19043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31698.1, data_15_31698.2]

/-- Complete interval computation for depth 15, residue 31699. -/
theorem bounds_15_31699 : exactInterval 15 31699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31699 : oddCount 31699 15 = 9 ∧ acceleratedOrbit 15 31699 = 19043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31699) = 3 ^ 9 * m + 19043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31699.1, data_15_31699.2]

/-- Complete interval computation for depth 15, residue 31700. -/
theorem bounds_15_31700 : exactInterval 15 31700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31700 : oddCount 31700 15 = 7 ∧ acceleratedOrbit 15 31700 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31700) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31700.1, data_15_31700.2]

/-- Complete interval computation for depth 15, residue 31701. -/
theorem bounds_15_31701 : exactInterval 15 31701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31701 : oddCount 31701 15 = 7 ∧ acceleratedOrbit 15 31701 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31701) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31701.1, data_15_31701.2]

/-- Complete interval computation for depth 15, residue 31702. -/
theorem bounds_15_31702 : exactInterval 15 31702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31702 : oddCount 31702 15 = 9 ∧ acceleratedOrbit 15 31702 = 19045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31702) = 3 ^ 9 * m + 19045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31702.1, data_15_31702.2]

/-- Complete interval computation for depth 15, residue 31703. -/
theorem bounds_15_31703 : exactInterval 15 31703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31703 : oddCount 31703 15 = 9 ∧ acceleratedOrbit 15 31703 = 19045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31703) = 3 ^ 9 * m + 19045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31703.1, data_15_31703.2]

/-- Complete interval computation for depth 15, residue 31704. -/
theorem bounds_15_31704 : exactInterval 15 31704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31704 : oddCount 31704 15 = 7 ∧ acceleratedOrbit 15 31704 = 2117 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31704) = 3 ^ 7 * m + 2117 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31704.1, data_15_31704.2]

/-- Complete interval computation for depth 15, residue 31705. -/
theorem bounds_15_31705 : exactInterval 15 31705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31705 : oddCount 31705 15 = 5 ∧ acceleratedOrbit 15 31705 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31705) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31705.1, data_15_31705.2]

/-- Complete interval computation for depth 15, residue 31706. -/
theorem bounds_15_31706 : exactInterval 15 31706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31706 : oddCount 31706 15 = 7 ∧ acceleratedOrbit 15 31706 = 2117 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31706) = 3 ^ 7 * m + 2117 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31706.1, data_15_31706.2]

/-- Complete interval computation for depth 15, residue 31707. -/
theorem bounds_15_31707 : exactInterval 15 31707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31707 : oddCount 31707 15 = 9 ∧ acceleratedOrbit 15 31707 = 19048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31707) = 3 ^ 9 * m + 19048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31707.1, data_15_31707.2]

/-- Complete interval computation for depth 15, residue 31708. -/
theorem bounds_15_31708 : exactInterval 15 31708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31708 : oddCount 31708 15 = 7 ∧ acceleratedOrbit 15 31708 = 2117 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31708) = 3 ^ 7 * m + 2117 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31708.1, data_15_31708.2]

/-- Complete interval computation for depth 15, residue 31709. -/
theorem bounds_15_31709 : exactInterval 15 31709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31709 : oddCount 31709 15 = 7 ∧ acceleratedOrbit 15 31709 = 2117 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31709) = 3 ^ 7 * m + 2117 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31709.1, data_15_31709.2]

/-- Complete interval computation for depth 15, residue 31710. -/
theorem bounds_15_31710 : exactInterval 15 31710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31710 : oddCount 31710 15 = 9 ∧ acceleratedOrbit 15 31710 = 19049 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31710) = 3 ^ 9 * m + 19049 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31710.1, data_15_31710.2]

/-- Complete interval computation for depth 15, residue 31711. -/
theorem bounds_15_31711 : exactInterval 15 31711 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31711) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31711 : oddCount 31711 15 = 9 ∧ acceleratedOrbit 15 31711 = 19049 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31711) = 3 ^ 9 * m + 19049 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31711.1, data_15_31711.2]

/-- Complete interval computation for depth 15, residue 31712. -/
theorem bounds_15_31712 : exactInterval 15 31712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31712 : oddCount 31712 15 = 7 ∧ acceleratedOrbit 15 31712 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31712) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31712.1, data_15_31712.2]

/-- Complete interval computation for depth 15, residue 31713. -/
theorem bounds_15_31713 : exactInterval 15 31713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31713 : oddCount 31713 15 = 9 ∧ acceleratedOrbit 15 31713 = 19052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31713) = 3 ^ 9 * m + 19052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31713.1, data_15_31713.2]

/-- Complete interval computation for depth 15, residue 31714. -/
theorem bounds_15_31714 : exactInterval 15 31714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31714 : oddCount 31714 15 = 7 ∧ acceleratedOrbit 15 31714 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31714) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31714.1, data_15_31714.2]

/-- Complete interval computation for depth 15, residue 31715. -/
theorem bounds_15_31715 : exactInterval 15 31715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31715 : oddCount 31715 15 = 7 ∧ acceleratedOrbit 15 31715 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31715) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31715.1, data_15_31715.2]

/-- Complete interval computation for depth 15, residue 31716. -/
theorem bounds_15_31716 : exactInterval 15 31716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31716 : oddCount 31716 15 = 6 ∧ acceleratedOrbit 15 31716 = 706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31716) = 3 ^ 6 * m + 706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31716.1, data_15_31716.2]

/-- Complete interval computation for depth 15, residue 31717. -/
theorem bounds_15_31717 : exactInterval 15 31717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31717 : oddCount 31717 15 = 6 ∧ acceleratedOrbit 15 31717 = 706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31717) = 3 ^ 6 * m + 706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31717.1, data_15_31717.2]

/-- Complete interval computation for depth 15, residue 31718. -/
theorem bounds_15_31718 : exactInterval 15 31718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31718 : oddCount 31718 15 = 6 ∧ acceleratedOrbit 15 31718 = 706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31718) = 3 ^ 6 * m + 706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31718.1, data_15_31718.2]

end Collatz.Research.PassageAtlas.Batch0968
