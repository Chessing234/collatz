import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0663

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21692. -/
theorem bounds_15_21692 : exactInterval 15 21692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21692 : oddCount 21692 15 = 9 ∧ acceleratedOrbit 15 21692 = 13034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21692) = 3 ^ 9 * m + 13034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21692.1, data_15_21692.2]

/-- Complete interval computation for depth 15, residue 21693. -/
theorem bounds_15_21693 : exactInterval 15 21693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21693 : oddCount 21693 15 = 9 ∧ acceleratedOrbit 15 21693 = 13034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21693) = 3 ^ 9 * m + 13034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21693.1, data_15_21693.2]

/-- Complete interval computation for depth 15, residue 21694. -/
theorem bounds_15_21694 : exactInterval 15 21694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21694 : oddCount 21694 15 = 9 ∧ acceleratedOrbit 15 21694 = 13034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21694) = 3 ^ 9 * m + 13034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21694.1, data_15_21694.2]

/-- Complete interval computation for depth 15, residue 21695. -/
theorem bounds_15_21695 : exactInterval 15 21695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21695 : oddCount 21695 15 = 10 ∧ acceleratedOrbit 15 21695 = 39098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21695) = 3 ^ 10 * m + 39098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21695.1, data_15_21695.2]

/-- Complete interval computation for depth 15, residue 21696. -/
theorem bounds_15_21696 : exactInterval 15 21696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21696 : oddCount 21696 15 = 7 ∧ acceleratedOrbit 15 21696 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21696) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21696.1, data_15_21696.2]

/-- Complete interval computation for depth 15, residue 21697. -/
theorem bounds_15_21697 : exactInterval 15 21697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21697 : oddCount 21697 15 = 9 ∧ acceleratedOrbit 15 21697 = 13040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21697) = 3 ^ 9 * m + 13040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21697.1, data_15_21697.2]

/-- Complete interval computation for depth 15, residue 21698. -/
theorem bounds_15_21698 : exactInterval 15 21698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21698 : oddCount 21698 15 = 9 ∧ acceleratedOrbit 15 21698 = 13040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21698) = 3 ^ 9 * m + 13040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21698.1, data_15_21698.2]

/-- Complete interval computation for depth 15, residue 21699. -/
theorem bounds_15_21699 : exactInterval 15 21699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21699 : oddCount 21699 15 = 9 ∧ acceleratedOrbit 15 21699 = 13040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21699) = 3 ^ 9 * m + 13040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21699.1, data_15_21699.2]

/-- Complete interval computation for depth 15, residue 21700. -/
theorem bounds_15_21700 : exactInterval 15 21700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21700 : oddCount 21700 15 = 7 ∧ acceleratedOrbit 15 21700 = 1451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21700) = 3 ^ 7 * m + 1451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21700.1, data_15_21700.2]

/-- Complete interval computation for depth 15, residue 21701. -/
theorem bounds_15_21701 : exactInterval 15 21701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21701 : oddCount 21701 15 = 7 ∧ acceleratedOrbit 15 21701 = 1451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21701) = 3 ^ 7 * m + 1451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21701.1, data_15_21701.2]

/-- Complete interval computation for depth 15, residue 21702. -/
theorem bounds_15_21702 : exactInterval 15 21702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21702 : oddCount 21702 15 = 7 ∧ acceleratedOrbit 15 21702 = 1451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21702) = 3 ^ 7 * m + 1451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21702.1, data_15_21702.2]

/-- Complete interval computation for depth 15, residue 21703. -/
theorem bounds_15_21703 : exactInterval 15 21703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21703 : oddCount 21703 15 = 9 ∧ acceleratedOrbit 15 21703 = 13040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21703) = 3 ^ 9 * m + 13040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21703.1, data_15_21703.2]

/-- Complete interval computation for depth 15, residue 21704. -/
theorem bounds_15_21704 : exactInterval 15 21704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21704 : oddCount 21704 15 = 7 ∧ acceleratedOrbit 15 21704 = 1451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21704) = 3 ^ 7 * m + 1451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21704.1, data_15_21704.2]

/-- Complete interval computation for depth 15, residue 21705. -/
theorem bounds_15_21705 : exactInterval 15 21705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21705 : oddCount 21705 15 = 5 ∧ acceleratedOrbit 15 21705 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21705) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21705.1, data_15_21705.2]

/-- Complete interval computation for depth 15, residue 21706. -/
theorem bounds_15_21706 : exactInterval 15 21706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21706 : oddCount 21706 15 = 7 ∧ acceleratedOrbit 15 21706 = 1451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21706) = 3 ^ 7 * m + 1451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21706.1, data_15_21706.2]

/-- Complete interval computation for depth 15, residue 21707. -/
theorem bounds_15_21707 : exactInterval 15 21707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21707 : oddCount 21707 15 = 5 ∧ acceleratedOrbit 15 21707 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21707) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21707.1, data_15_21707.2]

/-- Complete interval computation for depth 15, residue 21708. -/
theorem bounds_15_21708 : exactInterval 15 21708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21708 : oddCount 21708 15 = 7 ∧ acceleratedOrbit 15 21708 = 1451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21708) = 3 ^ 7 * m + 1451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21708.1, data_15_21708.2]

/-- Complete interval computation for depth 15, residue 21709. -/
theorem bounds_15_21709 : exactInterval 15 21709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21709 : oddCount 21709 15 = 7 ∧ acceleratedOrbit 15 21709 = 1451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21709) = 3 ^ 7 * m + 1451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21709.1, data_15_21709.2]

/-- Complete interval computation for depth 15, residue 21710. -/
theorem bounds_15_21710 : exactInterval 15 21710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21710 : oddCount 21710 15 = 9 ∧ acceleratedOrbit 15 21710 = 13043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21710) = 3 ^ 9 * m + 13043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21710.1, data_15_21710.2]

/-- Complete interval computation for depth 15, residue 21711. -/
theorem bounds_15_21711 : exactInterval 15 21711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21711 : oddCount 21711 15 = 9 ∧ acceleratedOrbit 15 21711 = 13043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21711) = 3 ^ 9 * m + 13043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21711.1, data_15_21711.2]

/-- Complete interval computation for depth 15, residue 21712. -/
theorem bounds_15_21712 : exactInterval 15 21712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21712 : oddCount 21712 15 = 7 ∧ acceleratedOrbit 15 21712 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21712) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21712.1, data_15_21712.2]

/-- Complete interval computation for depth 15, residue 21713. -/
theorem bounds_15_21713 : exactInterval 15 21713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21713 : oddCount 21713 15 = 8 ∧ acceleratedOrbit 15 21713 = 4349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21713) = 3 ^ 8 * m + 4349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21713.1, data_15_21713.2]

/-- Complete interval computation for depth 15, residue 21714. -/
theorem bounds_15_21714 : exactInterval 15 21714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21714 : oddCount 21714 15 = 8 ∧ acceleratedOrbit 15 21714 = 4349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21714) = 3 ^ 8 * m + 4349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21714.1, data_15_21714.2]

/-- Complete interval computation for depth 15, residue 21715. -/
theorem bounds_15_21715 : exactInterval 15 21715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21715 : oddCount 21715 15 = 8 ∧ acceleratedOrbit 15 21715 = 4349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21715) = 3 ^ 8 * m + 4349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21715.1, data_15_21715.2]

/-- Complete interval computation for depth 15, residue 21716. -/
theorem bounds_15_21716 : exactInterval 15 21716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21716 : oddCount 21716 15 = 7 ∧ acceleratedOrbit 15 21716 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21716) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21716.1, data_15_21716.2]

/-- Complete interval computation for depth 15, residue 21717. -/
theorem bounds_15_21717 : exactInterval 15 21717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21717 : oddCount 21717 15 = 7 ∧ acceleratedOrbit 15 21717 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21717) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21717.1, data_15_21717.2]

/-- Complete interval computation for depth 15, residue 21718. -/
theorem bounds_15_21718 : exactInterval 15 21718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21718 : oddCount 21718 15 = 7 ∧ acceleratedOrbit 15 21718 = 1450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21718) = 3 ^ 7 * m + 1450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21718.1, data_15_21718.2]

/-- Complete interval computation for depth 15, residue 21719. -/
theorem bounds_15_21719 : exactInterval 15 21719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21719 : oddCount 21719 15 = 7 ∧ acceleratedOrbit 15 21719 = 1450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21719) = 3 ^ 7 * m + 1450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21719.1, data_15_21719.2]

/-- Complete interval computation for depth 15, residue 21720. -/
theorem bounds_15_21720 : exactInterval 15 21720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21720 : oddCount 21720 15 = 9 ∧ acceleratedOrbit 15 21720 = 13054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21720) = 3 ^ 9 * m + 13054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21720.1, data_15_21720.2]

/-- Complete interval computation for depth 15, residue 21721. -/
theorem bounds_15_21721 : exactInterval 15 21721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21721 : oddCount 21721 15 = 7 ∧ acceleratedOrbit 15 21721 = 1451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21721) = 3 ^ 7 * m + 1451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21721.1, data_15_21721.2]

/-- Complete interval computation for depth 15, residue 21722. -/
theorem bounds_15_21722 : exactInterval 15 21722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21722 : oddCount 21722 15 = 9 ∧ acceleratedOrbit 15 21722 = 13054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21722) = 3 ^ 9 * m + 13054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21722.1, data_15_21722.2]

/-- Complete interval computation for depth 15, residue 21723. -/
theorem bounds_15_21723 : exactInterval 15 21723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21723 : oddCount 21723 15 = 7 ∧ acceleratedOrbit 15 21723 = 1450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21723) = 3 ^ 7 * m + 1450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21723.1, data_15_21723.2]

/-- Complete interval computation for depth 15, residue 21724. -/
theorem bounds_15_21724 : exactInterval 15 21724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21724 : oddCount 21724 15 = 9 ∧ acceleratedOrbit 15 21724 = 13054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21724) = 3 ^ 9 * m + 13054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21724.1, data_15_21724.2]

end Collatz.Research.PassageAtlas.Batch0663
