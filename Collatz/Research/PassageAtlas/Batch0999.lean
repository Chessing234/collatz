import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0999

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32702. -/
theorem bounds_15_32702 : exactInterval 15 32702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32702 : oddCount 32702 15 = 9 ∧ acceleratedOrbit 15 32702 = 19646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32702) = 3 ^ 9 * m + 19646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32702.1, data_15_32702.2]

/-- Complete interval computation for depth 15, residue 32703. -/
theorem bounds_15_32703 : exactInterval 15 32703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32703 : oddCount 32703 15 = 10 ∧ acceleratedOrbit 15 32703 = 58934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32703) = 3 ^ 10 * m + 58934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32703.1, data_15_32703.2]

/-- Complete interval computation for depth 15, residue 32704. -/
theorem bounds_15_32704 : exactInterval 15 32704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32704 : oddCount 32704 15 = 9 ∧ acceleratedOrbit 15 32704 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32704) = 3 ^ 9 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32704.1, data_15_32704.2]

/-- Complete interval computation for depth 15, residue 32705. -/
theorem bounds_15_32705 : exactInterval 15 32705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32705 : oddCount 32705 15 = 8 ∧ acceleratedOrbit 15 32705 = 6551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32705) = 3 ^ 8 * m + 6551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32705.1, data_15_32705.2]

/-- Complete interval computation for depth 15, residue 32706. -/
theorem bounds_15_32706 : exactInterval 15 32706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32706 : oddCount 32706 15 = 9 ∧ acceleratedOrbit 15 32706 = 19649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32706) = 3 ^ 9 * m + 19649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32706.1, data_15_32706.2]

/-- Complete interval computation for depth 15, residue 32707. -/
theorem bounds_15_32707 : exactInterval 15 32707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32707 : oddCount 32707 15 = 9 ∧ acceleratedOrbit 15 32707 = 19649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32707) = 3 ^ 9 * m + 19649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32707.1, data_15_32707.2]

/-- Complete interval computation for depth 15, residue 32708. -/
theorem bounds_15_32708 : exactInterval 15 32708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32708 : oddCount 32708 15 = 8 ∧ acceleratedOrbit 15 32708 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32708) = 3 ^ 8 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32708.1, data_15_32708.2]

/-- Complete interval computation for depth 15, residue 32709. -/
theorem bounds_15_32709 : exactInterval 15 32709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32709 : oddCount 32709 15 = 8 ∧ acceleratedOrbit 15 32709 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32709) = 3 ^ 8 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32709.1, data_15_32709.2]

/-- Complete interval computation for depth 15, residue 32710. -/
theorem bounds_15_32710 : exactInterval 15 32710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32710 : oddCount 32710 15 = 8 ∧ acceleratedOrbit 15 32710 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32710) = 3 ^ 8 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32710.1, data_15_32710.2]

/-- Complete interval computation for depth 15, residue 32711. -/
theorem bounds_15_32711 : exactInterval 15 32711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32711 : oddCount 32711 15 = 8 ∧ acceleratedOrbit 15 32711 = 6550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32711) = 3 ^ 8 * m + 6550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32711.1, data_15_32711.2]

/-- Complete interval computation for depth 15, residue 32712. -/
theorem bounds_15_32712 : exactInterval 15 32712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32712 : oddCount 32712 15 = 8 ∧ acceleratedOrbit 15 32712 = 6554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32712) = 3 ^ 8 * m + 6554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32712.1, data_15_32712.2]

/-- Complete interval computation for depth 15, residue 32713. -/
theorem bounds_15_32713 : exactInterval 15 32713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32713 : oddCount 32713 15 = 10 ∧ acceleratedOrbit 15 32713 = 58958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32713) = 3 ^ 10 * m + 58958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32713.1, data_15_32713.2]

/-- Complete interval computation for depth 15, residue 32714. -/
theorem bounds_15_32714 : exactInterval 15 32714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32714 : oddCount 32714 15 = 8 ∧ acceleratedOrbit 15 32714 = 6554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32714) = 3 ^ 8 * m + 6554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32714.1, data_15_32714.2]

/-- Complete interval computation for depth 15, residue 32715. -/
theorem bounds_15_32715 : exactInterval 15 32715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32715 : oddCount 32715 15 = 7 ∧ acceleratedOrbit 15 32715 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32715) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32715.1, data_15_32715.2]

/-- Complete interval computation for depth 15, residue 32716. -/
theorem bounds_15_32716 : exactInterval 15 32716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32716 : oddCount 32716 15 = 8 ∧ acceleratedOrbit 15 32716 = 6554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32716) = 3 ^ 8 * m + 6554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32716.1, data_15_32716.2]

/-- Complete interval computation for depth 15, residue 32717. -/
theorem bounds_15_32717 : exactInterval 15 32717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32717 : oddCount 32717 15 = 8 ∧ acceleratedOrbit 15 32717 = 6554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32717) = 3 ^ 8 * m + 6554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32717.1, data_15_32717.2]

/-- Complete interval computation for depth 15, residue 32718. -/
theorem bounds_15_32718 : exactInterval 15 32718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32718 : oddCount 32718 15 = 10 ∧ acceleratedOrbit 15 32718 = 58967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32718) = 3 ^ 10 * m + 58967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32718.1, data_15_32718.2]

/-- Complete interval computation for depth 15, residue 32719. -/
theorem bounds_15_32719 : exactInterval 15 32719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32719 : oddCount 32719 15 = 10 ∧ acceleratedOrbit 15 32719 = 58967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32719) = 3 ^ 10 * m + 58967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32719.1, data_15_32719.2]

/-- Complete interval computation for depth 15, residue 32720. -/
theorem bounds_15_32720 : exactInterval 15 32720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32720 : oddCount 32720 15 = 9 ∧ acceleratedOrbit 15 32720 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32720) = 3 ^ 9 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32720.1, data_15_32720.2]

/-- Complete interval computation for depth 15, residue 32721. -/
theorem bounds_15_32721 : exactInterval 15 32721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32721 : oddCount 32721 15 = 8 ∧ acceleratedOrbit 15 32721 = 6554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32721) = 3 ^ 8 * m + 6554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32721.1, data_15_32721.2]

/-- Complete interval computation for depth 15, residue 32722. -/
theorem bounds_15_32722 : exactInterval 15 32722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32722 : oddCount 32722 15 = 9 ∧ acceleratedOrbit 15 32722 = 19658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32722) = 3 ^ 9 * m + 19658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32722.1, data_15_32722.2]

/-- Complete interval computation for depth 15, residue 32723. -/
theorem bounds_15_32723 : exactInterval 15 32723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32723 : oddCount 32723 15 = 9 ∧ acceleratedOrbit 15 32723 = 19658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32723) = 3 ^ 9 * m + 19658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32723.1, data_15_32723.2]

/-- Complete interval computation for depth 15, residue 32724. -/
theorem bounds_15_32724 : exactInterval 15 32724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32724 : oddCount 32724 15 = 9 ∧ acceleratedOrbit 15 32724 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32724) = 3 ^ 9 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32724.1, data_15_32724.2]

/-- Complete interval computation for depth 15, residue 32725. -/
theorem bounds_15_32725 : exactInterval 15 32725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32725 : oddCount 32725 15 = 9 ∧ acceleratedOrbit 15 32725 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32725) = 3 ^ 9 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32725.1, data_15_32725.2]

/-- Complete interval computation for depth 15, residue 32726. -/
theorem bounds_15_32726 : exactInterval 15 32726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32726 : oddCount 32726 15 = 10 ∧ acceleratedOrbit 15 32726 = 58981 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32726) = 3 ^ 10 * m + 58981 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32726.1, data_15_32726.2]

/-- Complete interval computation for depth 15, residue 32727. -/
theorem bounds_15_32727 : exactInterval 15 32727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32727 : oddCount 32727 15 = 10 ∧ acceleratedOrbit 15 32727 = 58981 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32727) = 3 ^ 10 * m + 58981 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32727.1, data_15_32727.2]

/-- Complete interval computation for depth 15, residue 32728. -/
theorem bounds_15_32728 : exactInterval 15 32728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32728 : oddCount 32728 15 = 8 ∧ acceleratedOrbit 15 32728 = 6556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32728) = 3 ^ 8 * m + 6556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32728.1, data_15_32728.2]

/-- Complete interval computation for depth 15, residue 32729. -/
theorem bounds_15_32729 : exactInterval 15 32729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32729 : oddCount 32729 15 = 8 ∧ acceleratedOrbit 15 32729 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32729) = 3 ^ 8 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32729.1, data_15_32729.2]

/-- Complete interval computation for depth 15, residue 32730. -/
theorem bounds_15_32730 : exactInterval 15 32730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32730 : oddCount 32730 15 = 8 ∧ acceleratedOrbit 15 32730 = 6556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32730) = 3 ^ 8 * m + 6556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32730.1, data_15_32730.2]

/-- Complete interval computation for depth 15, residue 32731. -/
theorem bounds_15_32731 : exactInterval 15 32731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32731 : oddCount 32731 15 = 10 ∧ acceleratedOrbit 15 32731 = 58988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32731) = 3 ^ 10 * m + 58988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32731.1, data_15_32731.2]

/-- Complete interval computation for depth 15, residue 32732. -/
theorem bounds_15_32732 : exactInterval 15 32732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32732 : oddCount 32732 15 = 8 ∧ acceleratedOrbit 15 32732 = 6556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32732) = 3 ^ 8 * m + 6556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32732.1, data_15_32732.2]

/-- Complete interval computation for depth 15, residue 32733. -/
theorem bounds_15_32733 : exactInterval 15 32733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32733 : oddCount 32733 15 = 8 ∧ acceleratedOrbit 15 32733 = 6556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32733) = 3 ^ 8 * m + 6556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32733.1, data_15_32733.2]

/-- Complete interval computation for depth 15, residue 32734. -/
theorem bounds_15_32734 : exactInterval 15 32734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32734 : oddCount 32734 15 = 10 ∧ acceleratedOrbit 15 32734 = 58994 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32734) = 3 ^ 10 * m + 58994 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32734.1, data_15_32734.2]

end Collatz.Research.PassageAtlas.Batch0999
