import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0664

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21725. -/
theorem bounds_15_21725 : exactInterval 15 21725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21725 : oddCount 21725 15 = 9 ∧ acceleratedOrbit 15 21725 = 13054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21725) = 3 ^ 9 * m + 13054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21725.1, data_15_21725.2]

/-- Complete interval computation for depth 15, residue 21726. -/
theorem bounds_15_21726 : exactInterval 15 21726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21726 : oddCount 21726 15 = 9 ∧ acceleratedOrbit 15 21726 = 13052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21726) = 3 ^ 9 * m + 13052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21726.1, data_15_21726.2]

/-- Complete interval computation for depth 15, residue 21727. -/
theorem bounds_15_21727 : exactInterval 15 21727 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21727) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21727 : oddCount 21727 15 = 9 ∧ acceleratedOrbit 15 21727 = 13052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21727) = 3 ^ 9 * m + 13052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21727.1, data_15_21727.2]

/-- Complete interval computation for depth 15, residue 21728. -/
theorem bounds_15_21728 : exactInterval 15 21728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21728 : oddCount 21728 15 = 7 ∧ acceleratedOrbit 15 21728 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21728) = 3 ^ 7 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21728.1, data_15_21728.2]

/-- Complete interval computation for depth 15, residue 21729. -/
theorem bounds_15_21729 : exactInterval 15 21729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21729 : oddCount 21729 15 = 10 ∧ acceleratedOrbit 15 21729 = 39161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21729) = 3 ^ 10 * m + 39161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21729.1, data_15_21729.2]

/-- Complete interval computation for depth 15, residue 21730. -/
theorem bounds_15_21730 : exactInterval 15 21730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21730 : oddCount 21730 15 = 7 ∧ acceleratedOrbit 15 21730 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21730) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21730.1, data_15_21730.2]

/-- Complete interval computation for depth 15, residue 21731. -/
theorem bounds_15_21731 : exactInterval 15 21731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21731 : oddCount 21731 15 = 7 ∧ acceleratedOrbit 15 21731 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21731) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21731.1, data_15_21731.2]

/-- Complete interval computation for depth 15, residue 21732. -/
theorem bounds_15_21732 : exactInterval 15 21732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21732 : oddCount 21732 15 = 9 ∧ acceleratedOrbit 15 21732 = 13061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21732) = 3 ^ 9 * m + 13061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21732.1, data_15_21732.2]

/-- Complete interval computation for depth 15, residue 21733. -/
theorem bounds_15_21733 : exactInterval 15 21733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21733 : oddCount 21733 15 = 9 ∧ acceleratedOrbit 15 21733 = 13061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21733) = 3 ^ 9 * m + 13061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21733.1, data_15_21733.2]

/-- Complete interval computation for depth 15, residue 21734. -/
theorem bounds_15_21734 : exactInterval 15 21734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21734 : oddCount 21734 15 = 9 ∧ acceleratedOrbit 15 21734 = 13061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21734) = 3 ^ 9 * m + 13061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21734.1, data_15_21734.2]

/-- Complete interval computation for depth 15, residue 21735. -/
theorem bounds_15_21735 : exactInterval 15 21735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21735 : oddCount 21735 15 = 10 ∧ acceleratedOrbit 15 21735 = 39170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21735) = 3 ^ 10 * m + 39170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21735.1, data_15_21735.2]

/-- Complete interval computation for depth 15, residue 21736. -/
theorem bounds_15_21736 : exactInterval 15 21736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21736 : oddCount 21736 15 = 7 ∧ acceleratedOrbit 15 21736 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21736) = 3 ^ 7 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21736.1, data_15_21736.2]

/-- Complete interval computation for depth 15, residue 21737. -/
theorem bounds_15_21737 : exactInterval 15 21737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21737 : oddCount 21737 15 = 7 ∧ acceleratedOrbit 15 21737 = 1451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21737) = 3 ^ 7 * m + 1451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21737.1, data_15_21737.2]

/-- Complete interval computation for depth 15, residue 21738. -/
theorem bounds_15_21738 : exactInterval 15 21738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21738 : oddCount 21738 15 = 7 ∧ acceleratedOrbit 15 21738 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21738) = 3 ^ 7 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21738.1, data_15_21738.2]

/-- Complete interval computation for depth 15, residue 21739. -/
theorem bounds_15_21739 : exactInterval 15 21739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21739 : oddCount 21739 15 = 10 ∧ acceleratedOrbit 15 21739 = 39179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21739) = 3 ^ 10 * m + 39179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21739.1, data_15_21739.2]

/-- Complete interval computation for depth 15, residue 21740. -/
theorem bounds_15_21740 : exactInterval 15 21740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21740 : oddCount 21740 15 = 6 ∧ acceleratedOrbit 15 21740 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21740) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21740.1, data_15_21740.2]

/-- Complete interval computation for depth 15, residue 21741. -/
theorem bounds_15_21741 : exactInterval 15 21741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21741 : oddCount 21741 15 = 6 ∧ acceleratedOrbit 15 21741 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21741) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21741.1, data_15_21741.2]

/-- Complete interval computation for depth 15, residue 21742. -/
theorem bounds_15_21742 : exactInterval 15 21742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21742 : oddCount 21742 15 = 6 ∧ acceleratedOrbit 15 21742 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21742) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21742.1, data_15_21742.2]

/-- Complete interval computation for depth 15, residue 21743. -/
theorem bounds_15_21743 : exactInterval 15 21743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21743 : oddCount 21743 15 = 13 ∧ acceleratedOrbit 15 21743 = 1057961 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21743) = 3 ^ 13 * m + 1057961 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21743.1, data_15_21743.2]

/-- Complete interval computation for depth 15, residue 21744. -/
theorem bounds_15_21744 : exactInterval 15 21744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21744 : oddCount 21744 15 = 7 ∧ acceleratedOrbit 15 21744 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21744) = 3 ^ 7 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21744.1, data_15_21744.2]

/-- Complete interval computation for depth 15, residue 21745. -/
theorem bounds_15_21745 : exactInterval 15 21745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21745 : oddCount 21745 15 = 7 ∧ acceleratedOrbit 15 21745 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21745) = 3 ^ 7 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21745.1, data_15_21745.2]

/-- Complete interval computation for depth 15, residue 21746. -/
theorem bounds_15_21746 : exactInterval 15 21746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21746 : oddCount 21746 15 = 9 ∧ acceleratedOrbit 15 21746 = 13067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21746) = 3 ^ 9 * m + 13067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21746.1, data_15_21746.2]

/-- Complete interval computation for depth 15, residue 21747. -/
theorem bounds_15_21747 : exactInterval 15 21747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21747 : oddCount 21747 15 = 9 ∧ acceleratedOrbit 15 21747 = 13067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21747) = 3 ^ 9 * m + 13067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21747.1, data_15_21747.2]

/-- Complete interval computation for depth 15, residue 21748. -/
theorem bounds_15_21748 : exactInterval 15 21748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21748 : oddCount 21748 15 = 7 ∧ acceleratedOrbit 15 21748 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21748) = 3 ^ 7 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21748.1, data_15_21748.2]

/-- Complete interval computation for depth 15, residue 21749. -/
theorem bounds_15_21749 : exactInterval 15 21749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21749 : oddCount 21749 15 = 7 ∧ acceleratedOrbit 15 21749 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21749) = 3 ^ 7 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21749.1, data_15_21749.2]

/-- Complete interval computation for depth 15, residue 21750. -/
theorem bounds_15_21750 : exactInterval 15 21750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21750 : oddCount 21750 15 = 6 ∧ acceleratedOrbit 15 21750 = 484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21750) = 3 ^ 6 * m + 484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21750.1, data_15_21750.2]

/-- Complete interval computation for depth 15, residue 21751. -/
theorem bounds_15_21751 : exactInterval 15 21751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21751 : oddCount 21751 15 = 6 ∧ acceleratedOrbit 15 21751 = 484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21751) = 3 ^ 6 * m + 484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21751.1, data_15_21751.2]

/-- Complete interval computation for depth 15, residue 21752. -/
theorem bounds_15_21752 : exactInterval 15 21752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21752 : oddCount 21752 15 = 8 ∧ acceleratedOrbit 15 21752 = 4357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21752) = 3 ^ 8 * m + 4357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21752.1, data_15_21752.2]

/-- Complete interval computation for depth 15, residue 21753. -/
theorem bounds_15_21753 : exactInterval 15 21753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21753 : oddCount 21753 15 = 6 ∧ acceleratedOrbit 15 21753 = 484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21753) = 3 ^ 6 * m + 484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21753.1, data_15_21753.2]

/-- Complete interval computation for depth 15, residue 21754. -/
theorem bounds_15_21754 : exactInterval 15 21754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21754 : oddCount 21754 15 = 8 ∧ acceleratedOrbit 15 21754 = 4357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21754) = 3 ^ 8 * m + 4357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21754.1, data_15_21754.2]

/-- Complete interval computation for depth 15, residue 21755. -/
theorem bounds_15_21755 : exactInterval 15 21755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21755 : oddCount 21755 15 = 9 ∧ acceleratedOrbit 15 21755 = 13069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21755) = 3 ^ 9 * m + 13069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21755.1, data_15_21755.2]

/-- Complete interval computation for depth 15, residue 21756. -/
theorem bounds_15_21756 : exactInterval 15 21756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21756 : oddCount 21756 15 = 8 ∧ acceleratedOrbit 15 21756 = 4357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21756) = 3 ^ 8 * m + 4357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21756.1, data_15_21756.2]

end Collatz.Research.PassageAtlas.Batch0664
