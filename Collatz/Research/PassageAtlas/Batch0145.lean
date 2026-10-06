import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0145

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4718. -/
theorem bounds_15_4718 : exactInterval 15 4718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4718 : oddCount 4718 15 = 9 ∧ acceleratedOrbit 15 4718 = 2837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4718) = 3 ^ 9 * m + 2837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4718.1, data_15_4718.2]

/-- Complete interval computation for depth 15, residue 4719. -/
theorem bounds_15_4719 : exactInterval 15 4719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4719 : oddCount 4719 15 = 10 ∧ acceleratedOrbit 15 4719 = 8507 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4719) = 3 ^ 10 * m + 8507 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4719.1, data_15_4719.2]

/-- Complete interval computation for depth 15, residue 4720. -/
theorem bounds_15_4720 : exactInterval 15 4720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4720 : oddCount 4720 15 = 7 ∧ acceleratedOrbit 15 4720 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4720) = 3 ^ 7 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4720.1, data_15_4720.2]

/-- Complete interval computation for depth 15, residue 4721. -/
theorem bounds_15_4721 : exactInterval 15 4721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4721 : oddCount 4721 15 = 6 ∧ acceleratedOrbit 15 4721 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4721) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4721.1, data_15_4721.2]

/-- Complete interval computation for depth 15, residue 4722. -/
theorem bounds_15_4722 : exactInterval 15 4722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4722 : oddCount 4722 15 = 8 ∧ acceleratedOrbit 15 4722 = 947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4722) = 3 ^ 8 * m + 947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4722.1, data_15_4722.2]

/-- Complete interval computation for depth 15, residue 4723. -/
theorem bounds_15_4723 : exactInterval 15 4723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4723 : oddCount 4723 15 = 8 ∧ acceleratedOrbit 15 4723 = 947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4723) = 3 ^ 8 * m + 947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4723.1, data_15_4723.2]

/-- Complete interval computation for depth 15, residue 4724. -/
theorem bounds_15_4724 : exactInterval 15 4724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4724 : oddCount 4724 15 = 7 ∧ acceleratedOrbit 15 4724 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4724) = 3 ^ 7 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4724.1, data_15_4724.2]

/-- Complete interval computation for depth 15, residue 4725. -/
theorem bounds_15_4725 : exactInterval 15 4725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4725 : oddCount 4725 15 = 7 ∧ acceleratedOrbit 15 4725 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4725) = 3 ^ 7 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4725.1, data_15_4725.2]

/-- Complete interval computation for depth 15, residue 4726. -/
theorem bounds_15_4726 : exactInterval 15 4726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4726 : oddCount 4726 15 = 7 ∧ acceleratedOrbit 15 4726 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4726) = 3 ^ 7 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4726.1, data_15_4726.2]

/-- Complete interval computation for depth 15, residue 4727. -/
theorem bounds_15_4727 : exactInterval 15 4727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4727 : oddCount 4727 15 = 7 ∧ acceleratedOrbit 15 4727 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4727) = 3 ^ 7 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4727.1, data_15_4727.2]

/-- Complete interval computation for depth 15, residue 4728. -/
theorem bounds_15_4728 : exactInterval 15 4728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4728 : oddCount 4728 15 = 7 ∧ acceleratedOrbit 15 4728 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4728) = 3 ^ 7 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4728.1, data_15_4728.2]

/-- Complete interval computation for depth 15, residue 4729. -/
theorem bounds_15_4729 : exactInterval 15 4729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4729 : oddCount 4729 15 = 7 ∧ acceleratedOrbit 15 4729 = 316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4729) = 3 ^ 7 * m + 316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4729.1, data_15_4729.2]

/-- Complete interval computation for depth 15, residue 4730. -/
theorem bounds_15_4730 : exactInterval 15 4730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4730 : oddCount 4730 15 = 7 ∧ acceleratedOrbit 15 4730 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4730) = 3 ^ 7 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4730.1, data_15_4730.2]

/-- Complete interval computation for depth 15, residue 4731. -/
theorem bounds_15_4731 : exactInterval 15 4731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4731 : oddCount 4731 15 = 7 ∧ acceleratedOrbit 15 4731 = 316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4731) = 3 ^ 7 * m + 316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4731.1, data_15_4731.2]

/-- Complete interval computation for depth 15, residue 4732. -/
theorem bounds_15_4732 : exactInterval 15 4732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4732 : oddCount 4732 15 = 9 ∧ acceleratedOrbit 15 4732 = 2845 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4732) = 3 ^ 9 * m + 2845 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4732.1, data_15_4732.2]

/-- Complete interval computation for depth 15, residue 4733. -/
theorem bounds_15_4733 : exactInterval 15 4733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4733 : oddCount 4733 15 = 9 ∧ acceleratedOrbit 15 4733 = 2845 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4733) = 3 ^ 9 * m + 2845 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4733.1, data_15_4733.2]

/-- Complete interval computation for depth 15, residue 4734. -/
theorem bounds_15_4734 : exactInterval 15 4734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4734 : oddCount 4734 15 = 9 ∧ acceleratedOrbit 15 4734 = 2845 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4734) = 3 ^ 9 * m + 2845 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4734.1, data_15_4734.2]

/-- Complete interval computation for depth 15, residue 4735. -/
theorem bounds_15_4735 : exactInterval 15 4735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4735 : oddCount 4735 15 = 11 ∧ acceleratedOrbit 15 4735 = 25604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4735) = 3 ^ 11 * m + 25604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4735.1, data_15_4735.2]

/-- Complete interval computation for depth 15, residue 4736. -/
theorem bounds_15_4736 : exactInterval 15 4736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4736 : oddCount 4736 15 = 4 ∧ acceleratedOrbit 15 4736 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4736) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4736.1, data_15_4736.2]

/-- Complete interval computation for depth 15, residue 4737. -/
theorem bounds_15_4737 : exactInterval 15 4737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4737 : oddCount 4737 15 = 9 ∧ acceleratedOrbit 15 4737 = 2848 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4737) = 3 ^ 9 * m + 2848 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4737.1, data_15_4737.2]

/-- Complete interval computation for depth 15, residue 4738. -/
theorem bounds_15_4738 : exactInterval 15 4738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4738 : oddCount 4738 15 = 6 ∧ acceleratedOrbit 15 4738 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4738) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4738.1, data_15_4738.2]

/-- Complete interval computation for depth 15, residue 4739. -/
theorem bounds_15_4739 : exactInterval 15 4739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4739 : oddCount 4739 15 = 6 ∧ acceleratedOrbit 15 4739 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4739) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4739.1, data_15_4739.2]

/-- Complete interval computation for depth 15, residue 4740. -/
theorem bounds_15_4740 : exactInterval 15 4740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4740 : oddCount 4740 15 = 9 ∧ acceleratedOrbit 15 4740 = 2855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4740) = 3 ^ 9 * m + 2855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4740.1, data_15_4740.2]

/-- Complete interval computation for depth 15, residue 4741. -/
theorem bounds_15_4741 : exactInterval 15 4741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4741 : oddCount 4741 15 = 9 ∧ acceleratedOrbit 15 4741 = 2855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4741) = 3 ^ 9 * m + 2855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4741.1, data_15_4741.2]

/-- Complete interval computation for depth 15, residue 4742. -/
theorem bounds_15_4742 : exactInterval 15 4742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4742 : oddCount 4742 15 = 9 ∧ acceleratedOrbit 15 4742 = 2855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4742) = 3 ^ 9 * m + 2855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4742.1, data_15_4742.2]

/-- Complete interval computation for depth 15, residue 4743. -/
theorem bounds_15_4743 : exactInterval 15 4743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4743 : oddCount 4743 15 = 7 ∧ acceleratedOrbit 15 4743 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4743) = 3 ^ 7 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4743.1, data_15_4743.2]

/-- Complete interval computation for depth 15, residue 4744. -/
theorem bounds_15_4744 : exactInterval 15 4744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4744 : oddCount 4744 15 = 7 ∧ acceleratedOrbit 15 4744 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4744) = 3 ^ 7 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4744.1, data_15_4744.2]

/-- Complete interval computation for depth 15, residue 4745. -/
theorem bounds_15_4745 : exactInterval 15 4745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4745 : oddCount 4745 15 = 9 ∧ acceleratedOrbit 15 4745 = 2852 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4745) = 3 ^ 9 * m + 2852 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4745.1, data_15_4745.2]

/-- Complete interval computation for depth 15, residue 4746. -/
theorem bounds_15_4746 : exactInterval 15 4746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4746 : oddCount 4746 15 = 7 ∧ acceleratedOrbit 15 4746 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4746) = 3 ^ 7 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4746.1, data_15_4746.2]

/-- Complete interval computation for depth 15, residue 4747. -/
theorem bounds_15_4747 : exactInterval 15 4747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4747 : oddCount 4747 15 = 9 ∧ acceleratedOrbit 15 4747 = 2855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4747) = 3 ^ 9 * m + 2855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4747.1, data_15_4747.2]

/-- Complete interval computation for depth 15, residue 4748. -/
theorem bounds_15_4748 : exactInterval 15 4748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4748 : oddCount 4748 15 = 7 ∧ acceleratedOrbit 15 4748 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4748) = 3 ^ 7 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4748.1, data_15_4748.2]

/-- Complete interval computation for depth 15, residue 4749. -/
theorem bounds_15_4749 : exactInterval 15 4749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4749 : oddCount 4749 15 = 7 ∧ acceleratedOrbit 15 4749 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4749) = 3 ^ 7 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4749.1, data_15_4749.2]

/-- Complete interval computation for depth 15, residue 4750. -/
theorem bounds_15_4750 : exactInterval 15 4750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4750 : oddCount 4750 15 = 11 ∧ acceleratedOrbit 15 4750 = 25697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4750) = 3 ^ 11 * m + 25697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4750.1, data_15_4750.2]

end Collatz.Research.PassageAtlas.Batch0145
