import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0755

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24707. -/
theorem bounds_15_24707 : exactInterval 15 24707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24707 : oddCount 24707 15 = 6 ∧ acceleratedOrbit 15 24707 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24707) = 3 ^ 6 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24707.1, data_15_24707.2]

/-- Complete interval computation for depth 15, residue 24708. -/
theorem bounds_15_24708 : exactInterval 15 24708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24708 : oddCount 24708 15 = 6 ∧ acceleratedOrbit 15 24708 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24708) = 3 ^ 6 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24708.1, data_15_24708.2]

/-- Complete interval computation for depth 15, residue 24709. -/
theorem bounds_15_24709 : exactInterval 15 24709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24709 : oddCount 24709 15 = 6 ∧ acceleratedOrbit 15 24709 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24709) = 3 ^ 6 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24709.1, data_15_24709.2]

/-- Complete interval computation for depth 15, residue 24710. -/
theorem bounds_15_24710 : exactInterval 15 24710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24710 : oddCount 24710 15 = 6 ∧ acceleratedOrbit 15 24710 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24710) = 3 ^ 6 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24710.1, data_15_24710.2]

/-- Complete interval computation for depth 15, residue 24711. -/
theorem bounds_15_24711 : exactInterval 15 24711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24711 : oddCount 24711 15 = 8 ∧ acceleratedOrbit 15 24711 = 4949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24711) = 3 ^ 8 * m + 4949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24711.1, data_15_24711.2]

/-- Complete interval computation for depth 15, residue 24712. -/
theorem bounds_15_24712 : exactInterval 15 24712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24712 : oddCount 24712 15 = 5 ∧ acceleratedOrbit 15 24712 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24712) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24712.1, data_15_24712.2]

/-- Complete interval computation for depth 15, residue 24713. -/
theorem bounds_15_24713 : exactInterval 15 24713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24713 : oddCount 24713 15 = 11 ∧ acceleratedOrbit 15 24713 = 133613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24713) = 3 ^ 11 * m + 133613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24713.1, data_15_24713.2]

/-- Complete interval computation for depth 15, residue 24714. -/
theorem bounds_15_24714 : exactInterval 15 24714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24714 : oddCount 24714 15 = 5 ∧ acceleratedOrbit 15 24714 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24714) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24714.1, data_15_24714.2]

/-- Complete interval computation for depth 15, residue 24715. -/
theorem bounds_15_24715 : exactInterval 15 24715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24715 : oddCount 24715 15 = 9 ∧ acceleratedOrbit 15 24715 = 14849 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24715) = 3 ^ 9 * m + 14849 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24715.1, data_15_24715.2]

/-- Complete interval computation for depth 15, residue 24716. -/
theorem bounds_15_24716 : exactInterval 15 24716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24716 : oddCount 24716 15 = 5 ∧ acceleratedOrbit 15 24716 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24716) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24716.1, data_15_24716.2]

/-- Complete interval computation for depth 15, residue 24717. -/
theorem bounds_15_24717 : exactInterval 15 24717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24717 : oddCount 24717 15 = 5 ∧ acceleratedOrbit 15 24717 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24717) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24717.1, data_15_24717.2]

/-- Complete interval computation for depth 15, residue 24718. -/
theorem bounds_15_24718 : exactInterval 15 24718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24718 : oddCount 24718 15 = 11 ∧ acceleratedOrbit 15 24718 = 133649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24718) = 3 ^ 11 * m + 133649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24718.1, data_15_24718.2]

/-- Complete interval computation for depth 15, residue 24719. -/
theorem bounds_15_24719 : exactInterval 15 24719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24719 : oddCount 24719 15 = 11 ∧ acceleratedOrbit 15 24719 = 133649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24719) = 3 ^ 11 * m + 133649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24719.1, data_15_24719.2]

/-- Complete interval computation for depth 15, residue 24720. -/
theorem bounds_15_24720 : exactInterval 15 24720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24720 : oddCount 24720 15 = 6 ∧ acceleratedOrbit 15 24720 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24720) = 3 ^ 6 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24720.1, data_15_24720.2]

/-- Complete interval computation for depth 15, residue 24721. -/
theorem bounds_15_24721 : exactInterval 15 24721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24721 : oddCount 24721 15 = 8 ∧ acceleratedOrbit 15 24721 = 4951 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24721) = 3 ^ 8 * m + 4951 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24721.1, data_15_24721.2]

/-- Complete interval computation for depth 15, residue 24722. -/
theorem bounds_15_24722 : exactInterval 15 24722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24722 : oddCount 24722 15 = 8 ∧ acceleratedOrbit 15 24722 = 4951 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24722) = 3 ^ 8 * m + 4951 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24722.1, data_15_24722.2]

/-- Complete interval computation for depth 15, residue 24723. -/
theorem bounds_15_24723 : exactInterval 15 24723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24723 : oddCount 24723 15 = 8 ∧ acceleratedOrbit 15 24723 = 4951 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24723) = 3 ^ 8 * m + 4951 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24723.1, data_15_24723.2]

/-- Complete interval computation for depth 15, residue 24724. -/
theorem bounds_15_24724 : exactInterval 15 24724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24724 : oddCount 24724 15 = 6 ∧ acceleratedOrbit 15 24724 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24724) = 3 ^ 6 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24724.1, data_15_24724.2]

/-- Complete interval computation for depth 15, residue 24725. -/
theorem bounds_15_24725 : exactInterval 15 24725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24725 : oddCount 24725 15 = 6 ∧ acceleratedOrbit 15 24725 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24725) = 3 ^ 6 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24725.1, data_15_24725.2]

/-- Complete interval computation for depth 15, residue 24726. -/
theorem bounds_15_24726 : exactInterval 15 24726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24726 : oddCount 24726 15 = 5 ∧ acceleratedOrbit 15 24726 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24726) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24726.1, data_15_24726.2]

/-- Complete interval computation for depth 15, residue 24727. -/
theorem bounds_15_24727 : exactInterval 15 24727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24727 : oddCount 24727 15 = 5 ∧ acceleratedOrbit 15 24727 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24727) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24727.1, data_15_24727.2]

/-- Complete interval computation for depth 15, residue 24728. -/
theorem bounds_15_24728 : exactInterval 15 24728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24728 : oddCount 24728 15 = 6 ∧ acceleratedOrbit 15 24728 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24728) = 3 ^ 6 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24728.1, data_15_24728.2]

/-- Complete interval computation for depth 15, residue 24729. -/
theorem bounds_15_24729 : exactInterval 15 24729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24729 : oddCount 24729 15 = 7 ∧ acceleratedOrbit 15 24729 = 1651 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24729) = 3 ^ 7 * m + 1651 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24729.1, data_15_24729.2]

/-- Complete interval computation for depth 15, residue 24730. -/
theorem bounds_15_24730 : exactInterval 15 24730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24730 : oddCount 24730 15 = 6 ∧ acceleratedOrbit 15 24730 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24730) = 3 ^ 6 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24730.1, data_15_24730.2]

/-- Complete interval computation for depth 15, residue 24731. -/
theorem bounds_15_24731 : exactInterval 15 24731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24731 : oddCount 24731 15 = 10 ∧ acceleratedOrbit 15 24731 = 44570 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24731) = 3 ^ 10 * m + 44570 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24731.1, data_15_24731.2]

/-- Complete interval computation for depth 15, residue 24732. -/
theorem bounds_15_24732 : exactInterval 15 24732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24732 : oddCount 24732 15 = 8 ∧ acceleratedOrbit 15 24732 = 4954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24732) = 3 ^ 8 * m + 4954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24732.1, data_15_24732.2]

/-- Complete interval computation for depth 15, residue 24733. -/
theorem bounds_15_24733 : exactInterval 15 24733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24733 : oddCount 24733 15 = 8 ∧ acceleratedOrbit 15 24733 = 4954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24733) = 3 ^ 8 * m + 4954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24733.1, data_15_24733.2]

/-- Complete interval computation for depth 15, residue 24734. -/
theorem bounds_15_24734 : exactInterval 15 24734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24734 : oddCount 24734 15 = 8 ∧ acceleratedOrbit 15 24734 = 4954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24734) = 3 ^ 8 * m + 4954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24734.1, data_15_24734.2]

/-- Complete interval computation for depth 15, residue 24735. -/
theorem bounds_15_24735 : exactInterval 15 24735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24735 : oddCount 24735 15 = 11 ∧ acceleratedOrbit 15 24735 = 133726 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24735) = 3 ^ 11 * m + 133726 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24735.1, data_15_24735.2]

/-- Complete interval computation for depth 15, residue 24736. -/
theorem bounds_15_24736 : exactInterval 15 24736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24736 : oddCount 24736 15 = 4 ∧ acceleratedOrbit 15 24736 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24736) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24736.1, data_15_24736.2]

/-- Complete interval computation for depth 15, residue 24737. -/
theorem bounds_15_24737 : exactInterval 15 24737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24737 : oddCount 24737 15 = 9 ∧ acceleratedOrbit 15 24737 = 14861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24737) = 3 ^ 9 * m + 14861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24737.1, data_15_24737.2]

/-- Complete interval computation for depth 15, residue 24738. -/
theorem bounds_15_24738 : exactInterval 15 24738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24738 : oddCount 24738 15 = 6 ∧ acceleratedOrbit 15 24738 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24738) = 3 ^ 6 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24738.1, data_15_24738.2]

end Collatz.Research.PassageAtlas.Batch0755
