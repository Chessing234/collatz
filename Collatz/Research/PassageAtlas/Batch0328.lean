import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0328

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10715. -/
theorem bounds_15_10715 : exactInterval 15 10715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10715 : oddCount 10715 15 = 9 ∧ acceleratedOrbit 15 10715 = 6439 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10715) = 3 ^ 9 * m + 6439 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10715.1, data_15_10715.2]

/-- Complete interval computation for depth 15, residue 10716. -/
theorem bounds_15_10716 : exactInterval 15 10716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10716 : oddCount 10716 15 = 5 ∧ acceleratedOrbit 15 10716 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10716) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10716.1, data_15_10716.2]

/-- Complete interval computation for depth 15, residue 10717. -/
theorem bounds_15_10717 : exactInterval 15 10717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10717 : oddCount 10717 15 = 5 ∧ acceleratedOrbit 15 10717 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10717) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10717.1, data_15_10717.2]

/-- Complete interval computation for depth 15, residue 10718. -/
theorem bounds_15_10718 : exactInterval 15 10718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10718 : oddCount 10718 15 = 12 ∧ acceleratedOrbit 15 10718 = 173866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10718) = 3 ^ 12 * m + 173866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10718.1, data_15_10718.2]

/-- Complete interval computation for depth 15, residue 10719. -/
theorem bounds_15_10719 : exactInterval 15 10719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10719 : oddCount 10719 15 = 12 ∧ acceleratedOrbit 15 10719 = 173866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10719) = 3 ^ 12 * m + 173866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10719.1, data_15_10719.2]

/-- Complete interval computation for depth 15, residue 10720. -/
theorem bounds_15_10720 : exactInterval 15 10720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10720 : oddCount 10720 15 = 7 ∧ acceleratedOrbit 15 10720 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10720) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10720.1, data_15_10720.2]

/-- Complete interval computation for depth 15, residue 10721. -/
theorem bounds_15_10721 : exactInterval 15 10721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10721 : oddCount 10721 15 = 9 ∧ acceleratedOrbit 15 10721 = 6443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10721) = 3 ^ 9 * m + 6443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10721.1, data_15_10721.2]

/-- Complete interval computation for depth 15, residue 10722. -/
theorem bounds_15_10722 : exactInterval 15 10722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10722 : oddCount 10722 15 = 7 ∧ acceleratedOrbit 15 10722 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10722) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10722.1, data_15_10722.2]

/-- Complete interval computation for depth 15, residue 10723. -/
theorem bounds_15_10723 : exactInterval 15 10723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10723 : oddCount 10723 15 = 7 ∧ acceleratedOrbit 15 10723 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10723) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10723.1, data_15_10723.2]

/-- Complete interval computation for depth 15, residue 10724. -/
theorem bounds_15_10724 : exactInterval 15 10724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10724 : oddCount 10724 15 = 8 ∧ acceleratedOrbit 15 10724 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10724) = 3 ^ 8 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10724.1, data_15_10724.2]

/-- Complete interval computation for depth 15, residue 10725. -/
theorem bounds_15_10725 : exactInterval 15 10725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10725 : oddCount 10725 15 = 8 ∧ acceleratedOrbit 15 10725 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10725) = 3 ^ 8 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10725.1, data_15_10725.2]

/-- Complete interval computation for depth 15, residue 10726. -/
theorem bounds_15_10726 : exactInterval 15 10726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10726 : oddCount 10726 15 = 8 ∧ acceleratedOrbit 15 10726 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10726) = 3 ^ 8 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10726.1, data_15_10726.2]

/-- Complete interval computation for depth 15, residue 10727. -/
theorem bounds_15_10727 : exactInterval 15 10727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10727 : oddCount 10727 15 = 10 ∧ acceleratedOrbit 15 10727 = 19334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10727) = 3 ^ 10 * m + 19334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10727.1, data_15_10727.2]

/-- Complete interval computation for depth 15, residue 10728. -/
theorem bounds_15_10728 : exactInterval 15 10728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10728 : oddCount 10728 15 = 7 ∧ acceleratedOrbit 15 10728 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10728) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10728.1, data_15_10728.2]

/-- Complete interval computation for depth 15, residue 10729. -/
theorem bounds_15_10729 : exactInterval 15 10729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10729 : oddCount 10729 15 = 9 ∧ acceleratedOrbit 15 10729 = 6446 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10729) = 3 ^ 9 * m + 6446 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10729.1, data_15_10729.2]

/-- Complete interval computation for depth 15, residue 10730. -/
theorem bounds_15_10730 : exactInterval 15 10730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10730 : oddCount 10730 15 = 7 ∧ acceleratedOrbit 15 10730 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10730) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10730.1, data_15_10730.2]

/-- Complete interval computation for depth 15, residue 10731. -/
theorem bounds_15_10731 : exactInterval 15 10731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10731 : oddCount 10731 15 = 8 ∧ acceleratedOrbit 15 10731 = 2149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10731) = 3 ^ 8 * m + 2149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10731.1, data_15_10731.2]

/-- Complete interval computation for depth 15, residue 10732. -/
theorem bounds_15_10732 : exactInterval 15 10732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10732 : oddCount 10732 15 = 6 ∧ acceleratedOrbit 15 10732 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10732) = 3 ^ 6 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10732.1, data_15_10732.2]

/-- Complete interval computation for depth 15, residue 10733. -/
theorem bounds_15_10733 : exactInterval 15 10733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10733 : oddCount 10733 15 = 6 ∧ acceleratedOrbit 15 10733 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10733) = 3 ^ 6 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10733.1, data_15_10733.2]

/-- Complete interval computation for depth 15, residue 10734. -/
theorem bounds_15_10734 : exactInterval 15 10734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10734 : oddCount 10734 15 = 6 ∧ acceleratedOrbit 15 10734 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10734) = 3 ^ 6 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10734.1, data_15_10734.2]

/-- Complete interval computation for depth 15, residue 10735. -/
theorem bounds_15_10735 : exactInterval 15 10735 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10735) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10735 : oddCount 10735 15 = 9 ∧ acceleratedOrbit 15 10735 = 6449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10735) = 3 ^ 9 * m + 6449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10735.1, data_15_10735.2]

/-- Complete interval computation for depth 15, residue 10736. -/
theorem bounds_15_10736 : exactInterval 15 10736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10736 : oddCount 10736 15 = 8 ∧ acceleratedOrbit 15 10736 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10736) = 3 ^ 8 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10736.1, data_15_10736.2]

/-- Complete interval computation for depth 15, residue 10737. -/
theorem bounds_15_10737 : exactInterval 15 10737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10737 : oddCount 10737 15 = 7 ∧ acceleratedOrbit 15 10737 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10737) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10737.1, data_15_10737.2]

/-- Complete interval computation for depth 15, residue 10738. -/
theorem bounds_15_10738 : exactInterval 15 10738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10738 : oddCount 10738 15 = 6 ∧ acceleratedOrbit 15 10738 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10738) = 3 ^ 6 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10738.1, data_15_10738.2]

/-- Complete interval computation for depth 15, residue 10739. -/
theorem bounds_15_10739 : exactInterval 15 10739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10739 : oddCount 10739 15 = 6 ∧ acceleratedOrbit 15 10739 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10739) = 3 ^ 6 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10739.1, data_15_10739.2]

/-- Complete interval computation for depth 15, residue 10740. -/
theorem bounds_15_10740 : exactInterval 15 10740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10740 : oddCount 10740 15 = 8 ∧ acceleratedOrbit 15 10740 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10740) = 3 ^ 8 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10740.1, data_15_10740.2]

/-- Complete interval computation for depth 15, residue 10741. -/
theorem bounds_15_10741 : exactInterval 15 10741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10741 : oddCount 10741 15 = 8 ∧ acceleratedOrbit 15 10741 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10741) = 3 ^ 8 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10741.1, data_15_10741.2]

/-- Complete interval computation for depth 15, residue 10742. -/
theorem bounds_15_10742 : exactInterval 15 10742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10742 : oddCount 10742 15 = 9 ∧ acceleratedOrbit 15 10742 = 6455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10742) = 3 ^ 9 * m + 6455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10742.1, data_15_10742.2]

/-- Complete interval computation for depth 15, residue 10743. -/
theorem bounds_15_10743 : exactInterval 15 10743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10743 : oddCount 10743 15 = 9 ∧ acceleratedOrbit 15 10743 = 6455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10743) = 3 ^ 9 * m + 6455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10743.1, data_15_10743.2]

/-- Complete interval computation for depth 15, residue 10744. -/
theorem bounds_15_10744 : exactInterval 15 10744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10744 : oddCount 10744 15 = 8 ∧ acceleratedOrbit 15 10744 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10744) = 3 ^ 8 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10744.1, data_15_10744.2]

/-- Complete interval computation for depth 15, residue 10745. -/
theorem bounds_15_10745 : exactInterval 15 10745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10745 : oddCount 10745 15 = 8 ∧ acceleratedOrbit 15 10745 = 2152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10745) = 3 ^ 8 * m + 2152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10745.1, data_15_10745.2]

/-- Complete interval computation for depth 15, residue 10746. -/
theorem bounds_15_10746 : exactInterval 15 10746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10746 : oddCount 10746 15 = 8 ∧ acceleratedOrbit 15 10746 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10746) = 3 ^ 8 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10746.1, data_15_10746.2]

end Collatz.Research.PassageAtlas.Batch0328
