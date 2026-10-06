import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0877

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28704. -/
theorem bounds_15_28704 : exactInterval 15 28704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28704 : oddCount 28704 15 = 6 ∧ acceleratedOrbit 15 28704 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28704) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28704.1, data_15_28704.2]

/-- Complete interval computation for depth 15, residue 28705. -/
theorem bounds_15_28705 : exactInterval 15 28705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28705 : oddCount 28705 15 = 9 ∧ acceleratedOrbit 15 28705 = 17246 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28705) = 3 ^ 9 * m + 17246 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28705.1, data_15_28705.2]

/-- Complete interval computation for depth 15, residue 28706. -/
theorem bounds_15_28706 : exactInterval 15 28706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28706 : oddCount 28706 15 = 4 ∧ acceleratedOrbit 15 28706 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28706) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28706.1, data_15_28706.2]

/-- Complete interval computation for depth 15, residue 28707. -/
theorem bounds_15_28707 : exactInterval 15 28707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28707 : oddCount 28707 15 = 4 ∧ acceleratedOrbit 15 28707 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28707) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28707.1, data_15_28707.2]

/-- Complete interval computation for depth 15, residue 28708. -/
theorem bounds_15_28708 : exactInterval 15 28708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28708 : oddCount 28708 15 = 9 ∧ acceleratedOrbit 15 28708 = 17252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28708) = 3 ^ 9 * m + 17252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28708.1, data_15_28708.2]

/-- Complete interval computation for depth 15, residue 28709. -/
theorem bounds_15_28709 : exactInterval 15 28709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28709 : oddCount 28709 15 = 9 ∧ acceleratedOrbit 15 28709 = 17252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28709) = 3 ^ 9 * m + 17252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28709.1, data_15_28709.2]

/-- Complete interval computation for depth 15, residue 28710. -/
theorem bounds_15_28710 : exactInterval 15 28710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28710 : oddCount 28710 15 = 9 ∧ acceleratedOrbit 15 28710 = 17252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28710) = 3 ^ 9 * m + 17252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28710.1, data_15_28710.2]

/-- Complete interval computation for depth 15, residue 28711. -/
theorem bounds_15_28711 : exactInterval 15 28711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28711 : oddCount 28711 15 = 9 ∧ acceleratedOrbit 15 28711 = 17248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28711) = 3 ^ 9 * m + 17248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28711.1, data_15_28711.2]

/-- Complete interval computation for depth 15, residue 28712. -/
theorem bounds_15_28712 : exactInterval 15 28712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28712 : oddCount 28712 15 = 6 ∧ acceleratedOrbit 15 28712 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28712) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28712.1, data_15_28712.2]

/-- Complete interval computation for depth 15, residue 28713. -/
theorem bounds_15_28713 : exactInterval 15 28713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28713 : oddCount 28713 15 = 11 ∧ acceleratedOrbit 15 28713 = 155236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28713) = 3 ^ 11 * m + 155236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28713.1, data_15_28713.2]

/-- Complete interval computation for depth 15, residue 28714. -/
theorem bounds_15_28714 : exactInterval 15 28714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28714 : oddCount 28714 15 = 6 ∧ acceleratedOrbit 15 28714 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28714) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28714.1, data_15_28714.2]

/-- Complete interval computation for depth 15, residue 28715. -/
theorem bounds_15_28715 : exactInterval 15 28715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28715 : oddCount 28715 15 = 10 ∧ acceleratedOrbit 15 28715 = 51758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28715) = 3 ^ 10 * m + 51758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28715.1, data_15_28715.2]

/-- Complete interval computation for depth 15, residue 28716. -/
theorem bounds_15_28716 : exactInterval 15 28716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28716 : oddCount 28716 15 = 4 ∧ acceleratedOrbit 15 28716 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28716) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28716.1, data_15_28716.2]

/-- Complete interval computation for depth 15, residue 28717. -/
theorem bounds_15_28717 : exactInterval 15 28717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28717 : oddCount 28717 15 = 4 ∧ acceleratedOrbit 15 28717 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28717) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28717.1, data_15_28717.2]

/-- Complete interval computation for depth 15, residue 28718. -/
theorem bounds_15_28718 : exactInterval 15 28718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28718 : oddCount 28718 15 = 4 ∧ acceleratedOrbit 15 28718 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28718) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28718.1, data_15_28718.2]

/-- Complete interval computation for depth 15, residue 28719. -/
theorem bounds_15_28719 : exactInterval 15 28719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28719 : oddCount 28719 15 = 11 ∧ acceleratedOrbit 15 28719 = 155267 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28719) = 3 ^ 11 * m + 155267 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28719.1, data_15_28719.2]

/-- Complete interval computation for depth 15, residue 28720. -/
theorem bounds_15_28720 : exactInterval 15 28720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28720 : oddCount 28720 15 = 6 ∧ acceleratedOrbit 15 28720 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28720) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28720.1, data_15_28720.2]

/-- Complete interval computation for depth 15, residue 28721. -/
theorem bounds_15_28721 : exactInterval 15 28721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28721 : oddCount 28721 15 = 8 ∧ acceleratedOrbit 15 28721 = 5753 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28721) = 3 ^ 8 * m + 5753 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28721.1, data_15_28721.2]

/-- Complete interval computation for depth 15, residue 28722. -/
theorem bounds_15_28722 : exactInterval 15 28722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28722 : oddCount 28722 15 = 8 ∧ acceleratedOrbit 15 28722 = 5753 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28722) = 3 ^ 8 * m + 5753 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28722.1, data_15_28722.2]

/-- Complete interval computation for depth 15, residue 28723. -/
theorem bounds_15_28723 : exactInterval 15 28723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28723 : oddCount 28723 15 = 8 ∧ acceleratedOrbit 15 28723 = 5753 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28723) = 3 ^ 8 * m + 5753 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28723.1, data_15_28723.2]

/-- Complete interval computation for depth 15, residue 28724. -/
theorem bounds_15_28724 : exactInterval 15 28724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28724 : oddCount 28724 15 = 6 ∧ acceleratedOrbit 15 28724 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28724) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28724.1, data_15_28724.2]

/-- Complete interval computation for depth 15, residue 28725. -/
theorem bounds_15_28725 : exactInterval 15 28725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28725 : oddCount 28725 15 = 6 ∧ acceleratedOrbit 15 28725 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28725) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28725.1, data_15_28725.2]

/-- Complete interval computation for depth 15, residue 28726. -/
theorem bounds_15_28726 : exactInterval 15 28726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28726 : oddCount 28726 15 = 9 ∧ acceleratedOrbit 15 28726 = 17257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28726) = 3 ^ 9 * m + 17257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28726.1, data_15_28726.2]

/-- Complete interval computation for depth 15, residue 28727. -/
theorem bounds_15_28727 : exactInterval 15 28727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28727 : oddCount 28727 15 = 9 ∧ acceleratedOrbit 15 28727 = 17257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28727) = 3 ^ 9 * m + 17257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28727.1, data_15_28727.2]

/-- Complete interval computation for depth 15, residue 28728. -/
theorem bounds_15_28728 : exactInterval 15 28728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28728 : oddCount 28728 15 = 7 ∧ acceleratedOrbit 15 28728 = 1919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28728) = 3 ^ 7 * m + 1919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28728.1, data_15_28728.2]

/-- Complete interval computation for depth 15, residue 28729. -/
theorem bounds_15_28729 : exactInterval 15 28729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28729 : oddCount 28729 15 = 7 ∧ acceleratedOrbit 15 28729 = 1918 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28729) = 3 ^ 7 * m + 1918 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28729.1, data_15_28729.2]

/-- Complete interval computation for depth 15, residue 28730. -/
theorem bounds_15_28730 : exactInterval 15 28730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28730 : oddCount 28730 15 = 7 ∧ acceleratedOrbit 15 28730 = 1919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28730) = 3 ^ 7 * m + 1919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28730.1, data_15_28730.2]

/-- Complete interval computation for depth 15, residue 28731. -/
theorem bounds_15_28731 : exactInterval 15 28731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28731 : oddCount 28731 15 = 7 ∧ acceleratedOrbit 15 28731 = 1918 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28731) = 3 ^ 7 * m + 1918 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28731.1, data_15_28731.2]

/-- Complete interval computation for depth 15, residue 28732. -/
theorem bounds_15_28732 : exactInterval 15 28732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28732 : oddCount 28732 15 = 7 ∧ acceleratedOrbit 15 28732 = 1919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28732) = 3 ^ 7 * m + 1919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28732.1, data_15_28732.2]

/-- Complete interval computation for depth 15, residue 28733. -/
theorem bounds_15_28733 : exactInterval 15 28733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28733 : oddCount 28733 15 = 7 ∧ acceleratedOrbit 15 28733 = 1919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28733) = 3 ^ 7 * m + 1919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28733.1, data_15_28733.2]

/-- Complete interval computation for depth 15, residue 28734. -/
theorem bounds_15_28734 : exactInterval 15 28734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28734 : oddCount 28734 15 = 10 ∧ acceleratedOrbit 15 28734 = 51785 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28734) = 3 ^ 10 * m + 51785 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28734.1, data_15_28734.2]

/-- Complete interval computation for depth 15, residue 28735. -/
theorem bounds_15_28735 : exactInterval 15 28735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28735 : oddCount 28735 15 = 10 ∧ acceleratedOrbit 15 28735 = 51785 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28735) = 3 ^ 10 * m + 51785 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28735.1, data_15_28735.2]

/-- Complete interval computation for depth 15, residue 28736. -/
theorem bounds_15_28736 : exactInterval 15 28736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28736 : oddCount 28736 15 = 5 ∧ acceleratedOrbit 15 28736 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28736) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28736.1, data_15_28736.2]

end Collatz.Research.PassageAtlas.Batch0877
