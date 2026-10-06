import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0633

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20709. -/
theorem bounds_15_20709 : exactInterval 15 20709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20709 : oddCount 20709 15 = 6 ∧ acceleratedOrbit 15 20709 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20709) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20709.1, data_15_20709.2]

/-- Complete interval computation for depth 15, residue 20710. -/
theorem bounds_15_20710 : exactInterval 15 20710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20710 : oddCount 20710 15 = 6 ∧ acceleratedOrbit 15 20710 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20710) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20710.1, data_15_20710.2]

/-- Complete interval computation for depth 15, residue 20711. -/
theorem bounds_15_20711 : exactInterval 15 20711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20711 : oddCount 20711 15 = 9 ∧ acceleratedOrbit 15 20711 = 12442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20711) = 3 ^ 9 * m + 12442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20711.1, data_15_20711.2]

/-- Complete interval computation for depth 15, residue 20712. -/
theorem bounds_15_20712 : exactInterval 15 20712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20712 : oddCount 20712 15 = 5 ∧ acceleratedOrbit 15 20712 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20712) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20712.1, data_15_20712.2]

/-- Complete interval computation for depth 15, residue 20713. -/
theorem bounds_15_20713 : exactInterval 15 20713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20713 : oddCount 20713 15 = 10 ∧ acceleratedOrbit 15 20713 = 37331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20713) = 3 ^ 10 * m + 37331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20713.1, data_15_20713.2]

/-- Complete interval computation for depth 15, residue 20714. -/
theorem bounds_15_20714 : exactInterval 15 20714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20714 : oddCount 20714 15 = 5 ∧ acceleratedOrbit 15 20714 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20714) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20714.1, data_15_20714.2]

/-- Complete interval computation for depth 15, residue 20715. -/
theorem bounds_15_20715 : exactInterval 15 20715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20715 : oddCount 20715 15 = 10 ∧ acceleratedOrbit 15 20715 = 37334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20715) = 3 ^ 10 * m + 37334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20715.1, data_15_20715.2]

/-- Complete interval computation for depth 15, residue 20716. -/
theorem bounds_15_20716 : exactInterval 15 20716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20716 : oddCount 20716 15 = 8 ∧ acceleratedOrbit 15 20716 = 4151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20716) = 3 ^ 8 * m + 4151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20716.1, data_15_20716.2]

/-- Complete interval computation for depth 15, residue 20717. -/
theorem bounds_15_20717 : exactInterval 15 20717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20717 : oddCount 20717 15 = 8 ∧ acceleratedOrbit 15 20717 = 4151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20717) = 3 ^ 8 * m + 4151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20717.1, data_15_20717.2]

/-- Complete interval computation for depth 15, residue 20718. -/
theorem bounds_15_20718 : exactInterval 15 20718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20718 : oddCount 20718 15 = 8 ∧ acceleratedOrbit 15 20718 = 4151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20718) = 3 ^ 8 * m + 4151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20718.1, data_15_20718.2]

/-- Complete interval computation for depth 15, residue 20719. -/
theorem bounds_15_20719 : exactInterval 15 20719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20719 : oddCount 20719 15 = 11 ∧ acceleratedOrbit 15 20719 = 112016 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20719) = 3 ^ 11 * m + 112016 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20719.1, data_15_20719.2]

/-- Complete interval computation for depth 15, residue 20720. -/
theorem bounds_15_20720 : exactInterval 15 20720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20720 : oddCount 20720 15 = 5 ∧ acceleratedOrbit 15 20720 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20720) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20720.1, data_15_20720.2]

/-- Complete interval computation for depth 15, residue 20721. -/
theorem bounds_15_20721 : exactInterval 15 20721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20721 : oddCount 20721 15 = 5 ∧ acceleratedOrbit 15 20721 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20721) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20721.1, data_15_20721.2]

/-- Complete interval computation for depth 15, residue 20722. -/
theorem bounds_15_20722 : exactInterval 15 20722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20722 : oddCount 20722 15 = 8 ∧ acceleratedOrbit 15 20722 = 4150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20722) = 3 ^ 8 * m + 4150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20722.1, data_15_20722.2]

/-- Complete interval computation for depth 15, residue 20723. -/
theorem bounds_15_20723 : exactInterval 15 20723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20723 : oddCount 20723 15 = 8 ∧ acceleratedOrbit 15 20723 = 4150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20723) = 3 ^ 8 * m + 4150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20723.1, data_15_20723.2]

/-- Complete interval computation for depth 15, residue 20724. -/
theorem bounds_15_20724 : exactInterval 15 20724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20724 : oddCount 20724 15 = 5 ∧ acceleratedOrbit 15 20724 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20724) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20724.1, data_15_20724.2]

/-- Complete interval computation for depth 15, residue 20725. -/
theorem bounds_15_20725 : exactInterval 15 20725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20725 : oddCount 20725 15 = 5 ∧ acceleratedOrbit 15 20725 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20725) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20725.1, data_15_20725.2]

/-- Complete interval computation for depth 15, residue 20726. -/
theorem bounds_15_20726 : exactInterval 15 20726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20726 : oddCount 20726 15 = 8 ∧ acceleratedOrbit 15 20726 = 4151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20726) = 3 ^ 8 * m + 4151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20726.1, data_15_20726.2]

/-- Complete interval computation for depth 15, residue 20727. -/
theorem bounds_15_20727 : exactInterval 15 20727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20727 : oddCount 20727 15 = 8 ∧ acceleratedOrbit 15 20727 = 4151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20727) = 3 ^ 8 * m + 4151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20727.1, data_15_20727.2]

/-- Complete interval computation for depth 15, residue 20728. -/
theorem bounds_15_20728 : exactInterval 15 20728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20728 : oddCount 20728 15 = 7 ∧ acceleratedOrbit 15 20728 = 1384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20728) = 3 ^ 7 * m + 1384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20728.1, data_15_20728.2]

/-- Complete interval computation for depth 15, residue 20729. -/
theorem bounds_15_20729 : exactInterval 15 20729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20729 : oddCount 20729 15 = 10 ∧ acceleratedOrbit 15 20729 = 37361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20729) = 3 ^ 10 * m + 37361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20729.1, data_15_20729.2]

/-- Complete interval computation for depth 15, residue 20730. -/
theorem bounds_15_20730 : exactInterval 15 20730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20730 : oddCount 20730 15 = 7 ∧ acceleratedOrbit 15 20730 = 1384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20730) = 3 ^ 7 * m + 1384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20730.1, data_15_20730.2]

/-- Complete interval computation for depth 15, residue 20731. -/
theorem bounds_15_20731 : exactInterval 15 20731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20731 : oddCount 20731 15 = 12 ∧ acceleratedOrbit 15 20731 = 336251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20731) = 3 ^ 12 * m + 336251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20731.1, data_15_20731.2]

/-- Complete interval computation for depth 15, residue 20732. -/
theorem bounds_15_20732 : exactInterval 15 20732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20732 : oddCount 20732 15 = 7 ∧ acceleratedOrbit 15 20732 = 1384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20732) = 3 ^ 7 * m + 1384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20732.1, data_15_20732.2]

/-- Complete interval computation for depth 15, residue 20733. -/
theorem bounds_15_20733 : exactInterval 15 20733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20733 : oddCount 20733 15 = 7 ∧ acceleratedOrbit 15 20733 = 1384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20733) = 3 ^ 7 * m + 1384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20733.1, data_15_20733.2]

/-- Complete interval computation for depth 15, residue 20734. -/
theorem bounds_15_20734 : exactInterval 15 20734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20734 : oddCount 20734 15 = 11 ∧ acceleratedOrbit 15 20734 = 112103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20734) = 3 ^ 11 * m + 112103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20734.1, data_15_20734.2]

/-- Complete interval computation for depth 15, residue 20735. -/
theorem bounds_15_20735 : exactInterval 15 20735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20735 : oddCount 20735 15 = 11 ∧ acceleratedOrbit 15 20735 = 112103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20735) = 3 ^ 11 * m + 112103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20735.1, data_15_20735.2]

/-- Complete interval computation for depth 15, residue 20736. -/
theorem bounds_15_20736 : exactInterval 15 20736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20736 : oddCount 20736 15 = 4 ∧ acceleratedOrbit 15 20736 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20736) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20736.1, data_15_20736.2]

/-- Complete interval computation for depth 15, residue 20737. -/
theorem bounds_15_20737 : exactInterval 15 20737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20737 : oddCount 20737 15 = 7 ∧ acceleratedOrbit 15 20737 = 1385 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20737) = 3 ^ 7 * m + 1385 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20737.1, data_15_20737.2]

/-- Complete interval computation for depth 15, residue 20738. -/
theorem bounds_15_20738 : exactInterval 15 20738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20738 : oddCount 20738 15 = 7 ∧ acceleratedOrbit 15 20738 = 1385 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20738) = 3 ^ 7 * m + 1385 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20738.1, data_15_20738.2]

/-- Complete interval computation for depth 15, residue 20739. -/
theorem bounds_15_20739 : exactInterval 15 20739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20739 : oddCount 20739 15 = 7 ∧ acceleratedOrbit 15 20739 = 1385 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20739) = 3 ^ 7 * m + 1385 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20739.1, data_15_20739.2]

/-- Complete interval computation for depth 15, residue 20740. -/
theorem bounds_15_20740 : exactInterval 15 20740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20740 : oddCount 20740 15 = 5 ∧ acceleratedOrbit 15 20740 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20740) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20740.1, data_15_20740.2]

/-- Complete interval computation for depth 15, residue 20741. -/
theorem bounds_15_20741 : exactInterval 15 20741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20741 : oddCount 20741 15 = 5 ∧ acceleratedOrbit 15 20741 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20741) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20741.1, data_15_20741.2]

end Collatz.Research.PassageAtlas.Batch0633
