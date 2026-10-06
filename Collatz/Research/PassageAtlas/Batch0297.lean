import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0297

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9699. -/
theorem bounds_15_9699 : exactInterval 15 9699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9699 : oddCount 9699 15 = 3 ∧ acceleratedOrbit 15 9699 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9699) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9699.1, data_15_9699.2]

/-- Complete interval computation for depth 15, residue 9700. -/
theorem bounds_15_9700 : exactInterval 15 9700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9700 : oddCount 9700 15 = 11 ∧ acceleratedOrbit 15 9700 = 52487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9700) = 3 ^ 11 * m + 52487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9700.1, data_15_9700.2]

/-- Complete interval computation for depth 15, residue 9701. -/
theorem bounds_15_9701 : exactInterval 15 9701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9701 : oddCount 9701 15 = 11 ∧ acceleratedOrbit 15 9701 = 52487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9701) = 3 ^ 11 * m + 52487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9701.1, data_15_9701.2]

/-- Complete interval computation for depth 15, residue 9702. -/
theorem bounds_15_9702 : exactInterval 15 9702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9702 : oddCount 9702 15 = 11 ∧ acceleratedOrbit 15 9702 = 52487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9702) = 3 ^ 11 * m + 52487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9702.1, data_15_9702.2]

/-- Complete interval computation for depth 15, residue 9703. -/
theorem bounds_15_9703 : exactInterval 15 9703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9703 : oddCount 9703 15 = 10 ∧ acceleratedOrbit 15 9703 = 17489 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9703) = 3 ^ 10 * m + 17489 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9703.1, data_15_9703.2]

/-- Complete interval computation for depth 15, residue 9704. -/
theorem bounds_15_9704 : exactInterval 15 9704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9704 : oddCount 9704 15 = 7 ∧ acceleratedOrbit 15 9704 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9704) = 3 ^ 7 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9704.1, data_15_9704.2]

/-- Complete interval computation for depth 15, residue 9705. -/
theorem bounds_15_9705 : exactInterval 15 9705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9705 : oddCount 9705 15 = 11 ∧ acceleratedOrbit 15 9705 = 52478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9705) = 3 ^ 11 * m + 52478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9705.1, data_15_9705.2]

/-- Complete interval computation for depth 15, residue 9706. -/
theorem bounds_15_9706 : exactInterval 15 9706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9706 : oddCount 9706 15 = 7 ∧ acceleratedOrbit 15 9706 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9706) = 3 ^ 7 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9706.1, data_15_9706.2]

/-- Complete interval computation for depth 15, residue 9707. -/
theorem bounds_15_9707 : exactInterval 15 9707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9707 : oddCount 9707 15 = 13 ∧ acceleratedOrbit 15 9707 = 472391 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9707) = 3 ^ 13 * m + 472391 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9707.1, data_15_9707.2]

/-- Complete interval computation for depth 15, residue 9708. -/
theorem bounds_15_9708 : exactInterval 15 9708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9708 : oddCount 9708 15 = 8 ∧ acceleratedOrbit 15 9708 = 1946 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9708) = 3 ^ 8 * m + 1946 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9708.1, data_15_9708.2]

/-- Complete interval computation for depth 15, residue 9709. -/
theorem bounds_15_9709 : exactInterval 15 9709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9709 : oddCount 9709 15 = 8 ∧ acceleratedOrbit 15 9709 = 1946 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9709) = 3 ^ 8 * m + 1946 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9709.1, data_15_9709.2]

/-- Complete interval computation for depth 15, residue 9710. -/
theorem bounds_15_9710 : exactInterval 15 9710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9710 : oddCount 9710 15 = 8 ∧ acceleratedOrbit 15 9710 = 1946 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9710) = 3 ^ 8 * m + 1946 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9710.1, data_15_9710.2]

/-- Complete interval computation for depth 15, residue 9711. -/
theorem bounds_15_9711 : exactInterval 15 9711 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9711) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9711 : oddCount 9711 15 = 9 ∧ acceleratedOrbit 15 9711 = 5834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9711) = 3 ^ 9 * m + 5834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9711.1, data_15_9711.2]

/-- Complete interval computation for depth 15, residue 9712. -/
theorem bounds_15_9712 : exactInterval 15 9712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9712 : oddCount 9712 15 = 7 ∧ acceleratedOrbit 15 9712 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9712) = 3 ^ 7 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9712.1, data_15_9712.2]

/-- Complete interval computation for depth 15, residue 9713. -/
theorem bounds_15_9713 : exactInterval 15 9713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9713 : oddCount 9713 15 = 7 ∧ acceleratedOrbit 15 9713 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9713) = 3 ^ 7 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9713.1, data_15_9713.2]

/-- Complete interval computation for depth 15, residue 9714. -/
theorem bounds_15_9714 : exactInterval 15 9714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9714 : oddCount 9714 15 = 7 ∧ acceleratedOrbit 15 9714 = 649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9714) = 3 ^ 7 * m + 649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9714.1, data_15_9714.2]

/-- Complete interval computation for depth 15, residue 9715. -/
theorem bounds_15_9715 : exactInterval 15 9715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9715 : oddCount 9715 15 = 7 ∧ acceleratedOrbit 15 9715 = 649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9715) = 3 ^ 7 * m + 649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9715.1, data_15_9715.2]

/-- Complete interval computation for depth 15, residue 9716. -/
theorem bounds_15_9716 : exactInterval 15 9716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9716 : oddCount 9716 15 = 7 ∧ acceleratedOrbit 15 9716 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9716) = 3 ^ 7 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9716.1, data_15_9716.2]

/-- Complete interval computation for depth 15, residue 9717. -/
theorem bounds_15_9717 : exactInterval 15 9717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9717 : oddCount 9717 15 = 7 ∧ acceleratedOrbit 15 9717 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9717) = 3 ^ 7 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9717.1, data_15_9717.2]

/-- Complete interval computation for depth 15, residue 9718. -/
theorem bounds_15_9718 : exactInterval 15 9718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9718 : oddCount 9718 15 = 9 ∧ acceleratedOrbit 15 9718 = 5840 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9718) = 3 ^ 9 * m + 5840 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9718.1, data_15_9718.2]

/-- Complete interval computation for depth 15, residue 9719. -/
theorem bounds_15_9719 : exactInterval 15 9719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9719 : oddCount 9719 15 = 9 ∧ acceleratedOrbit 15 9719 = 5840 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9719) = 3 ^ 9 * m + 5840 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9719.1, data_15_9719.2]

/-- Complete interval computation for depth 15, residue 9720. -/
theorem bounds_15_9720 : exactInterval 15 9720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9720 : oddCount 9720 15 = 8 ∧ acceleratedOrbit 15 9720 = 1948 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9720) = 3 ^ 8 * m + 1948 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9720.1, data_15_9720.2]

/-- Complete interval computation for depth 15, residue 9721. -/
theorem bounds_15_9721 : exactInterval 15 9721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9721 : oddCount 9721 15 = 7 ∧ acceleratedOrbit 15 9721 = 649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9721) = 3 ^ 7 * m + 649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9721.1, data_15_9721.2]

/-- Complete interval computation for depth 15, residue 9722. -/
theorem bounds_15_9722 : exactInterval 15 9722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9722 : oddCount 9722 15 = 8 ∧ acceleratedOrbit 15 9722 = 1948 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9722) = 3 ^ 8 * m + 1948 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9722.1, data_15_9722.2]

/-- Complete interval computation for depth 15, residue 9723. -/
theorem bounds_15_9723 : exactInterval 15 9723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9723 : oddCount 9723 15 = 9 ∧ acceleratedOrbit 15 9723 = 5842 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9723) = 3 ^ 9 * m + 5842 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9723.1, data_15_9723.2]

/-- Complete interval computation for depth 15, residue 9724. -/
theorem bounds_15_9724 : exactInterval 15 9724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9724 : oddCount 9724 15 = 8 ∧ acceleratedOrbit 15 9724 = 1948 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9724) = 3 ^ 8 * m + 1948 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9724.1, data_15_9724.2]

/-- Complete interval computation for depth 15, residue 9725. -/
theorem bounds_15_9725 : exactInterval 15 9725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9725 : oddCount 9725 15 = 8 ∧ acceleratedOrbit 15 9725 = 1948 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9725) = 3 ^ 8 * m + 1948 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9725.1, data_15_9725.2]

/-- Complete interval computation for depth 15, residue 9726. -/
theorem bounds_15_9726 : exactInterval 15 9726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9726 : oddCount 9726 15 = 11 ∧ acceleratedOrbit 15 9726 = 52591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9726) = 3 ^ 11 * m + 52591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9726.1, data_15_9726.2]

/-- Complete interval computation for depth 15, residue 9727. -/
theorem bounds_15_9727 : exactInterval 15 9727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9727 : oddCount 9727 15 = 11 ∧ acceleratedOrbit 15 9727 = 52591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9727) = 3 ^ 11 * m + 52591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9727.1, data_15_9727.2]

/-- Complete interval computation for depth 15, residue 9728. -/
theorem bounds_15_9728 : exactInterval 15 9728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9728 : oddCount 9728 15 = 4 ∧ acceleratedOrbit 15 9728 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9728) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9728.1, data_15_9728.2]

/-- Complete interval computation for depth 15, residue 9729. -/
theorem bounds_15_9729 : exactInterval 15 9729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9729 : oddCount 9729 15 = 8 ∧ acceleratedOrbit 15 9729 = 1949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9729) = 3 ^ 8 * m + 1949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9729.1, data_15_9729.2]

/-- Complete interval computation for depth 15, residue 9730. -/
theorem bounds_15_9730 : exactInterval 15 9730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9730 : oddCount 9730 15 = 6 ∧ acceleratedOrbit 15 9730 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9730) = 3 ^ 6 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9730.1, data_15_9730.2]

/-- Complete interval computation for depth 15, residue 9731. -/
theorem bounds_15_9731 : exactInterval 15 9731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9731 : oddCount 9731 15 = 6 ∧ acceleratedOrbit 15 9731 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9731) = 3 ^ 6 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9731.1, data_15_9731.2]

end Collatz.Research.PassageAtlas.Batch0297
