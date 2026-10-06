import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0540

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17661. -/
theorem bounds_15_17661 : exactInterval 15 17661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17661 : oddCount 17661 15 = 11 ∧ acceleratedOrbit 15 17661 = 95498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17661) = 3 ^ 11 * m + 95498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17661.1, data_15_17661.2]

/-- Complete interval computation for depth 15, residue 17662. -/
theorem bounds_15_17662 : exactInterval 15 17662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17662 : oddCount 17662 15 = 11 ∧ acceleratedOrbit 15 17662 = 95494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17662) = 3 ^ 11 * m + 95494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17662.1, data_15_17662.2]

/-- Complete interval computation for depth 15, residue 17663. -/
theorem bounds_15_17663 : exactInterval 15 17663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17663 : oddCount 17663 15 = 11 ∧ acceleratedOrbit 15 17663 = 95494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17663) = 3 ^ 11 * m + 95494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17663.1, data_15_17663.2]

/-- Complete interval computation for depth 15, residue 17664. -/
theorem bounds_15_17664 : exactInterval 15 17664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17664 : oddCount 17664 15 = 2 ∧ acceleratedOrbit 15 17664 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17664) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17664.1, data_15_17664.2]

/-- Complete interval computation for depth 15, residue 17665. -/
theorem bounds_15_17665 : exactInterval 15 17665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17665 : oddCount 17665 15 = 8 ∧ acceleratedOrbit 15 17665 = 3539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17665) = 3 ^ 8 * m + 3539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17665.1, data_15_17665.2]

/-- Complete interval computation for depth 15, residue 17666. -/
theorem bounds_15_17666 : exactInterval 15 17666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17666 : oddCount 17666 15 = 8 ∧ acceleratedOrbit 15 17666 = 3539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17666) = 3 ^ 8 * m + 3539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17666.1, data_15_17666.2]

/-- Complete interval computation for depth 15, residue 17667. -/
theorem bounds_15_17667 : exactInterval 15 17667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17667 : oddCount 17667 15 = 8 ∧ acceleratedOrbit 15 17667 = 3539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17667) = 3 ^ 8 * m + 3539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17667.1, data_15_17667.2]

/-- Complete interval computation for depth 15, residue 17668. -/
theorem bounds_15_17668 : exactInterval 15 17668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17668 : oddCount 17668 15 = 6 ∧ acceleratedOrbit 15 17668 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17668) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17668.1, data_15_17668.2]

/-- Complete interval computation for depth 15, residue 17669. -/
theorem bounds_15_17669 : exactInterval 15 17669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17669 : oddCount 17669 15 = 6 ∧ acceleratedOrbit 15 17669 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17669) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17669.1, data_15_17669.2]

/-- Complete interval computation for depth 15, residue 17670. -/
theorem bounds_15_17670 : exactInterval 15 17670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17670 : oddCount 17670 15 = 6 ∧ acceleratedOrbit 15 17670 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17670) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17670.1, data_15_17670.2]

/-- Complete interval computation for depth 15, residue 17671. -/
theorem bounds_15_17671 : exactInterval 15 17671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17671 : oddCount 17671 15 = 9 ∧ acceleratedOrbit 15 17671 = 10616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17671) = 3 ^ 9 * m + 10616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17671.1, data_15_17671.2]

/-- Complete interval computation for depth 15, residue 17672. -/
theorem bounds_15_17672 : exactInterval 15 17672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17672 : oddCount 17672 15 = 7 ∧ acceleratedOrbit 15 17672 = 1181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17672) = 3 ^ 7 * m + 1181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17672.1, data_15_17672.2]

/-- Complete interval computation for depth 15, residue 17673. -/
theorem bounds_15_17673 : exactInterval 15 17673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17673 : oddCount 17673 15 = 10 ∧ acceleratedOrbit 15 17673 = 31853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17673) = 3 ^ 10 * m + 31853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17673.1, data_15_17673.2]

/-- Complete interval computation for depth 15, residue 17674. -/
theorem bounds_15_17674 : exactInterval 15 17674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17674 : oddCount 17674 15 = 7 ∧ acceleratedOrbit 15 17674 = 1181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17674) = 3 ^ 7 * m + 1181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17674.1, data_15_17674.2]

/-- Complete interval computation for depth 15, residue 17675. -/
theorem bounds_15_17675 : exactInterval 15 17675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17675 : oddCount 17675 15 = 7 ∧ acceleratedOrbit 15 17675 = 1180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17675) = 3 ^ 7 * m + 1180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17675.1, data_15_17675.2]

/-- Complete interval computation for depth 15, residue 17676. -/
theorem bounds_15_17676 : exactInterval 15 17676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17676 : oddCount 17676 15 = 7 ∧ acceleratedOrbit 15 17676 = 1181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17676) = 3 ^ 7 * m + 1181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17676.1, data_15_17676.2]

/-- Complete interval computation for depth 15, residue 17677. -/
theorem bounds_15_17677 : exactInterval 15 17677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17677 : oddCount 17677 15 = 7 ∧ acceleratedOrbit 15 17677 = 1181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17677) = 3 ^ 7 * m + 1181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17677.1, data_15_17677.2]

/-- Complete interval computation for depth 15, residue 17678. -/
theorem bounds_15_17678 : exactInterval 15 17678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17678 : oddCount 17678 15 = 7 ∧ acceleratedOrbit 15 17678 = 1181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17678) = 3 ^ 7 * m + 1181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17678.1, data_15_17678.2]

/-- Complete interval computation for depth 15, residue 17679. -/
theorem bounds_15_17679 : exactInterval 15 17679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17679 : oddCount 17679 15 = 7 ∧ acceleratedOrbit 15 17679 = 1181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17679) = 3 ^ 7 * m + 1181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17679.1, data_15_17679.2]

/-- Complete interval computation for depth 15, residue 17680. -/
theorem bounds_15_17680 : exactInterval 15 17680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17680 : oddCount 17680 15 = 6 ∧ acceleratedOrbit 15 17680 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17680) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17680.1, data_15_17680.2]

/-- Complete interval computation for depth 15, residue 17681. -/
theorem bounds_15_17681 : exactInterval 15 17681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17681 : oddCount 17681 15 = 7 ∧ acceleratedOrbit 15 17681 = 1181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17681) = 3 ^ 7 * m + 1181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17681.1, data_15_17681.2]

/-- Complete interval computation for depth 15, residue 17682. -/
theorem bounds_15_17682 : exactInterval 15 17682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17682 : oddCount 17682 15 = 9 ∧ acceleratedOrbit 15 17682 = 10624 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17682) = 3 ^ 9 * m + 10624 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17682.1, data_15_17682.2]

/-- Complete interval computation for depth 15, residue 17683. -/
theorem bounds_15_17683 : exactInterval 15 17683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17683 : oddCount 17683 15 = 9 ∧ acceleratedOrbit 15 17683 = 10624 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17683) = 3 ^ 9 * m + 10624 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17683.1, data_15_17683.2]

/-- Complete interval computation for depth 15, residue 17684. -/
theorem bounds_15_17684 : exactInterval 15 17684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17684 : oddCount 17684 15 = 6 ∧ acceleratedOrbit 15 17684 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17684) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17684.1, data_15_17684.2]

/-- Complete interval computation for depth 15, residue 17685. -/
theorem bounds_15_17685 : exactInterval 15 17685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17685 : oddCount 17685 15 = 6 ∧ acceleratedOrbit 15 17685 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17685) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17685.1, data_15_17685.2]

/-- Complete interval computation for depth 15, residue 17686. -/
theorem bounds_15_17686 : exactInterval 15 17686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17686 : oddCount 17686 15 = 7 ∧ acceleratedOrbit 15 17686 = 1181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17686) = 3 ^ 7 * m + 1181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17686.1, data_15_17686.2]

/-- Complete interval computation for depth 15, residue 17687. -/
theorem bounds_15_17687 : exactInterval 15 17687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17687 : oddCount 17687 15 = 7 ∧ acceleratedOrbit 15 17687 = 1181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17687) = 3 ^ 7 * m + 1181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17687.1, data_15_17687.2]

/-- Complete interval computation for depth 15, residue 17688. -/
theorem bounds_15_17688 : exactInterval 15 17688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17688 : oddCount 17688 15 = 6 ∧ acceleratedOrbit 15 17688 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17688) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17688.1, data_15_17688.2]

/-- Complete interval computation for depth 15, residue 17689. -/
theorem bounds_15_17689 : exactInterval 15 17689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17689 : oddCount 17689 15 = 9 ∧ acceleratedOrbit 15 17689 = 10628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17689) = 3 ^ 9 * m + 10628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17689.1, data_15_17689.2]

/-- Complete interval computation for depth 15, residue 17690. -/
theorem bounds_15_17690 : exactInterval 15 17690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17690 : oddCount 17690 15 = 6 ∧ acceleratedOrbit 15 17690 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17690) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17690.1, data_15_17690.2]

/-- Complete interval computation for depth 15, residue 17691. -/
theorem bounds_15_17691 : exactInterval 15 17691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17691 : oddCount 17691 15 = 12 ∧ acceleratedOrbit 15 17691 = 286942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17691) = 3 ^ 12 * m + 286942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17691.1, data_15_17691.2]

/-- Complete interval computation for depth 15, residue 17692. -/
theorem bounds_15_17692 : exactInterval 15 17692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17692 : oddCount 17692 15 = 9 ∧ acceleratedOrbit 15 17692 = 10631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17692) = 3 ^ 9 * m + 10631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17692.1, data_15_17692.2]

/-- Complete interval computation for depth 15, residue 17693. -/
theorem bounds_15_17693 : exactInterval 15 17693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17693 : oddCount 17693 15 = 9 ∧ acceleratedOrbit 15 17693 = 10631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17693) = 3 ^ 9 * m + 10631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17693.1, data_15_17693.2]

end Collatz.Research.PassageAtlas.Batch0540
