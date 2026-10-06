import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0508

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16613. -/
theorem bounds_15_16613 : exactInterval 15 16613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16613 : oddCount 16613 15 = 6 ∧ acceleratedOrbit 15 16613 = 370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16613) = 3 ^ 6 * m + 370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16613.1, data_15_16613.2]

/-- Complete interval computation for depth 15, residue 16614. -/
theorem bounds_15_16614 : exactInterval 15 16614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16614 : oddCount 16614 15 = 6 ∧ acceleratedOrbit 15 16614 = 370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16614) = 3 ^ 6 * m + 370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16614.1, data_15_16614.2]

/-- Complete interval computation for depth 15, residue 16615. -/
theorem bounds_15_16615 : exactInterval 15 16615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16615 : oddCount 16615 15 = 7 ∧ acceleratedOrbit 15 16615 = 1109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16615) = 3 ^ 7 * m + 1109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16615.1, data_15_16615.2]

/-- Complete interval computation for depth 15, residue 16616. -/
theorem bounds_15_16616 : exactInterval 15 16616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16616 : oddCount 16616 15 = 6 ∧ acceleratedOrbit 15 16616 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16616) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16616.1, data_15_16616.2]

/-- Complete interval computation for depth 15, residue 16617. -/
theorem bounds_15_16617 : exactInterval 15 16617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16617 : oddCount 16617 15 = 9 ∧ acceleratedOrbit 15 16617 = 9983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16617) = 3 ^ 9 * m + 9983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16617.1, data_15_16617.2]

/-- Complete interval computation for depth 15, residue 16618. -/
theorem bounds_15_16618 : exactInterval 15 16618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16618 : oddCount 16618 15 = 6 ∧ acceleratedOrbit 15 16618 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16618) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16618.1, data_15_16618.2]

/-- Complete interval computation for depth 15, residue 16619. -/
theorem bounds_15_16619 : exactInterval 15 16619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16619 : oddCount 16619 15 = 8 ∧ acceleratedOrbit 15 16619 = 3328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16619) = 3 ^ 8 * m + 3328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16619.1, data_15_16619.2]

/-- Complete interval computation for depth 15, residue 16620. -/
theorem bounds_15_16620 : exactInterval 15 16620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16620 : oddCount 16620 15 = 6 ∧ acceleratedOrbit 15 16620 = 370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16620) = 3 ^ 6 * m + 370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16620.1, data_15_16620.2]

/-- Complete interval computation for depth 15, residue 16621. -/
theorem bounds_15_16621 : exactInterval 15 16621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16621 : oddCount 16621 15 = 6 ∧ acceleratedOrbit 15 16621 = 370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16621) = 3 ^ 6 * m + 370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16621.1, data_15_16621.2]

/-- Complete interval computation for depth 15, residue 16622. -/
theorem bounds_15_16622 : exactInterval 15 16622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16622 : oddCount 16622 15 = 6 ∧ acceleratedOrbit 15 16622 = 370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16622) = 3 ^ 6 * m + 370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16622.1, data_15_16622.2]

/-- Complete interval computation for depth 15, residue 16623. -/
theorem bounds_15_16623 : exactInterval 15 16623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16623 : oddCount 16623 15 = 11 ∧ acceleratedOrbit 15 16623 = 89873 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16623) = 3 ^ 11 * m + 89873 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16623.1, data_15_16623.2]

/-- Complete interval computation for depth 15, residue 16624. -/
theorem bounds_15_16624 : exactInterval 15 16624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16624 : oddCount 16624 15 = 6 ∧ acceleratedOrbit 15 16624 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16624) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16624.1, data_15_16624.2]

/-- Complete interval computation for depth 15, residue 16625. -/
theorem bounds_15_16625 : exactInterval 15 16625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16625 : oddCount 16625 15 = 6 ∧ acceleratedOrbit 15 16625 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16625) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16625.1, data_15_16625.2]

/-- Complete interval computation for depth 15, residue 16626. -/
theorem bounds_15_16626 : exactInterval 15 16626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16626 : oddCount 16626 15 = 11 ∧ acceleratedOrbit 15 16626 = 89909 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16626) = 3 ^ 11 * m + 89909 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16626.1, data_15_16626.2]

/-- Complete interval computation for depth 15, residue 16627. -/
theorem bounds_15_16627 : exactInterval 15 16627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16627 : oddCount 16627 15 = 11 ∧ acceleratedOrbit 15 16627 = 89909 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16627) = 3 ^ 11 * m + 89909 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16627.1, data_15_16627.2]

/-- Complete interval computation for depth 15, residue 16628. -/
theorem bounds_15_16628 : exactInterval 15 16628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16628 : oddCount 16628 15 = 6 ∧ acceleratedOrbit 15 16628 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16628) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16628.1, data_15_16628.2]

/-- Complete interval computation for depth 15, residue 16629. -/
theorem bounds_15_16629 : exactInterval 15 16629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16629 : oddCount 16629 15 = 6 ∧ acceleratedOrbit 15 16629 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16629) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16629.1, data_15_16629.2]

/-- Complete interval computation for depth 15, residue 16630. -/
theorem bounds_15_16630 : exactInterval 15 16630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16630 : oddCount 16630 15 = 8 ∧ acceleratedOrbit 15 16630 = 3331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16630) = 3 ^ 8 * m + 3331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16630.1, data_15_16630.2]

/-- Complete interval computation for depth 15, residue 16631. -/
theorem bounds_15_16631 : exactInterval 15 16631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16631 : oddCount 16631 15 = 8 ∧ acceleratedOrbit 15 16631 = 3331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16631) = 3 ^ 8 * m + 3331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16631.1, data_15_16631.2]

/-- Complete interval computation for depth 15, residue 16632. -/
theorem bounds_15_16632 : exactInterval 15 16632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16632 : oddCount 16632 15 = 8 ∧ acceleratedOrbit 15 16632 = 3332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16632) = 3 ^ 8 * m + 3332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16632.1, data_15_16632.2]

/-- Complete interval computation for depth 15, residue 16633. -/
theorem bounds_15_16633 : exactInterval 15 16633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16633 : oddCount 16633 15 = 8 ∧ acceleratedOrbit 15 16633 = 3331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16633) = 3 ^ 8 * m + 3331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16633.1, data_15_16633.2]

/-- Complete interval computation for depth 15, residue 16634. -/
theorem bounds_15_16634 : exactInterval 15 16634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16634 : oddCount 16634 15 = 8 ∧ acceleratedOrbit 15 16634 = 3332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16634) = 3 ^ 8 * m + 3332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16634.1, data_15_16634.2]

/-- Complete interval computation for depth 15, residue 16635. -/
theorem bounds_15_16635 : exactInterval 15 16635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16635 : oddCount 16635 15 = 10 ∧ acceleratedOrbit 15 16635 = 29980 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16635) = 3 ^ 10 * m + 29980 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16635.1, data_15_16635.2]

/-- Complete interval computation for depth 15, residue 16636. -/
theorem bounds_15_16636 : exactInterval 15 16636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16636 : oddCount 16636 15 = 8 ∧ acceleratedOrbit 15 16636 = 3332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16636) = 3 ^ 8 * m + 3332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16636.1, data_15_16636.2]

/-- Complete interval computation for depth 15, residue 16637. -/
theorem bounds_15_16637 : exactInterval 15 16637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16637 : oddCount 16637 15 = 8 ∧ acceleratedOrbit 15 16637 = 3332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16637) = 3 ^ 8 * m + 3332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16637.1, data_15_16637.2]

/-- Complete interval computation for depth 15, residue 16638. -/
theorem bounds_15_16638 : exactInterval 15 16638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16638 : oddCount 16638 15 = 10 ∧ acceleratedOrbit 15 16638 = 29987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16638) = 3 ^ 10 * m + 29987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16638.1, data_15_16638.2]

/-- Complete interval computation for depth 15, residue 16639. -/
theorem bounds_15_16639 : exactInterval 15 16639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16639 : oddCount 16639 15 = 10 ∧ acceleratedOrbit 15 16639 = 29987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16639) = 3 ^ 10 * m + 29987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16639.1, data_15_16639.2]

/-- Complete interval computation for depth 15, residue 16640. -/
theorem bounds_15_16640 : exactInterval 15 16640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16640 : oddCount 16640 15 = 3 ∧ acceleratedOrbit 15 16640 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16640) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16640.1, data_15_16640.2]

/-- Complete interval computation for depth 15, residue 16641. -/
theorem bounds_15_16641 : exactInterval 15 16641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16641 : oddCount 16641 15 = 8 ∧ acceleratedOrbit 15 16641 = 3334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16641) = 3 ^ 8 * m + 3334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16641.1, data_15_16641.2]

/-- Complete interval computation for depth 15, residue 16642. -/
theorem bounds_15_16642 : exactInterval 15 16642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16642 : oddCount 16642 15 = 8 ∧ acceleratedOrbit 15 16642 = 3334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16642) = 3 ^ 8 * m + 3334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16642.1, data_15_16642.2]

/-- Complete interval computation for depth 15, residue 16643. -/
theorem bounds_15_16643 : exactInterval 15 16643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16643 : oddCount 16643 15 = 8 ∧ acceleratedOrbit 15 16643 = 3334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16643) = 3 ^ 8 * m + 3334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16643.1, data_15_16643.2]

/-- Complete interval computation for depth 15, residue 16644. -/
theorem bounds_15_16644 : exactInterval 15 16644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16644 : oddCount 16644 15 = 6 ∧ acceleratedOrbit 15 16644 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16644) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16644.1, data_15_16644.2]

/-- Complete interval computation for depth 15, residue 16645. -/
theorem bounds_15_16645 : exactInterval 15 16645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16645 : oddCount 16645 15 = 6 ∧ acceleratedOrbit 15 16645 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16645) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16645.1, data_15_16645.2]

end Collatz.Research.PassageAtlas.Batch0508
