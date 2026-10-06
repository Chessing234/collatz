import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0041

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 614. -/
theorem bounds_10_614 : exactInterval 10 614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_614 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 614) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_614 : oddCount 614 10 = 4 ∧ acceleratedOrbit 10 614 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_614 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 614) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_614.1, data_10_614.2]

/-- Complete interval computation for depth 10, residue 615. -/
theorem bounds_10_615 : exactInterval 10 615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_615 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 615) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_615 : oddCount 615 10 = 7 ∧ acceleratedOrbit 10 615 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_615 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 615) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_615.1, data_10_615.2]

/-- Complete interval computation for depth 10, residue 616. -/
theorem bounds_10_616 : exactInterval 10 616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_616 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 616) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_616 : oddCount 616 10 = 3 ∧ acceleratedOrbit 10 616 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_616 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 616) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_616.1, data_10_616.2]

/-- Complete interval computation for depth 10, residue 617. -/
theorem bounds_10_617 : exactInterval 10 617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_617 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 617) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_617 : oddCount 617 10 = 7 ∧ acceleratedOrbit 10 617 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_617 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 617) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_617.1, data_10_617.2]

/-- Complete interval computation for depth 10, residue 618. -/
theorem bounds_10_618 : exactInterval 10 618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_618 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 618) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_618 : oddCount 618 10 = 3 ∧ acceleratedOrbit 10 618 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_618 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 618) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_618.1, data_10_618.2]

/-- Complete interval computation for depth 10, residue 619. -/
theorem bounds_10_619 : exactInterval 10 619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_619 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 619) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_619 : oddCount 619 10 = 6 ∧ acceleratedOrbit 10 619 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_619 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 619) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_619.1, data_10_619.2]

/-- Complete interval computation for depth 10, residue 620. -/
theorem bounds_10_620 : exactInterval 10 620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_620 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 620) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_620 : oddCount 620 10 = 6 ∧ acceleratedOrbit 10 620 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_620 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 620) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_620.1, data_10_620.2]

/-- Complete interval computation for depth 10, residue 621. -/
theorem bounds_10_621 : exactInterval 10 621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_621 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 621) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_621 : oddCount 621 10 = 6 ∧ acceleratedOrbit 10 621 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_621 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 621) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_621.1, data_10_621.2]

/-- Complete interval computation for depth 10, residue 622. -/
theorem bounds_10_622 : exactInterval 10 622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_622 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 622) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_622 : oddCount 622 10 = 6 ∧ acceleratedOrbit 10 622 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_622 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 622) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_622.1, data_10_622.2]

/-- Complete interval computation for depth 10, residue 623. -/
theorem bounds_10_623 : exactInterval 10 623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_623 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 623) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_623 : oddCount 623 10 = 7 ∧ acceleratedOrbit 10 623 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_623 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 623) = 3 ^ 7 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_623.1, data_10_623.2]

/-- Complete interval computation for depth 10, residue 624. -/
theorem bounds_10_624 : exactInterval 10 624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_624 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 624) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_624 : oddCount 624 10 = 5 ∧ acceleratedOrbit 10 624 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_624 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 624) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_624.1, data_10_624.2]

/-- Complete interval computation for depth 10, residue 625. -/
theorem bounds_10_625 : exactInterval 10 625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_625 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 625) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_625 : oddCount 625 10 = 3 ∧ acceleratedOrbit 10 625 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_625 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 625) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_625.1, data_10_625.2]

/-- Complete interval computation for depth 10, residue 626. -/
theorem bounds_10_626 : exactInterval 10 626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_626 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 626) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_626 : oddCount 626 10 = 6 ∧ acceleratedOrbit 10 626 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_626 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 626) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_626.1, data_10_626.2]

/-- Complete interval computation for depth 10, residue 627. -/
theorem bounds_10_627 : exactInterval 10 627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_627 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 627) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_627 : oddCount 627 10 = 6 ∧ acceleratedOrbit 10 627 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_627 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 627) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_627.1, data_10_627.2]

/-- Complete interval computation for depth 10, residue 628. -/
theorem bounds_10_628 : exactInterval 10 628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_628 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 628) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_628 : oddCount 628 10 = 5 ∧ acceleratedOrbit 10 628 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_628 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 628) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_628.1, data_10_628.2]

end Collatz.Research.StoppingAtlas.Batch0041
