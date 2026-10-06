import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0241

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 614. -/
theorem bounds_12_614 : exactInterval 12 614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_614 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 614) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_614 : oddCount 614 12 = 5 ∧ acceleratedOrbit 12 614 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_614 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 614) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_614.1, data_12_614.2]

/-- Complete interval computation for depth 12, residue 615. -/
theorem bounds_12_615 : exactInterval 12 615 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_615 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 615) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_615 : oddCount 615 12 = 7 ∧ acceleratedOrbit 12 615 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_615 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 615) = 3 ^ 7 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_615.1, data_12_615.2]

/-- Complete interval computation for depth 12, residue 616. -/
theorem bounds_12_616 : exactInterval 12 616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_616 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 616) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_616 : oddCount 616 12 = 4 ∧ acceleratedOrbit 12 616 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_616 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 616) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_616.1, data_12_616.2]

/-- Complete interval computation for depth 12, residue 617. -/
theorem bounds_12_617 : exactInterval 12 617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_617 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 617) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_617 : oddCount 617 12 = 8 ∧ acceleratedOrbit 12 617 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_617 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 617) = 3 ^ 8 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_617.1, data_12_617.2]

/-- Complete interval computation for depth 12, residue 618. -/
theorem bounds_12_618 : exactInterval 12 618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_618 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 618) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_618 : oddCount 618 12 = 4 ∧ acceleratedOrbit 12 618 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_618 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 618) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_618.1, data_12_618.2]

/-- Complete interval computation for depth 12, residue 619. -/
theorem bounds_12_619 : exactInterval 12 619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_619 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 619) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_619 : oddCount 619 12 = 7 ∧ acceleratedOrbit 12 619 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_619 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 619) = 3 ^ 7 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_619.1, data_12_619.2]

/-- Complete interval computation for depth 12, residue 620. -/
theorem bounds_12_620 : exactInterval 12 620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_620 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 620) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_620 : oddCount 620 12 = 7 ∧ acceleratedOrbit 12 620 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_620 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 620) = 3 ^ 7 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_620.1, data_12_620.2]

/-- Complete interval computation for depth 12, residue 621. -/
theorem bounds_12_621 : exactInterval 12 621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_621 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 621) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_621 : oddCount 621 12 = 7 ∧ acceleratedOrbit 12 621 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_621 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 621) = 3 ^ 7 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_621.1, data_12_621.2]

/-- Complete interval computation for depth 12, residue 622. -/
theorem bounds_12_622 : exactInterval 12 622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_622 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 622) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_622 : oddCount 622 12 = 7 ∧ acceleratedOrbit 12 622 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_622 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 622) = 3 ^ 7 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_622.1, data_12_622.2]

/-- Complete interval computation for depth 12, residue 623. -/
theorem bounds_12_623 : exactInterval 12 623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_623 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 623) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_623 : oddCount 623 12 = 8 ∧ acceleratedOrbit 12 623 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_623 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 623) = 3 ^ 8 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_623.1, data_12_623.2]

/-- Complete interval computation for depth 12, residue 624. -/
theorem bounds_12_624 : exactInterval 12 624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_624 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 624) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_624 : oddCount 624 12 = 5 ∧ acceleratedOrbit 12 624 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_624 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 624) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_624.1, data_12_624.2]

/-- Complete interval computation for depth 12, residue 625. -/
theorem bounds_12_625 : exactInterval 12 625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_625 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 625) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_625 : oddCount 625 12 = 4 ∧ acceleratedOrbit 12 625 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_625 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 625) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_625.1, data_12_625.2]

/-- Complete interval computation for depth 12, residue 626. -/
theorem bounds_12_626 : exactInterval 12 626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_626 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 626) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_626 : oddCount 626 12 = 7 ∧ acceleratedOrbit 12 626 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_626 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 626) = 3 ^ 7 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_626.1, data_12_626.2]

/-- Complete interval computation for depth 12, residue 627. -/
theorem bounds_12_627 : exactInterval 12 627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_627 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 627) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_627 : oddCount 627 12 = 7 ∧ acceleratedOrbit 12 627 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_627 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 627) = 3 ^ 7 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_627.1, data_12_627.2]

/-- Complete interval computation for depth 12, residue 628. -/
theorem bounds_12_628 : exactInterval 12 628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_628 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 628) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_628 : oddCount 628 12 = 5 ∧ acceleratedOrbit 12 628 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_628 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 628) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_628.1, data_12_628.2]

end Collatz.Research.StoppingAtlas.Batch0241
