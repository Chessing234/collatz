import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0508

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 619. -/
theorem bounds_13_619 : exactInterval 13 619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_619 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 619) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_619 : oddCount 619 13 = 7 ∧ acceleratedOrbit 13 619 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_619 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 619) = 3 ^ 7 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_619.1, data_13_619.2]

/-- Complete interval computation for depth 13, residue 620. -/
theorem bounds_13_620 : exactInterval 13 620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_620 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 620) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_620 : oddCount 620 13 = 7 ∧ acceleratedOrbit 13 620 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_620 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 620) = 3 ^ 7 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_620.1, data_13_620.2]

/-- Complete interval computation for depth 13, residue 621. -/
theorem bounds_13_621 : exactInterval 13 621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_621 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 621) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_621 : oddCount 621 13 = 7 ∧ acceleratedOrbit 13 621 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_621 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 621) = 3 ^ 7 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_621.1, data_13_621.2]

/-- Complete interval computation for depth 13, residue 622. -/
theorem bounds_13_622 : exactInterval 13 622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_622 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 622) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_622 : oddCount 622 13 = 7 ∧ acceleratedOrbit 13 622 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_622 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 622) = 3 ^ 7 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_622.1, data_13_622.2]

/-- Complete interval computation for depth 13, residue 623. -/
theorem bounds_13_623 : exactInterval 13 623 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_623 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 623) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_623 : oddCount 623 13 = 8 ∧ acceleratedOrbit 13 623 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_623 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 623) = 3 ^ 8 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_623.1, data_13_623.2]

/-- Complete interval computation for depth 13, residue 624. -/
theorem bounds_13_624 : exactInterval 13 624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_624 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 624) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_624 : oddCount 624 13 = 5 ∧ acceleratedOrbit 13 624 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_624 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 624) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_624.1, data_13_624.2]

/-- Complete interval computation for depth 13, residue 625. -/
theorem bounds_13_625 : exactInterval 13 625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_625 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 625) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_625 : oddCount 625 13 = 5 ∧ acceleratedOrbit 13 625 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_625 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 625) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_625.1, data_13_625.2]

/-- Complete interval computation for depth 13, residue 626. -/
theorem bounds_13_626 : exactInterval 13 626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_626 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 626) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_626 : oddCount 626 13 = 8 ∧ acceleratedOrbit 13 626 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_626 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 626) = 3 ^ 8 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_626.1, data_13_626.2]

/-- Complete interval computation for depth 13, residue 627. -/
theorem bounds_13_627 : exactInterval 13 627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_627 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 627) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_627 : oddCount 627 13 = 8 ∧ acceleratedOrbit 13 627 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_627 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 627) = 3 ^ 8 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_627.1, data_13_627.2]

/-- Complete interval computation for depth 13, residue 628. -/
theorem bounds_13_628 : exactInterval 13 628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_628 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 628) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_628 : oddCount 628 13 = 5 ∧ acceleratedOrbit 13 628 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_628 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 628) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_628.1, data_13_628.2]

/-- Complete interval computation for depth 13, residue 629. -/
theorem bounds_13_629 : exactInterval 13 629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_629 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 629) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_629 : oddCount 629 13 = 5 ∧ acceleratedOrbit 13 629 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_629 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 629) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_629.1, data_13_629.2]

/-- Complete interval computation for depth 13, residue 630. -/
theorem bounds_13_630 : exactInterval 13 630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_630 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 630) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_630 : oddCount 630 13 = 5 ∧ acceleratedOrbit 13 630 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_630 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 630) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_630.1, data_13_630.2]

/-- Complete interval computation for depth 13, residue 631. -/
theorem bounds_13_631 : exactInterval 13 631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_631 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 631) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_631 : oddCount 631 13 = 5 ∧ acceleratedOrbit 13 631 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_631 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 631) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_631.1, data_13_631.2]

/-- Complete interval computation for depth 13, residue 632. -/
theorem bounds_13_632 : exactInterval 13 632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_632 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 632) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_632 : oddCount 632 13 = 5 ∧ acceleratedOrbit 13 632 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_632 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 632) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_632.1, data_13_632.2]

/-- Complete interval computation for depth 13, residue 633. -/
theorem bounds_13_633 : exactInterval 13 633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_633 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 633) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_633 : oddCount 633 13 = 7 ∧ acceleratedOrbit 13 633 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_633 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 633) = 3 ^ 7 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_633.1, data_13_633.2]

end Collatz.Research.StoppingAtlas.Batch0508
