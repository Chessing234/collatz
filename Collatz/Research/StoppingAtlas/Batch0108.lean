import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0108

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 619. -/
theorem bounds_11_619 : exactInterval 11 619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_619 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 619) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_619 : oddCount 619 11 = 6 ∧ acceleratedOrbit 11 619 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_619 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 619) = 3 ^ 6 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_619.1, data_11_619.2]

/-- Complete interval computation for depth 11, residue 620. -/
theorem bounds_11_620 : exactInterval 11 620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_620 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 620) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_620 : oddCount 620 11 = 7 ∧ acceleratedOrbit 11 620 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_620 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 620) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_620.1, data_11_620.2]

/-- Complete interval computation for depth 11, residue 621. -/
theorem bounds_11_621 : exactInterval 11 621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_621 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 621) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_621 : oddCount 621 11 = 7 ∧ acceleratedOrbit 11 621 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_621 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 621) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_621.1, data_11_621.2]

/-- Complete interval computation for depth 11, residue 622. -/
theorem bounds_11_622 : exactInterval 11 622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_622 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 622) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_622 : oddCount 622 11 = 7 ∧ acceleratedOrbit 11 622 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_622 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 622) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_622.1, data_11_622.2]

/-- Complete interval computation for depth 11, residue 623. -/
theorem bounds_11_623 : exactInterval 11 623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_623 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 623) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_623 : oddCount 623 11 = 8 ∧ acceleratedOrbit 11 623 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_623 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 623) = 3 ^ 8 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_623.1, data_11_623.2]

/-- Complete interval computation for depth 11, residue 624. -/
theorem bounds_11_624 : exactInterval 11 624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_624 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 624) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_624 : oddCount 624 11 = 5 ∧ acceleratedOrbit 11 624 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_624 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 624) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_624.1, data_11_624.2]

/-- Complete interval computation for depth 11, residue 625. -/
theorem bounds_11_625 : exactInterval 11 625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_625 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 625) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_625 : oddCount 625 11 = 4 ∧ acceleratedOrbit 11 625 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_625 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 625) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_625.1, data_11_625.2]

/-- Complete interval computation for depth 11, residue 626. -/
theorem bounds_11_626 : exactInterval 11 626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_626 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 626) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_626 : oddCount 626 11 = 7 ∧ acceleratedOrbit 11 626 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_626 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 626) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_626.1, data_11_626.2]

/-- Complete interval computation for depth 11, residue 627. -/
theorem bounds_11_627 : exactInterval 11 627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_627 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 627) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_627 : oddCount 627 11 = 7 ∧ acceleratedOrbit 11 627 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_627 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 627) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_627.1, data_11_627.2]

/-- Complete interval computation for depth 11, residue 628. -/
theorem bounds_11_628 : exactInterval 11 628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_628 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 628) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_628 : oddCount 628 11 = 5 ∧ acceleratedOrbit 11 628 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_628 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 628) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_628.1, data_11_628.2]

/-- Complete interval computation for depth 11, residue 629. -/
theorem bounds_11_629 : exactInterval 11 629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_629 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 629) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_629 : oddCount 629 11 = 5 ∧ acceleratedOrbit 11 629 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_629 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 629) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_629.1, data_11_629.2]

/-- Complete interval computation for depth 11, residue 630. -/
theorem bounds_11_630 : exactInterval 11 630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_630 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 630) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_630 : oddCount 630 11 = 4 ∧ acceleratedOrbit 11 630 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_630 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 630) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_630.1, data_11_630.2]

/-- Complete interval computation for depth 11, residue 631. -/
theorem bounds_11_631 : exactInterval 11 631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_631 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 631) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_631 : oddCount 631 11 = 4 ∧ acceleratedOrbit 11 631 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_631 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 631) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_631.1, data_11_631.2]

/-- Complete interval computation for depth 11, residue 632. -/
theorem bounds_11_632 : exactInterval 11 632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_632 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 632) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_632 : oddCount 632 11 = 5 ∧ acceleratedOrbit 11 632 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_632 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 632) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_632.1, data_11_632.2]

/-- Complete interval computation for depth 11, residue 633. -/
theorem bounds_11_633 : exactInterval 11 633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_633 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 633) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_633 : oddCount 633 11 = 6 ∧ acceleratedOrbit 11 633 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_633 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 633) = 3 ^ 6 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_633.1, data_11_633.2]

end Collatz.Research.StoppingAtlas.Batch0108
