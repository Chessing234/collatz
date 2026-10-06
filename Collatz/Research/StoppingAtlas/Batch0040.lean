import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0040

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 599. -/
theorem bounds_10_599 : exactInterval 10 599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_599 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 599) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_599 : oddCount 599 10 = 5 ∧ acceleratedOrbit 10 599 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_599 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 599) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_599.1, data_10_599.2]

/-- Complete interval computation for depth 10, residue 600. -/
theorem bounds_10_600 : exactInterval 10 600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_600 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 600) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_600 : oddCount 600 10 = 3 ∧ acceleratedOrbit 10 600 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_600 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 600) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_600.1, data_10_600.2]

/-- Complete interval computation for depth 10, residue 601. -/
theorem bounds_10_601 : exactInterval 10 601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_601 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 601) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_601 : oddCount 601 10 = 6 ∧ acceleratedOrbit 10 601 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_601 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 601) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_601.1, data_10_601.2]

/-- Complete interval computation for depth 10, residue 602. -/
theorem bounds_10_602 : exactInterval 10 602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_602 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 602) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_602 : oddCount 602 10 = 3 ∧ acceleratedOrbit 10 602 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_602 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 602) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_602.1, data_10_602.2]

/-- Complete interval computation for depth 10, residue 603. -/
theorem bounds_10_603 : exactInterval 10 603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_603 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 603) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_603 : oddCount 603 10 = 7 ∧ acceleratedOrbit 10 603 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_603 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 603) = 3 ^ 7 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_603.1, data_10_603.2]

/-- Complete interval computation for depth 10, residue 604. -/
theorem bounds_10_604 : exactInterval 10 604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_604 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 604) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_604 : oddCount 604 10 = 3 ∧ acceleratedOrbit 10 604 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_604 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 604) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_604.1, data_10_604.2]

/-- Complete interval computation for depth 10, residue 605. -/
theorem bounds_10_605 : exactInterval 10 605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_605 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 605) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_605 : oddCount 605 10 = 3 ∧ acceleratedOrbit 10 605 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_605 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 605) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_605.1, data_10_605.2]

/-- Complete interval computation for depth 10, residue 606. -/
theorem bounds_10_606 : exactInterval 10 606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_606 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 606) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_606 : oddCount 606 10 = 6 ∧ acceleratedOrbit 10 606 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_606 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 606) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_606.1, data_10_606.2]

/-- Complete interval computation for depth 10, residue 607. -/
theorem bounds_10_607 : exactInterval 10 607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_607 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 607) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_607 : oddCount 607 10 = 6 ∧ acceleratedOrbit 10 607 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_607 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 607) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_607.1, data_10_607.2]

/-- Complete interval computation for depth 10, residue 608. -/
theorem bounds_10_608 : exactInterval 10 608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_608 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 608) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_608 : oddCount 608 10 = 3 ∧ acceleratedOrbit 10 608 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_608 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 608) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_608.1, data_10_608.2]

/-- Complete interval computation for depth 10, residue 609. -/
theorem bounds_10_609 : exactInterval 10 609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_609 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 609) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_609 : oddCount 609 10 = 5 ∧ acceleratedOrbit 10 609 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_609 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 609) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_609.1, data_10_609.2]

/-- Complete interval computation for depth 10, residue 610. -/
theorem bounds_10_610 : exactInterval 10 610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_610 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 610) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_610 : oddCount 610 10 = 4 ∧ acceleratedOrbit 10 610 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_610 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 610) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_610.1, data_10_610.2]

/-- Complete interval computation for depth 10, residue 611. -/
theorem bounds_10_611 : exactInterval 10 611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_611 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 611) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_611 : oddCount 611 10 = 4 ∧ acceleratedOrbit 10 611 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_611 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 611) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_611.1, data_10_611.2]

/-- Complete interval computation for depth 10, residue 612. -/
theorem bounds_10_612 : exactInterval 10 612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_612 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 612) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_612 : oddCount 612 10 = 4 ∧ acceleratedOrbit 10 612 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_612 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 612) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_612.1, data_10_612.2]

/-- Complete interval computation for depth 10, residue 613. -/
theorem bounds_10_613 : exactInterval 10 613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_613 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 613) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_613 : oddCount 613 10 = 4 ∧ acceleratedOrbit 10 613 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_613 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 613) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_613.1, data_10_613.2]

end Collatz.Research.StoppingAtlas.Batch0040
