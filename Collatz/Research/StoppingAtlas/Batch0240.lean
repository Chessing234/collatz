import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0240

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 599. -/
theorem bounds_12_599 : exactInterval 12 599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_599 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 599) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_599 : oddCount 599 12 = 7 ∧ acceleratedOrbit 12 599 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_599 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 599) = 3 ^ 7 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_599.1, data_12_599.2]

/-- Complete interval computation for depth 12, residue 600. -/
theorem bounds_12_600 : exactInterval 12 600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_600 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 600) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_600 : oddCount 600 12 = 3 ∧ acceleratedOrbit 12 600 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_600 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 600) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_600.1, data_12_600.2]

/-- Complete interval computation for depth 12, residue 601. -/
theorem bounds_12_601 : exactInterval 12 601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_601 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 601) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_601 : oddCount 601 12 = 8 ∧ acceleratedOrbit 12 601 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_601 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 601) = 3 ^ 8 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_601.1, data_12_601.2]

/-- Complete interval computation for depth 12, residue 602. -/
theorem bounds_12_602 : exactInterval 12 602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_602 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 602) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_602 : oddCount 602 12 = 3 ∧ acceleratedOrbit 12 602 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_602 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 602) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_602.1, data_12_602.2]

/-- Complete interval computation for depth 12, residue 603. -/
theorem bounds_12_603 : exactInterval 12 603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_603 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 603) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_603 : oddCount 603 12 = 9 ∧ acceleratedOrbit 12 603 = 2906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_603 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 603) = 3 ^ 9 * m + 2906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_603.1, data_12_603.2]

/-- Complete interval computation for depth 12, residue 604. -/
theorem bounds_12_604 : exactInterval 12 604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_604 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 604) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_604 : oddCount 604 12 = 3 ∧ acceleratedOrbit 12 604 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_604 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 604) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_604.1, data_12_604.2]

/-- Complete interval computation for depth 12, residue 605. -/
theorem bounds_12_605 : exactInterval 12 605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_605 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 605) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_605 : oddCount 605 12 = 3 ∧ acceleratedOrbit 12 605 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_605 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 605) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_605.1, data_12_605.2]

/-- Complete interval computation for depth 12, residue 606. -/
theorem bounds_12_606 : exactInterval 12 606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_606 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 606) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_606 : oddCount 606 12 = 7 ∧ acceleratedOrbit 12 606 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_606 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 606) = 3 ^ 7 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_606.1, data_12_606.2]

/-- Complete interval computation for depth 12, residue 607. -/
theorem bounds_12_607 : exactInterval 12 607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_607 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 607) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_607 : oddCount 607 12 = 7 ∧ acceleratedOrbit 12 607 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_607 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 607) = 3 ^ 7 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_607.1, data_12_607.2]

/-- Complete interval computation for depth 12, residue 608. -/
theorem bounds_12_608 : exactInterval 12 608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_608 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 608) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_608 : oddCount 608 12 = 4 ∧ acceleratedOrbit 12 608 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_608 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 608) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_608.1, data_12_608.2]

/-- Complete interval computation for depth 12, residue 609. -/
theorem bounds_12_609 : exactInterval 12 609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_609 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 609) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_609 : oddCount 609 12 = 6 ∧ acceleratedOrbit 12 609 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_609 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 609) = 3 ^ 6 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_609.1, data_12_609.2]

/-- Complete interval computation for depth 12, residue 610. -/
theorem bounds_12_610 : exactInterval 12 610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_610 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 610) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_610 : oddCount 610 12 = 5 ∧ acceleratedOrbit 12 610 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_610 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 610) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_610.1, data_12_610.2]

/-- Complete interval computation for depth 12, residue 611. -/
theorem bounds_12_611 : exactInterval 12 611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_611 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 611) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_611 : oddCount 611 12 = 5 ∧ acceleratedOrbit 12 611 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_611 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 611) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_611.1, data_12_611.2]

/-- Complete interval computation for depth 12, residue 612. -/
theorem bounds_12_612 : exactInterval 12 612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_612 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 612) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_612 : oddCount 612 12 = 5 ∧ acceleratedOrbit 12 612 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_612 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 612) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_612.1, data_12_612.2]

/-- Complete interval computation for depth 12, residue 613. -/
theorem bounds_12_613 : exactInterval 12 613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_613 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 613) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_613 : oddCount 613 12 = 5 ∧ acceleratedOrbit 12 613 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_613 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 613) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_613.1, data_12_613.2]

end Collatz.Research.StoppingAtlas.Batch0240
