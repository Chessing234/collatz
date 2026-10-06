import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0660

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21594. -/
theorem bounds_15_21594 : exactInterval 15 21594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21594 : oddCount 21594 15 = 6 ∧ acceleratedOrbit 15 21594 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21594) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21594.1, data_15_21594.2]

/-- Complete interval computation for depth 15, residue 21595. -/
theorem bounds_15_21595 : exactInterval 15 21595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21595 : oddCount 21595 15 = 10 ∧ acceleratedOrbit 15 21595 = 38918 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21595) = 3 ^ 10 * m + 38918 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21595.1, data_15_21595.2]

/-- Complete interval computation for depth 15, residue 21596. -/
theorem bounds_15_21596 : exactInterval 15 21596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21596 : oddCount 21596 15 = 6 ∧ acceleratedOrbit 15 21596 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21596) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21596.1, data_15_21596.2]

/-- Complete interval computation for depth 15, residue 21597. -/
theorem bounds_15_21597 : exactInterval 15 21597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21597 : oddCount 21597 15 = 6 ∧ acceleratedOrbit 15 21597 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21597) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21597.1, data_15_21597.2]

/-- Complete interval computation for depth 15, residue 21598. -/
theorem bounds_15_21598 : exactInterval 15 21598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21598 : oddCount 21598 15 = 8 ∧ acceleratedOrbit 15 21598 = 4325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21598) = 3 ^ 8 * m + 4325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21598.1, data_15_21598.2]

/-- Complete interval computation for depth 15, residue 21599. -/
theorem bounds_15_21599 : exactInterval 15 21599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21599 : oddCount 21599 15 = 8 ∧ acceleratedOrbit 15 21599 = 4325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21599) = 3 ^ 8 * m + 4325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21599.1, data_15_21599.2]

/-- Complete interval computation for depth 15, residue 21600. -/
theorem bounds_15_21600 : exactInterval 15 21600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21600 : oddCount 21600 15 = 6 ∧ acceleratedOrbit 15 21600 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21600) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21600.1, data_15_21600.2]

/-- Complete interval computation for depth 15, residue 21601. -/
theorem bounds_15_21601 : exactInterval 15 21601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21601 : oddCount 21601 15 = 7 ∧ acceleratedOrbit 15 21601 = 1442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21601) = 3 ^ 7 * m + 1442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21601.1, data_15_21601.2]

/-- Complete interval computation for depth 15, residue 21602. -/
theorem bounds_15_21602 : exactInterval 15 21602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21602 : oddCount 21602 15 = 9 ∧ acceleratedOrbit 15 21602 = 12986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21602) = 3 ^ 9 * m + 12986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21602.1, data_15_21602.2]

/-- Complete interval computation for depth 15, residue 21603. -/
theorem bounds_15_21603 : exactInterval 15 21603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21603 : oddCount 21603 15 = 9 ∧ acceleratedOrbit 15 21603 = 12986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21603) = 3 ^ 9 * m + 12986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21603.1, data_15_21603.2]

/-- Complete interval computation for depth 15, residue 21604. -/
theorem bounds_15_21604 : exactInterval 15 21604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21604 : oddCount 21604 15 = 9 ∧ acceleratedOrbit 15 21604 = 12986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21604) = 3 ^ 9 * m + 12986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21604.1, data_15_21604.2]

/-- Complete interval computation for depth 15, residue 21605. -/
theorem bounds_15_21605 : exactInterval 15 21605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21605 : oddCount 21605 15 = 9 ∧ acceleratedOrbit 15 21605 = 12986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21605) = 3 ^ 9 * m + 12986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21605.1, data_15_21605.2]

/-- Complete interval computation for depth 15, residue 21606. -/
theorem bounds_15_21606 : exactInterval 15 21606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21606 : oddCount 21606 15 = 9 ∧ acceleratedOrbit 15 21606 = 12986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21606) = 3 ^ 9 * m + 12986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21606.1, data_15_21606.2]

/-- Complete interval computation for depth 15, residue 21607. -/
theorem bounds_15_21607 : exactInterval 15 21607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21607 : oddCount 21607 15 = 10 ∧ acceleratedOrbit 15 21607 = 38939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21607) = 3 ^ 10 * m + 38939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21607.1, data_15_21607.2]

/-- Complete interval computation for depth 15, residue 21608. -/
theorem bounds_15_21608 : exactInterval 15 21608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21608 : oddCount 21608 15 = 6 ∧ acceleratedOrbit 15 21608 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21608) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21608.1, data_15_21608.2]

/-- Complete interval computation for depth 15, residue 21609. -/
theorem bounds_15_21609 : exactInterval 15 21609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21609 : oddCount 21609 15 = 9 ∧ acceleratedOrbit 15 21609 = 12982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21609) = 3 ^ 9 * m + 12982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21609.1, data_15_21609.2]

/-- Complete interval computation for depth 15, residue 21610. -/
theorem bounds_15_21610 : exactInterval 15 21610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21610 : oddCount 21610 15 = 6 ∧ acceleratedOrbit 15 21610 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21610) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21610.1, data_15_21610.2]

/-- Complete interval computation for depth 15, residue 21611. -/
theorem bounds_15_21611 : exactInterval 15 21611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21611 : oddCount 21611 15 = 8 ∧ acceleratedOrbit 15 21611 = 4328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21611) = 3 ^ 8 * m + 4328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21611.1, data_15_21611.2]

/-- Complete interval computation for depth 15, residue 21612. -/
theorem bounds_15_21612 : exactInterval 15 21612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21612 : oddCount 21612 15 = 10 ∧ acceleratedOrbit 15 21612 = 38956 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21612) = 3 ^ 10 * m + 38956 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21612.1, data_15_21612.2]

/-- Complete interval computation for depth 15, residue 21613. -/
theorem bounds_15_21613 : exactInterval 15 21613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21613 : oddCount 21613 15 = 10 ∧ acceleratedOrbit 15 21613 = 38956 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21613) = 3 ^ 10 * m + 38956 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21613.1, data_15_21613.2]

/-- Complete interval computation for depth 15, residue 21614. -/
theorem bounds_15_21614 : exactInterval 15 21614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21614 : oddCount 21614 15 = 10 ∧ acceleratedOrbit 15 21614 = 38956 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21614) = 3 ^ 10 * m + 38956 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21614.1, data_15_21614.2]

/-- Complete interval computation for depth 15, residue 21615. -/
theorem bounds_15_21615 : exactInterval 15 21615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21615 : oddCount 21615 15 = 10 ∧ acceleratedOrbit 15 21615 = 38954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21615) = 3 ^ 10 * m + 38954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21615.1, data_15_21615.2]

/-- Complete interval computation for depth 15, residue 21616. -/
theorem bounds_15_21616 : exactInterval 15 21616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21616 : oddCount 21616 15 = 8 ∧ acceleratedOrbit 15 21616 = 4333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21616) = 3 ^ 8 * m + 4333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21616.1, data_15_21616.2]

/-- Complete interval computation for depth 15, residue 21617. -/
theorem bounds_15_21617 : exactInterval 15 21617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21617 : oddCount 21617 15 = 6 ∧ acceleratedOrbit 15 21617 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21617) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21617.1, data_15_21617.2]

/-- Complete interval computation for depth 15, residue 21618. -/
theorem bounds_15_21618 : exactInterval 15 21618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21618 : oddCount 21618 15 = 8 ∧ acceleratedOrbit 15 21618 = 4330 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21618) = 3 ^ 8 * m + 4330 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21618.1, data_15_21618.2]

/-- Complete interval computation for depth 15, residue 21619. -/
theorem bounds_15_21619 : exactInterval 15 21619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21619 : oddCount 21619 15 = 8 ∧ acceleratedOrbit 15 21619 = 4330 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21619) = 3 ^ 8 * m + 4330 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21619.1, data_15_21619.2]

/-- Complete interval computation for depth 15, residue 21620. -/
theorem bounds_15_21620 : exactInterval 15 21620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21620 : oddCount 21620 15 = 8 ∧ acceleratedOrbit 15 21620 = 4333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21620) = 3 ^ 8 * m + 4333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21620.1, data_15_21620.2]

/-- Complete interval computation for depth 15, residue 21621. -/
theorem bounds_15_21621 : exactInterval 15 21621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21621 : oddCount 21621 15 = 8 ∧ acceleratedOrbit 15 21621 = 4333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21621) = 3 ^ 8 * m + 4333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21621.1, data_15_21621.2]

/-- Complete interval computation for depth 15, residue 21622. -/
theorem bounds_15_21622 : exactInterval 15 21622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21622 : oddCount 21622 15 = 7 ∧ acceleratedOrbit 15 21622 = 1444 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21622) = 3 ^ 7 * m + 1444 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21622.1, data_15_21622.2]

/-- Complete interval computation for depth 15, residue 21623. -/
theorem bounds_15_21623 : exactInterval 15 21623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21623 : oddCount 21623 15 = 7 ∧ acceleratedOrbit 15 21623 = 1444 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21623) = 3 ^ 7 * m + 1444 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21623.1, data_15_21623.2]

/-- Complete interval computation for depth 15, residue 21624. -/
theorem bounds_15_21624 : exactInterval 15 21624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21624 : oddCount 21624 15 = 8 ∧ acceleratedOrbit 15 21624 = 4333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21624) = 3 ^ 8 * m + 4333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21624.1, data_15_21624.2]

/-- Complete interval computation for depth 15, residue 21625. -/
theorem bounds_15_21625 : exactInterval 15 21625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21625 : oddCount 21625 15 = 10 ∧ acceleratedOrbit 15 21625 = 38974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21625) = 3 ^ 10 * m + 38974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21625.1, data_15_21625.2]

end Collatz.Research.PassageAtlas.Batch0660
