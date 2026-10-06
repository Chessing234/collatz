import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0324

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10584. -/
theorem bounds_15_10584 : exactInterval 15 10584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10584 : oddCount 10584 15 = 6 ∧ acceleratedOrbit 15 10584 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10584) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10584.1, data_15_10584.2]

/-- Complete interval computation for depth 15, residue 10585. -/
theorem bounds_15_10585 : exactInterval 15 10585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10585 : oddCount 10585 15 = 7 ∧ acceleratedOrbit 15 10585 = 707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10585) = 3 ^ 7 * m + 707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10585.1, data_15_10585.2]

/-- Complete interval computation for depth 15, residue 10586. -/
theorem bounds_15_10586 : exactInterval 15 10586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10586 : oddCount 10586 15 = 6 ∧ acceleratedOrbit 15 10586 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10586) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10586.1, data_15_10586.2]

/-- Complete interval computation for depth 15, residue 10587. -/
theorem bounds_15_10587 : exactInterval 15 10587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10587 : oddCount 10587 15 = 9 ∧ acceleratedOrbit 15 10587 = 6362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10587) = 3 ^ 9 * m + 6362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10587.1, data_15_10587.2]

/-- Complete interval computation for depth 15, residue 10588. -/
theorem bounds_15_10588 : exactInterval 15 10588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10588 : oddCount 10588 15 = 6 ∧ acceleratedOrbit 15 10588 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10588) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10588.1, data_15_10588.2]

/-- Complete interval computation for depth 15, residue 10589. -/
theorem bounds_15_10589 : exactInterval 15 10589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10589 : oddCount 10589 15 = 6 ∧ acceleratedOrbit 15 10589 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10589) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10589.1, data_15_10589.2]

/-- Complete interval computation for depth 15, residue 10590. -/
theorem bounds_15_10590 : exactInterval 15 10590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10590 : oddCount 10590 15 = 7 ∧ acceleratedOrbit 15 10590 = 707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10590) = 3 ^ 7 * m + 707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10590.1, data_15_10590.2]

/-- Complete interval computation for depth 15, residue 10591. -/
theorem bounds_15_10591 : exactInterval 15 10591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10591 : oddCount 10591 15 = 7 ∧ acceleratedOrbit 15 10591 = 707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10591) = 3 ^ 7 * m + 707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10591.1, data_15_10591.2]

/-- Complete interval computation for depth 15, residue 10592. -/
theorem bounds_15_10592 : exactInterval 15 10592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10592 : oddCount 10592 15 = 5 ∧ acceleratedOrbit 15 10592 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10592) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10592.1, data_15_10592.2]

/-- Complete interval computation for depth 15, residue 10593. -/
theorem bounds_15_10593 : exactInterval 15 10593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10593 : oddCount 10593 15 = 9 ∧ acceleratedOrbit 15 10593 = 6365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10593) = 3 ^ 9 * m + 6365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10593.1, data_15_10593.2]

/-- Complete interval computation for depth 15, residue 10594. -/
theorem bounds_15_10594 : exactInterval 15 10594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10594 : oddCount 10594 15 = 8 ∧ acceleratedOrbit 15 10594 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10594) = 3 ^ 8 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10594.1, data_15_10594.2]

/-- Complete interval computation for depth 15, residue 10595. -/
theorem bounds_15_10595 : exactInterval 15 10595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10595 : oddCount 10595 15 = 8 ∧ acceleratedOrbit 15 10595 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10595) = 3 ^ 8 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10595.1, data_15_10595.2]

/-- Complete interval computation for depth 15, residue 10596. -/
theorem bounds_15_10596 : exactInterval 15 10596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10596 : oddCount 10596 15 = 8 ∧ acceleratedOrbit 15 10596 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10596) = 3 ^ 8 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10596.1, data_15_10596.2]

/-- Complete interval computation for depth 15, residue 10597. -/
theorem bounds_15_10597 : exactInterval 15 10597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10597 : oddCount 10597 15 = 8 ∧ acceleratedOrbit 15 10597 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10597) = 3 ^ 8 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10597.1, data_15_10597.2]

/-- Complete interval computation for depth 15, residue 10598. -/
theorem bounds_15_10598 : exactInterval 15 10598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10598 : oddCount 10598 15 = 8 ∧ acceleratedOrbit 15 10598 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10598) = 3 ^ 8 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10598.1, data_15_10598.2]

/-- Complete interval computation for depth 15, residue 10599. -/
theorem bounds_15_10599 : exactInterval 15 10599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10599 : oddCount 10599 15 = 11 ∧ acceleratedOrbit 15 10599 = 57307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10599) = 3 ^ 11 * m + 57307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10599.1, data_15_10599.2]

/-- Complete interval computation for depth 15, residue 10600. -/
theorem bounds_15_10600 : exactInterval 15 10600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10600 : oddCount 10600 15 = 5 ∧ acceleratedOrbit 15 10600 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10600) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10600.1, data_15_10600.2]

/-- Complete interval computation for depth 15, residue 10601. -/
theorem bounds_15_10601 : exactInterval 15 10601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10601 : oddCount 10601 15 = 6 ∧ acceleratedOrbit 15 10601 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10601) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10601.1, data_15_10601.2]

/-- Complete interval computation for depth 15, residue 10602. -/
theorem bounds_15_10602 : exactInterval 15 10602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10602 : oddCount 10602 15 = 5 ∧ acceleratedOrbit 15 10602 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10602) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10602.1, data_15_10602.2]

/-- Complete interval computation for depth 15, residue 10603. -/
theorem bounds_15_10603 : exactInterval 15 10603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10603 : oddCount 10603 15 = 10 ∧ acceleratedOrbit 15 10603 = 19115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10603) = 3 ^ 10 * m + 19115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10603.1, data_15_10603.2]

/-- Complete interval computation for depth 15, residue 10604. -/
theorem bounds_15_10604 : exactInterval 15 10604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10604 : oddCount 10604 15 = 9 ∧ acceleratedOrbit 15 10604 = 6374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10604) = 3 ^ 9 * m + 6374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10604.1, data_15_10604.2]

/-- Complete interval computation for depth 15, residue 10605. -/
theorem bounds_15_10605 : exactInterval 15 10605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10605 : oddCount 10605 15 = 9 ∧ acceleratedOrbit 15 10605 = 6374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10605) = 3 ^ 9 * m + 6374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10605.1, data_15_10605.2]

/-- Complete interval computation for depth 15, residue 10606. -/
theorem bounds_15_10606 : exactInterval 15 10606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10606 : oddCount 10606 15 = 9 ∧ acceleratedOrbit 15 10606 = 6374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10606) = 3 ^ 9 * m + 6374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10606.1, data_15_10606.2]

/-- Complete interval computation for depth 15, residue 10607. -/
theorem bounds_15_10607 : exactInterval 15 10607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10607 : oddCount 10607 15 = 6 ∧ acceleratedOrbit 15 10607 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10607) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10607.1, data_15_10607.2]

/-- Complete interval computation for depth 15, residue 10608. -/
theorem bounds_15_10608 : exactInterval 15 10608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10608 : oddCount 10608 15 = 5 ∧ acceleratedOrbit 15 10608 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10608) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10608.1, data_15_10608.2]

/-- Complete interval computation for depth 15, residue 10609. -/
theorem bounds_15_10609 : exactInterval 15 10609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10609 : oddCount 10609 15 = 5 ∧ acceleratedOrbit 15 10609 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10609) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10609.1, data_15_10609.2]

/-- Complete interval computation for depth 15, residue 10610. -/
theorem bounds_15_10610 : exactInterval 15 10610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10610 : oddCount 10610 15 = 8 ∧ acceleratedOrbit 15 10610 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10610) = 3 ^ 8 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10610.1, data_15_10610.2]

/-- Complete interval computation for depth 15, residue 10611. -/
theorem bounds_15_10611 : exactInterval 15 10611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10611 : oddCount 10611 15 = 8 ∧ acceleratedOrbit 15 10611 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10611) = 3 ^ 8 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10611.1, data_15_10611.2]

/-- Complete interval computation for depth 15, residue 10612. -/
theorem bounds_15_10612 : exactInterval 15 10612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10612 : oddCount 10612 15 = 5 ∧ acceleratedOrbit 15 10612 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10612) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10612.1, data_15_10612.2]

/-- Complete interval computation for depth 15, residue 10613. -/
theorem bounds_15_10613 : exactInterval 15 10613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10613 : oddCount 10613 15 = 5 ∧ acceleratedOrbit 15 10613 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10613) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10613.1, data_15_10613.2]

/-- Complete interval computation for depth 15, residue 10614. -/
theorem bounds_15_10614 : exactInterval 15 10614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10614 : oddCount 10614 15 = 10 ∧ acceleratedOrbit 15 10614 = 19136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10614) = 3 ^ 10 * m + 19136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10614.1, data_15_10614.2]

/-- Complete interval computation for depth 15, residue 10615. -/
theorem bounds_15_10615 : exactInterval 15 10615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10615 : oddCount 10615 15 = 10 ∧ acceleratedOrbit 15 10615 = 19136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10615) = 3 ^ 10 * m + 19136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10615.1, data_15_10615.2]

end Collatz.Research.PassageAtlas.Batch0324
