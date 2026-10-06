import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0385

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12582. -/
theorem bounds_15_12582 : exactInterval 15 12582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12582 : oddCount 12582 15 = 8 ∧ acceleratedOrbit 15 12582 = 2521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12582) = 3 ^ 8 * m + 2521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12582.1, data_15_12582.2]

/-- Complete interval computation for depth 15, residue 12583. -/
theorem bounds_15_12583 : exactInterval 15 12583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12583 : oddCount 12583 15 = 11 ∧ acceleratedOrbit 15 12583 = 68039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12583) = 3 ^ 11 * m + 68039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12583.1, data_15_12583.2]

/-- Complete interval computation for depth 15, residue 12584. -/
theorem bounds_15_12584 : exactInterval 15 12584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12584 : oddCount 12584 15 = 6 ∧ acceleratedOrbit 15 12584 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12584) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12584.1, data_15_12584.2]

/-- Complete interval computation for depth 15, residue 12585. -/
theorem bounds_15_12585 : exactInterval 15 12585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12585 : oddCount 12585 15 = 9 ∧ acceleratedOrbit 15 12585 = 7561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12585) = 3 ^ 9 * m + 7561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12585.1, data_15_12585.2]

/-- Complete interval computation for depth 15, residue 12586. -/
theorem bounds_15_12586 : exactInterval 15 12586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12586 : oddCount 12586 15 = 6 ∧ acceleratedOrbit 15 12586 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12586) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12586.1, data_15_12586.2]

/-- Complete interval computation for depth 15, residue 12587. -/
theorem bounds_15_12587 : exactInterval 15 12587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12587 : oddCount 12587 15 = 8 ∧ acceleratedOrbit 15 12587 = 2521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12587) = 3 ^ 8 * m + 2521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12587.1, data_15_12587.2]

/-- Complete interval computation for depth 15, residue 12588. -/
theorem bounds_15_12588 : exactInterval 15 12588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12588 : oddCount 12588 15 = 5 ∧ acceleratedOrbit 15 12588 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12588) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12588.1, data_15_12588.2]

/-- Complete interval computation for depth 15, residue 12589. -/
theorem bounds_15_12589 : exactInterval 15 12589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12589 : oddCount 12589 15 = 5 ∧ acceleratedOrbit 15 12589 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12589) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12589.1, data_15_12589.2]

/-- Complete interval computation for depth 15, residue 12590. -/
theorem bounds_15_12590 : exactInterval 15 12590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12590 : oddCount 12590 15 = 5 ∧ acceleratedOrbit 15 12590 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12590) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12590.1, data_15_12590.2]

/-- Complete interval computation for depth 15, residue 12591. -/
theorem bounds_15_12591 : exactInterval 15 12591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12591 : oddCount 12591 15 = 10 ∧ acceleratedOrbit 15 12591 = 22693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12591) = 3 ^ 10 * m + 22693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12591.1, data_15_12591.2]

/-- Complete interval computation for depth 15, residue 12592. -/
theorem bounds_15_12592 : exactInterval 15 12592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12592 : oddCount 12592 15 = 6 ∧ acceleratedOrbit 15 12592 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12592) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12592.1, data_15_12592.2]

/-- Complete interval computation for depth 15, residue 12593. -/
theorem bounds_15_12593 : exactInterval 15 12593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12593 : oddCount 12593 15 = 8 ∧ acceleratedOrbit 15 12593 = 2524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12593) = 3 ^ 8 * m + 2524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12593.1, data_15_12593.2]

/-- Complete interval computation for depth 15, residue 12594. -/
theorem bounds_15_12594 : exactInterval 15 12594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12594 : oddCount 12594 15 = 8 ∧ acceleratedOrbit 15 12594 = 2524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12594) = 3 ^ 8 * m + 2524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12594.1, data_15_12594.2]

/-- Complete interval computation for depth 15, residue 12595. -/
theorem bounds_15_12595 : exactInterval 15 12595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12595 : oddCount 12595 15 = 8 ∧ acceleratedOrbit 15 12595 = 2524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12595) = 3 ^ 8 * m + 2524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12595.1, data_15_12595.2]

/-- Complete interval computation for depth 15, residue 12596. -/
theorem bounds_15_12596 : exactInterval 15 12596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12596 : oddCount 12596 15 = 6 ∧ acceleratedOrbit 15 12596 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12596) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12596.1, data_15_12596.2]

/-- Complete interval computation for depth 15, residue 12597. -/
theorem bounds_15_12597 : exactInterval 15 12597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12597 : oddCount 12597 15 = 6 ∧ acceleratedOrbit 15 12597 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12597) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12597.1, data_15_12597.2]

/-- Complete interval computation for depth 15, residue 12598. -/
theorem bounds_15_12598 : exactInterval 15 12598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12598 : oddCount 12598 15 = 7 ∧ acceleratedOrbit 15 12598 = 841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12598) = 3 ^ 7 * m + 841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12598.1, data_15_12598.2]

/-- Complete interval computation for depth 15, residue 12599. -/
theorem bounds_15_12599 : exactInterval 15 12599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12599 : oddCount 12599 15 = 7 ∧ acceleratedOrbit 15 12599 = 841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12599) = 3 ^ 7 * m + 841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12599.1, data_15_12599.2]

/-- Complete interval computation for depth 15, residue 12600. -/
theorem bounds_15_12600 : exactInterval 15 12600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12600 : oddCount 12600 15 = 6 ∧ acceleratedOrbit 15 12600 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12600) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12600.1, data_15_12600.2]

/-- Complete interval computation for depth 15, residue 12601. -/
theorem bounds_15_12601 : exactInterval 15 12601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12601 : oddCount 12601 15 = 9 ∧ acceleratedOrbit 15 12601 = 7571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12601) = 3 ^ 9 * m + 7571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12601.1, data_15_12601.2]

/-- Complete interval computation for depth 15, residue 12602. -/
theorem bounds_15_12602 : exactInterval 15 12602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12602 : oddCount 12602 15 = 6 ∧ acceleratedOrbit 15 12602 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12602) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12602.1, data_15_12602.2]

/-- Complete interval computation for depth 15, residue 12603. -/
theorem bounds_15_12603 : exactInterval 15 12603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12603 : oddCount 12603 15 = 6 ∧ acceleratedOrbit 15 12603 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12603) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12603.1, data_15_12603.2]

/-- Complete interval computation for depth 15, residue 12604. -/
theorem bounds_15_12604 : exactInterval 15 12604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12604 : oddCount 12604 15 = 6 ∧ acceleratedOrbit 15 12604 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12604) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12604.1, data_15_12604.2]

/-- Complete interval computation for depth 15, residue 12605. -/
theorem bounds_15_12605 : exactInterval 15 12605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12605 : oddCount 12605 15 = 6 ∧ acceleratedOrbit 15 12605 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12605) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12605.1, data_15_12605.2]

/-- Complete interval computation for depth 15, residue 12606. -/
theorem bounds_15_12606 : exactInterval 15 12606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12606 : oddCount 12606 15 = 12 ∧ acceleratedOrbit 15 12606 = 204484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12606) = 3 ^ 12 * m + 204484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12606.1, data_15_12606.2]

/-- Complete interval computation for depth 15, residue 12607. -/
theorem bounds_15_12607 : exactInterval 15 12607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12607 : oddCount 12607 15 = 12 ∧ acceleratedOrbit 15 12607 = 204484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12607) = 3 ^ 12 * m + 204484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12607.1, data_15_12607.2]

/-- Complete interval computation for depth 15, residue 12608. -/
theorem bounds_15_12608 : exactInterval 15 12608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12608 : oddCount 12608 15 = 3 ∧ acceleratedOrbit 15 12608 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12608) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12608.1, data_15_12608.2]

/-- Complete interval computation for depth 15, residue 12609. -/
theorem bounds_15_12609 : exactInterval 15 12609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12609 : oddCount 12609 15 = 6 ∧ acceleratedOrbit 15 12609 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12609) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12609.1, data_15_12609.2]

/-- Complete interval computation for depth 15, residue 12610. -/
theorem bounds_15_12610 : exactInterval 15 12610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12610 : oddCount 12610 15 = 7 ∧ acceleratedOrbit 15 12610 = 842 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12610) = 3 ^ 7 * m + 842 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12610.1, data_15_12610.2]

/-- Complete interval computation for depth 15, residue 12611. -/
theorem bounds_15_12611 : exactInterval 15 12611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12611 : oddCount 12611 15 = 7 ∧ acceleratedOrbit 15 12611 = 842 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12611) = 3 ^ 7 * m + 842 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12611.1, data_15_12611.2]

/-- Complete interval computation for depth 15, residue 12612. -/
theorem bounds_15_12612 : exactInterval 15 12612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12612 : oddCount 12612 15 = 6 ∧ acceleratedOrbit 15 12612 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12612) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12612.1, data_15_12612.2]

/-- Complete interval computation for depth 15, residue 12613. -/
theorem bounds_15_12613 : exactInterval 15 12613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12613 : oddCount 12613 15 = 6 ∧ acceleratedOrbit 15 12613 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12613) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12613.1, data_15_12613.2]

/-- Complete interval computation for depth 15, residue 12614. -/
theorem bounds_15_12614 : exactInterval 15 12614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12614 : oddCount 12614 15 = 6 ∧ acceleratedOrbit 15 12614 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12614) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12614.1, data_15_12614.2]

end Collatz.Research.PassageAtlas.Batch0385
