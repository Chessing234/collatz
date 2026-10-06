import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0506

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 588. -/
theorem bounds_13_588 : exactInterval 13 588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_588 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 588) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_588 : oddCount 588 13 = 7 ∧ acceleratedOrbit 13 588 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_588 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 588) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_588.1, data_13_588.2]

/-- Complete interval computation for depth 13, residue 589. -/
theorem bounds_13_589 : exactInterval 13 589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_589 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 589) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_589 : oddCount 589 13 = 7 ∧ acceleratedOrbit 13 589 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_589 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 589) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_589.1, data_13_589.2]

/-- Complete interval computation for depth 13, residue 590. -/
theorem bounds_13_590 : exactInterval 13 590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_590 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 590) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_590 : oddCount 590 13 = 8 ∧ acceleratedOrbit 13 590 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_590 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 590) = 3 ^ 8 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_590.1, data_13_590.2]

/-- Complete interval computation for depth 13, residue 591. -/
theorem bounds_13_591 : exactInterval 13 591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_591 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 591) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_591 : oddCount 591 13 = 8 ∧ acceleratedOrbit 13 591 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_591 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 591) = 3 ^ 8 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_591.1, data_13_591.2]

/-- Complete interval computation for depth 13, residue 592. -/
theorem bounds_13_592 : exactInterval 13 592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_592 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 592) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_592 : oddCount 592 13 = 5 ∧ acceleratedOrbit 13 592 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_592 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 592) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_592.1, data_13_592.2]

/-- Complete interval computation for depth 13, residue 593. -/
theorem bounds_13_593 : exactInterval 13 593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_593 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 593) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_593 : oddCount 593 13 = 8 ∧ acceleratedOrbit 13 593 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_593 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 593) = 3 ^ 8 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_593.1, data_13_593.2]

/-- Complete interval computation for depth 13, residue 594. -/
theorem bounds_13_594 : exactInterval 13 594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_594 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 594) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_594 : oddCount 594 13 = 8 ∧ acceleratedOrbit 13 594 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_594 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 594) = 3 ^ 8 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_594.1, data_13_594.2]

/-- Complete interval computation for depth 13, residue 595. -/
theorem bounds_13_595 : exactInterval 13 595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_595 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 595) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_595 : oddCount 595 13 = 8 ∧ acceleratedOrbit 13 595 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_595 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 595) = 3 ^ 8 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_595.1, data_13_595.2]

/-- Complete interval computation for depth 13, residue 596. -/
theorem bounds_13_596 : exactInterval 13 596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_596 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 596) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_596 : oddCount 596 13 = 5 ∧ acceleratedOrbit 13 596 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_596 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 596) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_596.1, data_13_596.2]

/-- Complete interval computation for depth 13, residue 597. -/
theorem bounds_13_597 : exactInterval 13 597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_597 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 597) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_597 : oddCount 597 13 = 5 ∧ acceleratedOrbit 13 597 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_597 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 597) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_597.1, data_13_597.2]

/-- Complete interval computation for depth 13, residue 598. -/
theorem bounds_13_598 : exactInterval 13 598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_598 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 598) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_598 : oddCount 598 13 = 8 ∧ acceleratedOrbit 13 598 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_598 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 598) = 3 ^ 8 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_598.1, data_13_598.2]

/-- Complete interval computation for depth 13, residue 599. -/
theorem bounds_13_599 : exactInterval 13 599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_599 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 599) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_599 : oddCount 599 13 = 8 ∧ acceleratedOrbit 13 599 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_599 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 599) = 3 ^ 8 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_599.1, data_13_599.2]

/-- Complete interval computation for depth 13, residue 600. -/
theorem bounds_13_600 : exactInterval 13 600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_600 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 600) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_600 : oddCount 600 13 = 3 ∧ acceleratedOrbit 13 600 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_600 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 600) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_600.1, data_13_600.2]

/-- Complete interval computation for depth 13, residue 601. -/
theorem bounds_13_601 : exactInterval 13 601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_601 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 601) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_601 : oddCount 601 13 = 9 ∧ acceleratedOrbit 13 601 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_601 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 601) = 3 ^ 9 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_601.1, data_13_601.2]

/-- Complete interval computation for depth 13, residue 602. -/
theorem bounds_13_602 : exactInterval 13 602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_602 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 602) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_602 : oddCount 602 13 = 3 ∧ acceleratedOrbit 13 602 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_602 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 602) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_602.1, data_13_602.2]

/-- Complete interval computation for depth 13, residue 603. -/
theorem bounds_13_603 : exactInterval 13 603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_603 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 603) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_603 : oddCount 603 13 = 9 ∧ acceleratedOrbit 13 603 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_603 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 603) = 3 ^ 9 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_603.1, data_13_603.2]

end Collatz.Research.StoppingAtlas.Batch0506
