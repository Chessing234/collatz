import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0106

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 588. -/
theorem bounds_11_588 : exactInterval 11 588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_588 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 588) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_588 : oddCount 588 11 = 5 ∧ acceleratedOrbit 11 588 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_588 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 588) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_588.1, data_11_588.2]

/-- Complete interval computation for depth 11, residue 589. -/
theorem bounds_11_589 : exactInterval 11 589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_589 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 589) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_589 : oddCount 589 11 = 5 ∧ acceleratedOrbit 11 589 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_589 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 589) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_589.1, data_11_589.2]

/-- Complete interval computation for depth 11, residue 590. -/
theorem bounds_11_590 : exactInterval 11 590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_590 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 590) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_590 : oddCount 590 11 = 6 ∧ acceleratedOrbit 11 590 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_590 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 590) = 3 ^ 6 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_590.1, data_11_590.2]

/-- Complete interval computation for depth 11, residue 591. -/
theorem bounds_11_591 : exactInterval 11 591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_591 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 591) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_591 : oddCount 591 11 = 6 ∧ acceleratedOrbit 11 591 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_591 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 591) = 3 ^ 6 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_591.1, data_11_591.2]

/-- Complete interval computation for depth 11, residue 592. -/
theorem bounds_11_592 : exactInterval 11 592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_592 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 592) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_592 : oddCount 592 11 = 4 ∧ acceleratedOrbit 11 592 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_592 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 592) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_592.1, data_11_592.2]

/-- Complete interval computation for depth 11, residue 593. -/
theorem bounds_11_593 : exactInterval 11 593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_593 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 593) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_593 : oddCount 593 11 = 7 ∧ acceleratedOrbit 11 593 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_593 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 593) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_593.1, data_11_593.2]

/-- Complete interval computation for depth 11, residue 594. -/
theorem bounds_11_594 : exactInterval 11 594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_594 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 594) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_594 : oddCount 594 11 = 7 ∧ acceleratedOrbit 11 594 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_594 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 594) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_594.1, data_11_594.2]

/-- Complete interval computation for depth 11, residue 595. -/
theorem bounds_11_595 : exactInterval 11 595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_595 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 595) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_595 : oddCount 595 11 = 7 ∧ acceleratedOrbit 11 595 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_595 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 595) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_595.1, data_11_595.2]

/-- Complete interval computation for depth 11, residue 596. -/
theorem bounds_11_596 : exactInterval 11 596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_596 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 596) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_596 : oddCount 596 11 = 4 ∧ acceleratedOrbit 11 596 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_596 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 596) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_596.1, data_11_596.2]

/-- Complete interval computation for depth 11, residue 597. -/
theorem bounds_11_597 : exactInterval 11 597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_597 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 597) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_597 : oddCount 597 11 = 4 ∧ acceleratedOrbit 11 597 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_597 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 597) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_597.1, data_11_597.2]

/-- Complete interval computation for depth 11, residue 598. -/
theorem bounds_11_598 : exactInterval 11 598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_598 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 598) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_598 : oddCount 598 11 = 6 ∧ acceleratedOrbit 11 598 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_598 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 598) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_598.1, data_11_598.2]

/-- Complete interval computation for depth 11, residue 599. -/
theorem bounds_11_599 : exactInterval 11 599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_599 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 599) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_599 : oddCount 599 11 = 6 ∧ acceleratedOrbit 11 599 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_599 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 599) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_599.1, data_11_599.2]

/-- Complete interval computation for depth 11, residue 600. -/
theorem bounds_11_600 : exactInterval 11 600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_600 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 600) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_600 : oddCount 600 11 = 3 ∧ acceleratedOrbit 11 600 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_600 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 600) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_600.1, data_11_600.2]

/-- Complete interval computation for depth 11, residue 601. -/
theorem bounds_11_601 : exactInterval 11 601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_601 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 601) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_601 : oddCount 601 11 = 7 ∧ acceleratedOrbit 11 601 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_601 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 601) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_601.1, data_11_601.2]

/-- Complete interval computation for depth 11, residue 602. -/
theorem bounds_11_602 : exactInterval 11 602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_602 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 602) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_602 : oddCount 602 11 = 3 ∧ acceleratedOrbit 11 602 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_602 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 602) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_602.1, data_11_602.2]

/-- Complete interval computation for depth 11, residue 603. -/
theorem bounds_11_603 : exactInterval 11 603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_603 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 603) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_603 : oddCount 603 11 = 8 ∧ acceleratedOrbit 11 603 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_603 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 603) = 3 ^ 8 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_603.1, data_11_603.2]

end Collatz.Research.StoppingAtlas.Batch0106
