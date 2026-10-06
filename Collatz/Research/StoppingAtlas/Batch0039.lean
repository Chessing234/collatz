import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0039

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 583. -/
theorem bounds_10_583 : exactInterval 10 583 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_583 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 583) 10 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_583 : oddCount 583 10 = 6 ∧ acceleratedOrbit 10 583 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_583 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 583) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_583.1, data_10_583.2]

/-- Complete interval computation for depth 10, residue 584. -/
theorem bounds_10_584 : exactInterval 10 584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_584 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 584) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_584 : oddCount 584 10 = 4 ∧ acceleratedOrbit 10 584 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_584 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 584) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_584.1, data_10_584.2]

/-- Complete interval computation for depth 10, residue 585. -/
theorem bounds_10_585 : exactInterval 10 585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_585 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 585) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_585 : oddCount 585 10 = 6 ∧ acceleratedOrbit 10 585 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_585 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 585) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_585.1, data_10_585.2]

/-- Complete interval computation for depth 10, residue 586. -/
theorem bounds_10_586 : exactInterval 10 586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_586 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 586) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_586 : oddCount 586 10 = 4 ∧ acceleratedOrbit 10 586 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_586 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 586) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_586.1, data_10_586.2]

/-- Complete interval computation for depth 10, residue 587. -/
theorem bounds_10_587 : exactInterval 10 587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_587 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 587) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_587 : oddCount 587 10 = 4 ∧ acceleratedOrbit 10 587 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_587 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 587) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_587.1, data_10_587.2]

/-- Complete interval computation for depth 10, residue 588. -/
theorem bounds_10_588 : exactInterval 10 588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_588 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 588) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_588 : oddCount 588 10 = 4 ∧ acceleratedOrbit 10 588 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_588 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 588) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_588.1, data_10_588.2]

/-- Complete interval computation for depth 10, residue 589. -/
theorem bounds_10_589 : exactInterval 10 589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_589 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 589) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_589 : oddCount 589 10 = 4 ∧ acceleratedOrbit 10 589 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_589 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 589) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_589.1, data_10_589.2]

/-- Complete interval computation for depth 10, residue 590. -/
theorem bounds_10_590 : exactInterval 10 590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_590 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 590) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_590 : oddCount 590 10 = 6 ∧ acceleratedOrbit 10 590 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_590 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 590) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_590.1, data_10_590.2]

/-- Complete interval computation for depth 10, residue 591. -/
theorem bounds_10_591 : exactInterval 10 591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_591 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 591) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_591 : oddCount 591 10 = 6 ∧ acceleratedOrbit 10 591 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_591 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 591) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_591.1, data_10_591.2]

/-- Complete interval computation for depth 10, residue 592. -/
theorem bounds_10_592 : exactInterval 10 592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_592 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 592) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_592 : oddCount 592 10 = 3 ∧ acceleratedOrbit 10 592 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_592 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 592) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_592.1, data_10_592.2]

/-- Complete interval computation for depth 10, residue 593. -/
theorem bounds_10_593 : exactInterval 10 593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_593 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 593) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_593 : oddCount 593 10 = 6 ∧ acceleratedOrbit 10 593 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_593 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 593) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_593.1, data_10_593.2]

/-- Complete interval computation for depth 10, residue 594. -/
theorem bounds_10_594 : exactInterval 10 594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_594 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 594) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_594 : oddCount 594 10 = 6 ∧ acceleratedOrbit 10 594 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_594 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 594) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_594.1, data_10_594.2]

/-- Complete interval computation for depth 10, residue 595. -/
theorem bounds_10_595 : exactInterval 10 595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_595 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 595) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_595 : oddCount 595 10 = 6 ∧ acceleratedOrbit 10 595 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_595 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 595) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_595.1, data_10_595.2]

/-- Complete interval computation for depth 10, residue 596. -/
theorem bounds_10_596 : exactInterval 10 596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_596 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 596) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_596 : oddCount 596 10 = 3 ∧ acceleratedOrbit 10 596 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_596 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 596) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_596.1, data_10_596.2]

/-- Complete interval computation for depth 10, residue 597. -/
theorem bounds_10_597 : exactInterval 10 597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_597 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 597) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_597 : oddCount 597 10 = 3 ∧ acceleratedOrbit 10 597 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_597 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 597) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_597.1, data_10_597.2]

/-- Complete interval computation for depth 10, residue 598. -/
theorem bounds_10_598 : exactInterval 10 598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_598 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 598) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_598 : oddCount 598 10 = 5 ∧ acceleratedOrbit 10 598 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_598 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 598) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_598.1, data_10_598.2]

end Collatz.Research.StoppingAtlas.Batch0039
