import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0239

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 583. -/
theorem bounds_12_583 : exactInterval 12 583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_583 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 583) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_583 : oddCount 583 12 = 6 ∧ acceleratedOrbit 12 583 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_583 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 583) = 3 ^ 6 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_583.1, data_12_583.2]

/-- Complete interval computation for depth 12, residue 584. -/
theorem bounds_12_584 : exactInterval 12 584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_584 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 584) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_584 : oddCount 584 12 = 6 ∧ acceleratedOrbit 12 584 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_584 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 584) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_584.1, data_12_584.2]

/-- Complete interval computation for depth 12, residue 585. -/
theorem bounds_12_585 : exactInterval 12 585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_585 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 585) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_585 : oddCount 585 12 = 7 ∧ acceleratedOrbit 12 585 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_585 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 585) = 3 ^ 7 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_585.1, data_12_585.2]

/-- Complete interval computation for depth 12, residue 586. -/
theorem bounds_12_586 : exactInterval 12 586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_586 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 586) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_586 : oddCount 586 12 = 6 ∧ acceleratedOrbit 12 586 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_586 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 586) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_586.1, data_12_586.2]

/-- Complete interval computation for depth 12, residue 587. -/
theorem bounds_12_587 : exactInterval 12 587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_587 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 587) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_587 : oddCount 587 12 = 6 ∧ acceleratedOrbit 12 587 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_587 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 587) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_587.1, data_12_587.2]

/-- Complete interval computation for depth 12, residue 588. -/
theorem bounds_12_588 : exactInterval 12 588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_588 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 588) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_588 : oddCount 588 12 = 6 ∧ acceleratedOrbit 12 588 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_588 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 588) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_588.1, data_12_588.2]

/-- Complete interval computation for depth 12, residue 589. -/
theorem bounds_12_589 : exactInterval 12 589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_589 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 589) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_589 : oddCount 589 12 = 6 ∧ acceleratedOrbit 12 589 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_589 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 589) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_589.1, data_12_589.2]

/-- Complete interval computation for depth 12, residue 590. -/
theorem bounds_12_590 : exactInterval 12 590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_590 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 590) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_590 : oddCount 590 12 = 7 ∧ acceleratedOrbit 12 590 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_590 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 590) = 3 ^ 7 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_590.1, data_12_590.2]

/-- Complete interval computation for depth 12, residue 591. -/
theorem bounds_12_591 : exactInterval 12 591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_591 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 591) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_591 : oddCount 591 12 = 7 ∧ acceleratedOrbit 12 591 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_591 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 591) = 3 ^ 7 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_591.1, data_12_591.2]

/-- Complete interval computation for depth 12, residue 592. -/
theorem bounds_12_592 : exactInterval 12 592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_592 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 592) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_592 : oddCount 592 12 = 4 ∧ acceleratedOrbit 12 592 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_592 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 592) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_592.1, data_12_592.2]

/-- Complete interval computation for depth 12, residue 593. -/
theorem bounds_12_593 : exactInterval 12 593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_593 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 593) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_593 : oddCount 593 12 = 7 ∧ acceleratedOrbit 12 593 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_593 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 593) = 3 ^ 7 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_593.1, data_12_593.2]

/-- Complete interval computation for depth 12, residue 594. -/
theorem bounds_12_594 : exactInterval 12 594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_594 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 594) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_594 : oddCount 594 12 = 7 ∧ acceleratedOrbit 12 594 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_594 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 594) = 3 ^ 7 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_594.1, data_12_594.2]

/-- Complete interval computation for depth 12, residue 595. -/
theorem bounds_12_595 : exactInterval 12 595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_595 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 595) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_595 : oddCount 595 12 = 7 ∧ acceleratedOrbit 12 595 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_595 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 595) = 3 ^ 7 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_595.1, data_12_595.2]

/-- Complete interval computation for depth 12, residue 596. -/
theorem bounds_12_596 : exactInterval 12 596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_596 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 596) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_596 : oddCount 596 12 = 4 ∧ acceleratedOrbit 12 596 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_596 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 596) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_596.1, data_12_596.2]

/-- Complete interval computation for depth 12, residue 597. -/
theorem bounds_12_597 : exactInterval 12 597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_597 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 597) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_597 : oddCount 597 12 = 4 ∧ acceleratedOrbit 12 597 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_597 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 597) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_597.1, data_12_597.2]

/-- Complete interval computation for depth 12, residue 598. -/
theorem bounds_12_598 : exactInterval 12 598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_598 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 598) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_598 : oddCount 598 12 = 7 ∧ acceleratedOrbit 12 598 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_598 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 598) = 3 ^ 7 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_598.1, data_12_598.2]

end Collatz.Research.StoppingAtlas.Batch0239
