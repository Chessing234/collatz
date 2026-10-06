import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0690

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22577. -/
theorem bounds_15_22577 : exactInterval 15 22577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22577 : oddCount 22577 15 = 9 ∧ acceleratedOrbit 15 22577 = 13567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22577) = 3 ^ 9 * m + 13567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22577.1, data_15_22577.2]

/-- Complete interval computation for depth 15, residue 22578. -/
theorem bounds_15_22578 : exactInterval 15 22578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22578 : oddCount 22578 15 = 9 ∧ acceleratedOrbit 15 22578 = 13567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22578) = 3 ^ 9 * m + 13567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22578.1, data_15_22578.2]

/-- Complete interval computation for depth 15, residue 22579. -/
theorem bounds_15_22579 : exactInterval 15 22579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22579 : oddCount 22579 15 = 9 ∧ acceleratedOrbit 15 22579 = 13567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22579) = 3 ^ 9 * m + 13567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22579.1, data_15_22579.2]

/-- Complete interval computation for depth 15, residue 22580. -/
theorem bounds_15_22580 : exactInterval 15 22580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22580 : oddCount 22580 15 = 4 ∧ acceleratedOrbit 15 22580 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22580) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22580.1, data_15_22580.2]

/-- Complete interval computation for depth 15, residue 22581. -/
theorem bounds_15_22581 : exactInterval 15 22581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22581 : oddCount 22581 15 = 4 ∧ acceleratedOrbit 15 22581 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22581) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22581.1, data_15_22581.2]

/-- Complete interval computation for depth 15, residue 22582. -/
theorem bounds_15_22582 : exactInterval 15 22582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22582 : oddCount 22582 15 = 10 ∧ acceleratedOrbit 15 22582 = 40699 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22582) = 3 ^ 10 * m + 40699 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22582.1, data_15_22582.2]

/-- Complete interval computation for depth 15, residue 22583. -/
theorem bounds_15_22583 : exactInterval 15 22583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22583 : oddCount 22583 15 = 10 ∧ acceleratedOrbit 15 22583 = 40699 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22583) = 3 ^ 10 * m + 40699 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22583.1, data_15_22583.2]

/-- Complete interval computation for depth 15, residue 22584. -/
theorem bounds_15_22584 : exactInterval 15 22584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22584 : oddCount 22584 15 = 8 ∧ acceleratedOrbit 15 22584 = 4526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22584) = 3 ^ 8 * m + 4526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22584.1, data_15_22584.2]

/-- Complete interval computation for depth 15, residue 22585. -/
theorem bounds_15_22585 : exactInterval 15 22585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22585 : oddCount 22585 15 = 6 ∧ acceleratedOrbit 15 22585 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22585) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22585.1, data_15_22585.2]

/-- Complete interval computation for depth 15, residue 22586. -/
theorem bounds_15_22586 : exactInterval 15 22586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22586 : oddCount 22586 15 = 8 ∧ acceleratedOrbit 15 22586 = 4526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22586) = 3 ^ 8 * m + 4526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22586.1, data_15_22586.2]

/-- Complete interval computation for depth 15, residue 22587. -/
theorem bounds_15_22587 : exactInterval 15 22587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22587 : oddCount 22587 15 = 9 ∧ acceleratedOrbit 15 22587 = 13571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22587) = 3 ^ 9 * m + 13571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22587.1, data_15_22587.2]

/-- Complete interval computation for depth 15, residue 22588. -/
theorem bounds_15_22588 : exactInterval 15 22588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22588 : oddCount 22588 15 = 8 ∧ acceleratedOrbit 15 22588 = 4526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22588) = 3 ^ 8 * m + 4526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22588.1, data_15_22588.2]

/-- Complete interval computation for depth 15, residue 22589. -/
theorem bounds_15_22589 : exactInterval 15 22589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22589 : oddCount 22589 15 = 8 ∧ acceleratedOrbit 15 22589 = 4526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22589) = 3 ^ 8 * m + 4526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22589.1, data_15_22589.2]

/-- Complete interval computation for depth 15, residue 22590. -/
theorem bounds_15_22590 : exactInterval 15 22590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22590 : oddCount 22590 15 = 11 ∧ acceleratedOrbit 15 22590 = 122138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22590) = 3 ^ 11 * m + 122138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22590.1, data_15_22590.2]

/-- Complete interval computation for depth 15, residue 22591. -/
theorem bounds_15_22591 : exactInterval 15 22591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22591 : oddCount 22591 15 = 11 ∧ acceleratedOrbit 15 22591 = 122138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22591) = 3 ^ 11 * m + 122138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22591.1, data_15_22591.2]

/-- Complete interval computation for depth 15, residue 22592. -/
theorem bounds_15_22592 : exactInterval 15 22592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22592 : oddCount 22592 15 = 6 ∧ acceleratedOrbit 15 22592 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22592) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22592.1, data_15_22592.2]

/-- Complete interval computation for depth 15, residue 22593. -/
theorem bounds_15_22593 : exactInterval 15 22593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22593 : oddCount 22593 15 = 8 ∧ acceleratedOrbit 15 22593 = 4526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22593) = 3 ^ 8 * m + 4526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22593.1, data_15_22593.2]

/-- Complete interval computation for depth 15, residue 22594. -/
theorem bounds_15_22594 : exactInterval 15 22594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22594 : oddCount 22594 15 = 8 ∧ acceleratedOrbit 15 22594 = 4526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22594) = 3 ^ 8 * m + 4526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22594.1, data_15_22594.2]

/-- Complete interval computation for depth 15, residue 22595. -/
theorem bounds_15_22595 : exactInterval 15 22595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22595 : oddCount 22595 15 = 8 ∧ acceleratedOrbit 15 22595 = 4526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22595) = 3 ^ 8 * m + 4526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22595.1, data_15_22595.2]

/-- Complete interval computation for depth 15, residue 22596. -/
theorem bounds_15_22596 : exactInterval 15 22596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22596 : oddCount 22596 15 = 4 ∧ acceleratedOrbit 15 22596 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22596) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22596.1, data_15_22596.2]

/-- Complete interval computation for depth 15, residue 22597. -/
theorem bounds_15_22597 : exactInterval 15 22597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22597 : oddCount 22597 15 = 4 ∧ acceleratedOrbit 15 22597 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22597) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22597.1, data_15_22597.2]

/-- Complete interval computation for depth 15, residue 22598. -/
theorem bounds_15_22598 : exactInterval 15 22598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22598 : oddCount 22598 15 = 4 ∧ acceleratedOrbit 15 22598 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22598) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22598.1, data_15_22598.2]

/-- Complete interval computation for depth 15, residue 22599. -/
theorem bounds_15_22599 : exactInterval 15 22599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22599 : oddCount 22599 15 = 9 ∧ acceleratedOrbit 15 22599 = 13576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22599) = 3 ^ 9 * m + 13576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22599.1, data_15_22599.2]

/-- Complete interval computation for depth 15, residue 22600. -/
theorem bounds_15_22600 : exactInterval 15 22600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22600 : oddCount 22600 15 = 8 ∧ acceleratedOrbit 15 22600 = 4529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22600) = 3 ^ 8 * m + 4529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22600.1, data_15_22600.2]

/-- Complete interval computation for depth 15, residue 22601. -/
theorem bounds_15_22601 : exactInterval 15 22601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22601 : oddCount 22601 15 = 10 ∧ acceleratedOrbit 15 22601 = 40733 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22601) = 3 ^ 10 * m + 40733 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22601.1, data_15_22601.2]

/-- Complete interval computation for depth 15, residue 22602. -/
theorem bounds_15_22602 : exactInterval 15 22602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22602 : oddCount 22602 15 = 8 ∧ acceleratedOrbit 15 22602 = 4529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22602) = 3 ^ 8 * m + 4529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22602.1, data_15_22602.2]

/-- Complete interval computation for depth 15, residue 22603. -/
theorem bounds_15_22603 : exactInterval 15 22603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22603 : oddCount 22603 15 = 4 ∧ acceleratedOrbit 15 22603 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22603) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22603.1, data_15_22603.2]

/-- Complete interval computation for depth 15, residue 22604. -/
theorem bounds_15_22604 : exactInterval 15 22604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22604 : oddCount 22604 15 = 8 ∧ acceleratedOrbit 15 22604 = 4529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22604) = 3 ^ 8 * m + 4529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22604.1, data_15_22604.2]

/-- Complete interval computation for depth 15, residue 22605. -/
theorem bounds_15_22605 : exactInterval 15 22605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22605 : oddCount 22605 15 = 8 ∧ acceleratedOrbit 15 22605 = 4529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22605) = 3 ^ 8 * m + 4529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22605.1, data_15_22605.2]

/-- Complete interval computation for depth 15, residue 22606. -/
theorem bounds_15_22606 : exactInterval 15 22606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22606 : oddCount 22606 15 = 6 ∧ acceleratedOrbit 15 22606 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22606) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22606.1, data_15_22606.2]

/-- Complete interval computation for depth 15, residue 22607. -/
theorem bounds_15_22607 : exactInterval 15 22607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22607 : oddCount 22607 15 = 6 ∧ acceleratedOrbit 15 22607 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22607) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22607.1, data_15_22607.2]

/-- Complete interval computation for depth 15, residue 22608. -/
theorem bounds_15_22608 : exactInterval 15 22608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22608 : oddCount 22608 15 = 6 ∧ acceleratedOrbit 15 22608 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22608) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22608.1, data_15_22608.2]

end Collatz.Research.PassageAtlas.Batch0690
