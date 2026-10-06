import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0751

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24576. -/
theorem bounds_15_24576 : exactInterval 15 24576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24576 : oddCount 24576 15 = 2 ∧ acceleratedOrbit 15 24576 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24576) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24576.1, data_15_24576.2]

/-- Complete interval computation for depth 15, residue 24577. -/
theorem bounds_15_24577 : exactInterval 15 24577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24577 : oddCount 24577 15 = 9 ∧ acceleratedOrbit 15 24577 = 14768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24577) = 3 ^ 9 * m + 14768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24577.1, data_15_24577.2]

/-- Complete interval computation for depth 15, residue 24578. -/
theorem bounds_15_24578 : exactInterval 15 24578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24578 : oddCount 24578 15 = 6 ∧ acceleratedOrbit 15 24578 = 547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24578) = 3 ^ 6 * m + 547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24578.1, data_15_24578.2]

/-- Complete interval computation for depth 15, residue 24579. -/
theorem bounds_15_24579 : exactInterval 15 24579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24579 : oddCount 24579 15 = 6 ∧ acceleratedOrbit 15 24579 = 547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24579) = 3 ^ 6 * m + 547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24579.1, data_15_24579.2]

/-- Complete interval computation for depth 15, residue 24580. -/
theorem bounds_15_24580 : exactInterval 15 24580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24580 : oddCount 24580 15 = 7 ∧ acceleratedOrbit 15 24580 = 1642 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24580) = 3 ^ 7 * m + 1642 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24580.1, data_15_24580.2]

/-- Complete interval computation for depth 15, residue 24581. -/
theorem bounds_15_24581 : exactInterval 15 24581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24581 : oddCount 24581 15 = 7 ∧ acceleratedOrbit 15 24581 = 1642 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24581) = 3 ^ 7 * m + 1642 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24581.1, data_15_24581.2]

/-- Complete interval computation for depth 15, residue 24582. -/
theorem bounds_15_24582 : exactInterval 15 24582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24582 : oddCount 24582 15 = 7 ∧ acceleratedOrbit 15 24582 = 1642 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24582) = 3 ^ 7 * m + 1642 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24582.1, data_15_24582.2]

/-- Complete interval computation for depth 15, residue 24583. -/
theorem bounds_15_24583 : exactInterval 15 24583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24583 : oddCount 24583 15 = 6 ∧ acceleratedOrbit 15 24583 = 547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24583) = 3 ^ 6 * m + 547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24583.1, data_15_24583.2]

/-- Complete interval computation for depth 15, residue 24584. -/
theorem bounds_15_24584 : exactInterval 15 24584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24584 : oddCount 24584 15 = 6 ∧ acceleratedOrbit 15 24584 = 548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24584) = 3 ^ 6 * m + 548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24584.1, data_15_24584.2]

/-- Complete interval computation for depth 15, residue 24585. -/
theorem bounds_15_24585 : exactInterval 15 24585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24585 : oddCount 24585 15 = 6 ∧ acceleratedOrbit 15 24585 = 547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24585) = 3 ^ 6 * m + 547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24585.1, data_15_24585.2]

/-- Complete interval computation for depth 15, residue 24586. -/
theorem bounds_15_24586 : exactInterval 15 24586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24586 : oddCount 24586 15 = 6 ∧ acceleratedOrbit 15 24586 = 548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24586) = 3 ^ 6 * m + 548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24586.1, data_15_24586.2]

/-- Complete interval computation for depth 15, residue 24587. -/
theorem bounds_15_24587 : exactInterval 15 24587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24587 : oddCount 24587 15 = 7 ∧ acceleratedOrbit 15 24587 = 1642 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24587) = 3 ^ 7 * m + 1642 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24587.1, data_15_24587.2]

/-- Complete interval computation for depth 15, residue 24588. -/
theorem bounds_15_24588 : exactInterval 15 24588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24588 : oddCount 24588 15 = 6 ∧ acceleratedOrbit 15 24588 = 548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24588) = 3 ^ 6 * m + 548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24588.1, data_15_24588.2]

/-- Complete interval computation for depth 15, residue 24589. -/
theorem bounds_15_24589 : exactInterval 15 24589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24589 : oddCount 24589 15 = 6 ∧ acceleratedOrbit 15 24589 = 548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24589) = 3 ^ 6 * m + 548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24589.1, data_15_24589.2]

/-- Complete interval computation for depth 15, residue 24590. -/
theorem bounds_15_24590 : exactInterval 15 24590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24590 : oddCount 24590 15 = 7 ∧ acceleratedOrbit 15 24590 = 1642 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24590) = 3 ^ 7 * m + 1642 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24590.1, data_15_24590.2]

/-- Complete interval computation for depth 15, residue 24591. -/
theorem bounds_15_24591 : exactInterval 15 24591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24591 : oddCount 24591 15 = 7 ∧ acceleratedOrbit 15 24591 = 1642 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24591) = 3 ^ 7 * m + 1642 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24591.1, data_15_24591.2]

/-- Complete interval computation for depth 15, residue 24592. -/
theorem bounds_15_24592 : exactInterval 15 24592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24592 : oddCount 24592 15 = 7 ∧ acceleratedOrbit 15 24592 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24592) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24592.1, data_15_24592.2]

/-- Complete interval computation for depth 15, residue 24593. -/
theorem bounds_15_24593 : exactInterval 15 24593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24593 : oddCount 24593 15 = 6 ∧ acceleratedOrbit 15 24593 = 548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24593) = 3 ^ 6 * m + 548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24593.1, data_15_24593.2]

/-- Complete interval computation for depth 15, residue 24594. -/
theorem bounds_15_24594 : exactInterval 15 24594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24594 : oddCount 24594 15 = 7 ∧ acceleratedOrbit 15 24594 = 1642 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24594) = 3 ^ 7 * m + 1642 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24594.1, data_15_24594.2]

/-- Complete interval computation for depth 15, residue 24595. -/
theorem bounds_15_24595 : exactInterval 15 24595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24595 : oddCount 24595 15 = 7 ∧ acceleratedOrbit 15 24595 = 1642 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24595) = 3 ^ 7 * m + 1642 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24595.1, data_15_24595.2]

/-- Complete interval computation for depth 15, residue 24596. -/
theorem bounds_15_24596 : exactInterval 15 24596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24596 : oddCount 24596 15 = 7 ∧ acceleratedOrbit 15 24596 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24596) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24596.1, data_15_24596.2]

/-- Complete interval computation for depth 15, residue 24597. -/
theorem bounds_15_24597 : exactInterval 15 24597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24597 : oddCount 24597 15 = 7 ∧ acceleratedOrbit 15 24597 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24597) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24597.1, data_15_24597.2]

/-- Complete interval computation for depth 15, residue 24598. -/
theorem bounds_15_24598 : exactInterval 15 24598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24598 : oddCount 24598 15 = 6 ∧ acceleratedOrbit 15 24598 = 548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24598) = 3 ^ 6 * m + 548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24598.1, data_15_24598.2]

/-- Complete interval computation for depth 15, residue 24599. -/
theorem bounds_15_24599 : exactInterval 15 24599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24599 : oddCount 24599 15 = 6 ∧ acceleratedOrbit 15 24599 = 548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24599) = 3 ^ 6 * m + 548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24599.1, data_15_24599.2]

/-- Complete interval computation for depth 15, residue 24600. -/
theorem bounds_15_24600 : exactInterval 15 24600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24600 : oddCount 24600 15 = 7 ∧ acceleratedOrbit 15 24600 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24600) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24600.1, data_15_24600.2]

/-- Complete interval computation for depth 15, residue 24601. -/
theorem bounds_15_24601 : exactInterval 15 24601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24601 : oddCount 24601 15 = 8 ∧ acceleratedOrbit 15 24601 = 4927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24601) = 3 ^ 8 * m + 4927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24601.1, data_15_24601.2]

/-- Complete interval computation for depth 15, residue 24602. -/
theorem bounds_15_24602 : exactInterval 15 24602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24602 : oddCount 24602 15 = 7 ∧ acceleratedOrbit 15 24602 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24602) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24602.1, data_15_24602.2]

/-- Complete interval computation for depth 15, residue 24603. -/
theorem bounds_15_24603 : exactInterval 15 24603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24603 : oddCount 24603 15 = 11 ∧ acceleratedOrbit 15 24603 = 133015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24603) = 3 ^ 11 * m + 133015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24603.1, data_15_24603.2]

/-- Complete interval computation for depth 15, residue 24604. -/
theorem bounds_15_24604 : exactInterval 15 24604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24604 : oddCount 24604 15 = 6 ∧ acceleratedOrbit 15 24604 = 548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24604) = 3 ^ 6 * m + 548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24604.1, data_15_24604.2]

/-- Complete interval computation for depth 15, residue 24605. -/
theorem bounds_15_24605 : exactInterval 15 24605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24605 : oddCount 24605 15 = 6 ∧ acceleratedOrbit 15 24605 = 548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24605) = 3 ^ 6 * m + 548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24605.1, data_15_24605.2]

/-- Complete interval computation for depth 15, residue 24606. -/
theorem bounds_15_24606 : exactInterval 15 24606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24606 : oddCount 24606 15 = 6 ∧ acceleratedOrbit 15 24606 = 548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24606) = 3 ^ 6 * m + 548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24606.1, data_15_24606.2]

/-- Complete interval computation for depth 15, residue 24607. -/
theorem bounds_15_24607 : exactInterval 15 24607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24607 : oddCount 24607 15 = 10 ∧ acceleratedOrbit 15 24607 = 44345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24607) = 3 ^ 10 * m + 44345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24607.1, data_15_24607.2]

end Collatz.Research.PassageAtlas.Batch0751
