import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0629

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20578. -/
theorem bounds_15_20578 : exactInterval 15 20578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20578 : oddCount 20578 15 = 8 ∧ acceleratedOrbit 15 20578 = 4124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20578) = 3 ^ 8 * m + 4124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20578.1, data_15_20578.2]

/-- Complete interval computation for depth 15, residue 20579. -/
theorem bounds_15_20579 : exactInterval 15 20579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20579 : oddCount 20579 15 = 8 ∧ acceleratedOrbit 15 20579 = 4124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20579) = 3 ^ 8 * m + 4124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20579.1, data_15_20579.2]

/-- Complete interval computation for depth 15, residue 20580. -/
theorem bounds_15_20580 : exactInterval 15 20580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20580 : oddCount 20580 15 = 8 ∧ acceleratedOrbit 15 20580 = 4124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20580) = 3 ^ 8 * m + 4124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20580.1, data_15_20580.2]

/-- Complete interval computation for depth 15, residue 20581. -/
theorem bounds_15_20581 : exactInterval 15 20581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20581 : oddCount 20581 15 = 8 ∧ acceleratedOrbit 15 20581 = 4124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20581) = 3 ^ 8 * m + 4124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20581.1, data_15_20581.2]

/-- Complete interval computation for depth 15, residue 20582. -/
theorem bounds_15_20582 : exactInterval 15 20582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20582 : oddCount 20582 15 = 8 ∧ acceleratedOrbit 15 20582 = 4124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20582) = 3 ^ 8 * m + 4124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20582.1, data_15_20582.2]

/-- Complete interval computation for depth 15, residue 20583. -/
theorem bounds_15_20583 : exactInterval 15 20583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20583 : oddCount 20583 15 = 9 ∧ acceleratedOrbit 15 20583 = 12365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20583) = 3 ^ 9 * m + 12365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20583.1, data_15_20583.2]

/-- Complete interval computation for depth 15, residue 20584. -/
theorem bounds_15_20584 : exactInterval 15 20584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20584 : oddCount 20584 15 = 3 ∧ acceleratedOrbit 15 20584 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20584) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20584.1, data_15_20584.2]

/-- Complete interval computation for depth 15, residue 20585. -/
theorem bounds_15_20585 : exactInterval 15 20585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20585 : oddCount 20585 15 = 6 ∧ acceleratedOrbit 15 20585 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20585) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20585.1, data_15_20585.2]

/-- Complete interval computation for depth 15, residue 20586. -/
theorem bounds_15_20586 : exactInterval 15 20586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20586 : oddCount 20586 15 = 3 ∧ acceleratedOrbit 15 20586 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20586) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20586.1, data_15_20586.2]

/-- Complete interval computation for depth 15, residue 20587. -/
theorem bounds_15_20587 : exactInterval 15 20587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20587 : oddCount 20587 15 = 9 ∧ acceleratedOrbit 15 20587 = 12368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20587) = 3 ^ 9 * m + 12368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20587.1, data_15_20587.2]

/-- Complete interval computation for depth 15, residue 20588. -/
theorem bounds_15_20588 : exactInterval 15 20588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20588 : oddCount 20588 15 = 10 ∧ acceleratedOrbit 15 20588 = 37111 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20588) = 3 ^ 10 * m + 37111 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20588.1, data_15_20588.2]

/-- Complete interval computation for depth 15, residue 20589. -/
theorem bounds_15_20589 : exactInterval 15 20589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20589 : oddCount 20589 15 = 10 ∧ acceleratedOrbit 15 20589 = 37111 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20589) = 3 ^ 10 * m + 37111 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20589.1, data_15_20589.2]

/-- Complete interval computation for depth 15, residue 20590. -/
theorem bounds_15_20590 : exactInterval 15 20590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20590 : oddCount 20590 15 = 10 ∧ acceleratedOrbit 15 20590 = 37111 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20590) = 3 ^ 10 * m + 37111 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20590.1, data_15_20590.2]

/-- Complete interval computation for depth 15, residue 20591. -/
theorem bounds_15_20591 : exactInterval 15 20591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20591 : oddCount 20591 15 = 10 ∧ acceleratedOrbit 15 20591 = 37108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20591) = 3 ^ 10 * m + 37108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20591.1, data_15_20591.2]

/-- Complete interval computation for depth 15, residue 20592. -/
theorem bounds_15_20592 : exactInterval 15 20592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20592 : oddCount 20592 15 = 8 ∧ acceleratedOrbit 15 20592 = 4130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20592) = 3 ^ 8 * m + 4130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20592.1, data_15_20592.2]

/-- Complete interval computation for depth 15, residue 20593. -/
theorem bounds_15_20593 : exactInterval 15 20593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20593 : oddCount 20593 15 = 3 ∧ acceleratedOrbit 15 20593 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20593) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20593.1, data_15_20593.2]

/-- Complete interval computation for depth 15, residue 20594. -/
theorem bounds_15_20594 : exactInterval 15 20594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20594 : oddCount 20594 15 = 7 ∧ acceleratedOrbit 15 20594 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20594) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20594.1, data_15_20594.2]

/-- Complete interval computation for depth 15, residue 20595. -/
theorem bounds_15_20595 : exactInterval 15 20595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20595 : oddCount 20595 15 = 7 ∧ acceleratedOrbit 15 20595 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20595) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20595.1, data_15_20595.2]

/-- Complete interval computation for depth 15, residue 20596. -/
theorem bounds_15_20596 : exactInterval 15 20596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20596 : oddCount 20596 15 = 8 ∧ acceleratedOrbit 15 20596 = 4130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20596) = 3 ^ 8 * m + 4130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20596.1, data_15_20596.2]

/-- Complete interval computation for depth 15, residue 20597. -/
theorem bounds_15_20597 : exactInterval 15 20597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20597 : oddCount 20597 15 = 8 ∧ acceleratedOrbit 15 20597 = 4130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20597) = 3 ^ 8 * m + 4130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20597.1, data_15_20597.2]

/-- Complete interval computation for depth 15, residue 20598. -/
theorem bounds_15_20598 : exactInterval 15 20598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20598 : oddCount 20598 15 = 8 ∧ acceleratedOrbit 15 20598 = 4126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20598) = 3 ^ 8 * m + 4126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20598.1, data_15_20598.2]

/-- Complete interval computation for depth 15, residue 20599. -/
theorem bounds_15_20599 : exactInterval 15 20599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20599 : oddCount 20599 15 = 8 ∧ acceleratedOrbit 15 20599 = 4126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20599) = 3 ^ 8 * m + 4126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20599.1, data_15_20599.2]

/-- Complete interval computation for depth 15, residue 20600. -/
theorem bounds_15_20600 : exactInterval 15 20600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20600 : oddCount 20600 15 = 8 ∧ acceleratedOrbit 15 20600 = 4130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20600) = 3 ^ 8 * m + 4130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20600.1, data_15_20600.2]

/-- Complete interval computation for depth 15, residue 20601. -/
theorem bounds_15_20601 : exactInterval 15 20601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20601 : oddCount 20601 15 = 9 ∧ acceleratedOrbit 15 20601 = 12376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20601) = 3 ^ 9 * m + 12376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20601.1, data_15_20601.2]

/-- Complete interval computation for depth 15, residue 20602. -/
theorem bounds_15_20602 : exactInterval 15 20602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20602 : oddCount 20602 15 = 8 ∧ acceleratedOrbit 15 20602 = 4130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20602) = 3 ^ 8 * m + 4130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20602.1, data_15_20602.2]

/-- Complete interval computation for depth 15, residue 20603. -/
theorem bounds_15_20603 : exactInterval 15 20603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20603 : oddCount 20603 15 = 8 ∧ acceleratedOrbit 15 20603 = 4126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20603) = 3 ^ 8 * m + 4126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20603.1, data_15_20603.2]

/-- Complete interval computation for depth 15, residue 20604. -/
theorem bounds_15_20604 : exactInterval 15 20604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20604 : oddCount 20604 15 = 10 ∧ acceleratedOrbit 15 20604 = 37138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20604) = 3 ^ 10 * m + 37138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20604.1, data_15_20604.2]

/-- Complete interval computation for depth 15, residue 20605. -/
theorem bounds_15_20605 : exactInterval 15 20605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20605 : oddCount 20605 15 = 10 ∧ acceleratedOrbit 15 20605 = 37138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20605) = 3 ^ 10 * m + 37138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20605.1, data_15_20605.2]

/-- Complete interval computation for depth 15, residue 20606. -/
theorem bounds_15_20606 : exactInterval 15 20606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20606 : oddCount 20606 15 = 10 ∧ acceleratedOrbit 15 20606 = 37138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20606) = 3 ^ 10 * m + 37138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20606.1, data_15_20606.2]

/-- Complete interval computation for depth 15, residue 20607. -/
theorem bounds_15_20607 : exactInterval 15 20607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20607 : oddCount 20607 15 = 9 ∧ acceleratedOrbit 15 20607 = 12379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20607) = 3 ^ 9 * m + 12379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20607.1, data_15_20607.2]

/-- Complete interval computation for depth 15, residue 20608. -/
theorem bounds_15_20608 : exactInterval 15 20608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20608 : oddCount 20608 15 = 5 ∧ acceleratedOrbit 15 20608 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20608) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20608.1, data_15_20608.2]

/-- Complete interval computation for depth 15, residue 20609. -/
theorem bounds_15_20609 : exactInterval 15 20609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20609 : oddCount 20609 15 = 9 ∧ acceleratedOrbit 15 20609 = 12383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20609) = 3 ^ 9 * m + 12383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20609.1, data_15_20609.2]

/-- Complete interval computation for depth 15, residue 20610. -/
theorem bounds_15_20610 : exactInterval 15 20610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20610 : oddCount 20610 15 = 9 ∧ acceleratedOrbit 15 20610 = 12392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20610) = 3 ^ 9 * m + 12392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20610.1, data_15_20610.2]

end Collatz.Research.PassageAtlas.Batch0629
