import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0934

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30572. -/
theorem bounds_15_30572 : exactInterval 15 30572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30572 : oddCount 30572 15 = 7 ∧ acceleratedOrbit 15 30572 = 2042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30572) = 3 ^ 7 * m + 2042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30572.1, data_15_30572.2]

/-- Complete interval computation for depth 15, residue 30573. -/
theorem bounds_15_30573 : exactInterval 15 30573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30573 : oddCount 30573 15 = 7 ∧ acceleratedOrbit 15 30573 = 2042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30573) = 3 ^ 7 * m + 2042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30573.1, data_15_30573.2]

/-- Complete interval computation for depth 15, residue 30574. -/
theorem bounds_15_30574 : exactInterval 15 30574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30574 : oddCount 30574 15 = 7 ∧ acceleratedOrbit 15 30574 = 2042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30574) = 3 ^ 7 * m + 2042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30574.1, data_15_30574.2]

/-- Complete interval computation for depth 15, residue 30575. -/
theorem bounds_15_30575 : exactInterval 15 30575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30575 : oddCount 30575 15 = 10 ∧ acceleratedOrbit 15 30575 = 55100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30575) = 3 ^ 10 * m + 55100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30575.1, data_15_30575.2]

/-- Complete interval computation for depth 15, residue 30576. -/
theorem bounds_15_30576 : exactInterval 15 30576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30576 : oddCount 30576 15 = 5 ∧ acceleratedOrbit 15 30576 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30576) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30576.1, data_15_30576.2]

/-- Complete interval computation for depth 15, residue 30577. -/
theorem bounds_15_30577 : exactInterval 15 30577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30577 : oddCount 30577 15 = 5 ∧ acceleratedOrbit 15 30577 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30577) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30577.1, data_15_30577.2]

/-- Complete interval computation for depth 15, residue 30578. -/
theorem bounds_15_30578 : exactInterval 15 30578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30578 : oddCount 30578 15 = 7 ∧ acceleratedOrbit 15 30578 = 2042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30578) = 3 ^ 7 * m + 2042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30578.1, data_15_30578.2]

/-- Complete interval computation for depth 15, residue 30579. -/
theorem bounds_15_30579 : exactInterval 15 30579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30579 : oddCount 30579 15 = 7 ∧ acceleratedOrbit 15 30579 = 2042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30579) = 3 ^ 7 * m + 2042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30579.1, data_15_30579.2]

/-- Complete interval computation for depth 15, residue 30580. -/
theorem bounds_15_30580 : exactInterval 15 30580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30580 : oddCount 30580 15 = 5 ∧ acceleratedOrbit 15 30580 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30580) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30580.1, data_15_30580.2]

/-- Complete interval computation for depth 15, residue 30581. -/
theorem bounds_15_30581 : exactInterval 15 30581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30581 : oddCount 30581 15 = 5 ∧ acceleratedOrbit 15 30581 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30581) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30581.1, data_15_30581.2]

/-- Complete interval computation for depth 15, residue 30582. -/
theorem bounds_15_30582 : exactInterval 15 30582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30582 : oddCount 30582 15 = 7 ∧ acceleratedOrbit 15 30582 = 2042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30582) = 3 ^ 7 * m + 2042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30582.1, data_15_30582.2]

/-- Complete interval computation for depth 15, residue 30583. -/
theorem bounds_15_30583 : exactInterval 15 30583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30583 : oddCount 30583 15 = 7 ∧ acceleratedOrbit 15 30583 = 2042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30583) = 3 ^ 7 * m + 2042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30583.1, data_15_30583.2]

/-- Complete interval computation for depth 15, residue 30584. -/
theorem bounds_15_30584 : exactInterval 15 30584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30584 : oddCount 30584 15 = 9 ∧ acceleratedOrbit 15 30584 = 18377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30584) = 3 ^ 9 * m + 18377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30584.1, data_15_30584.2]

/-- Complete interval computation for depth 15, residue 30585. -/
theorem bounds_15_30585 : exactInterval 15 30585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30585 : oddCount 30585 15 = 10 ∧ acceleratedOrbit 15 30585 = 55120 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30585) = 3 ^ 10 * m + 55120 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30585.1, data_15_30585.2]

/-- Complete interval computation for depth 15, residue 30586. -/
theorem bounds_15_30586 : exactInterval 15 30586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30586 : oddCount 30586 15 = 9 ∧ acceleratedOrbit 15 30586 = 18377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30586) = 3 ^ 9 * m + 18377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30586.1, data_15_30586.2]

/-- Complete interval computation for depth 15, residue 30587. -/
theorem bounds_15_30587 : exactInterval 15 30587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30587 : oddCount 30587 15 = 10 ∧ acceleratedOrbit 15 30587 = 55124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30587) = 3 ^ 10 * m + 55124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30587.1, data_15_30587.2]

/-- Complete interval computation for depth 15, residue 30588. -/
theorem bounds_15_30588 : exactInterval 15 30588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30588 : oddCount 30588 15 = 9 ∧ acceleratedOrbit 15 30588 = 18377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30588) = 3 ^ 9 * m + 18377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30588.1, data_15_30588.2]

/-- Complete interval computation for depth 15, residue 30589. -/
theorem bounds_15_30589 : exactInterval 15 30589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30589 : oddCount 30589 15 = 9 ∧ acceleratedOrbit 15 30589 = 18377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30589) = 3 ^ 9 * m + 18377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30589.1, data_15_30589.2]

/-- Complete interval computation for depth 15, residue 30590. -/
theorem bounds_15_30590 : exactInterval 15 30590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30590 : oddCount 30590 15 = 9 ∧ acceleratedOrbit 15 30590 = 18376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30590) = 3 ^ 9 * m + 18376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30590.1, data_15_30590.2]

/-- Complete interval computation for depth 15, residue 30591. -/
theorem bounds_15_30591 : exactInterval 15 30591 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30591) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30591 : oddCount 30591 15 = 9 ∧ acceleratedOrbit 15 30591 = 18376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30591) = 3 ^ 9 * m + 18376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30591.1, data_15_30591.2]

/-- Complete interval computation for depth 15, residue 30592. -/
theorem bounds_15_30592 : exactInterval 15 30592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30592 : oddCount 30592 15 = 7 ∧ acceleratedOrbit 15 30592 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30592) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30592.1, data_15_30592.2]

/-- Complete interval computation for depth 15, residue 30593. -/
theorem bounds_15_30593 : exactInterval 15 30593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30593 : oddCount 30593 15 = 9 ∧ acceleratedOrbit 15 30593 = 18380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30593) = 3 ^ 9 * m + 18380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30593.1, data_15_30593.2]

/-- Complete interval computation for depth 15, residue 30594. -/
theorem bounds_15_30594 : exactInterval 15 30594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30594 : oddCount 30594 15 = 9 ∧ acceleratedOrbit 15 30594 = 18386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30594) = 3 ^ 9 * m + 18386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30594.1, data_15_30594.2]

/-- Complete interval computation for depth 15, residue 30595. -/
theorem bounds_15_30595 : exactInterval 15 30595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30595 : oddCount 30595 15 = 9 ∧ acceleratedOrbit 15 30595 = 18386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30595) = 3 ^ 9 * m + 18386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30595.1, data_15_30595.2]

/-- Complete interval computation for depth 15, residue 30596. -/
theorem bounds_15_30596 : exactInterval 15 30596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30596 : oddCount 30596 15 = 9 ∧ acceleratedOrbit 15 30596 = 18386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30596) = 3 ^ 9 * m + 18386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30596.1, data_15_30596.2]

/-- Complete interval computation for depth 15, residue 30597. -/
theorem bounds_15_30597 : exactInterval 15 30597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30597 : oddCount 30597 15 = 9 ∧ acceleratedOrbit 15 30597 = 18386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30597) = 3 ^ 9 * m + 18386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30597.1, data_15_30597.2]

/-- Complete interval computation for depth 15, residue 30598. -/
theorem bounds_15_30598 : exactInterval 15 30598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30598 : oddCount 30598 15 = 9 ∧ acceleratedOrbit 15 30598 = 18386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30598) = 3 ^ 9 * m + 18386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30598.1, data_15_30598.2]

/-- Complete interval computation for depth 15, residue 30599. -/
theorem bounds_15_30599 : exactInterval 15 30599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30599 : oddCount 30599 15 = 9 ∧ acceleratedOrbit 15 30599 = 18386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30599) = 3 ^ 9 * m + 18386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30599.1, data_15_30599.2]

/-- Complete interval computation for depth 15, residue 30600. -/
theorem bounds_15_30600 : exactInterval 15 30600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30600 : oddCount 30600 15 = 4 ∧ acceleratedOrbit 15 30600 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30600) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30600.1, data_15_30600.2]

/-- Complete interval computation for depth 15, residue 30601. -/
theorem bounds_15_30601 : exactInterval 15 30601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30601 : oddCount 30601 15 = 8 ∧ acceleratedOrbit 15 30601 = 6128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30601) = 3 ^ 8 * m + 6128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30601.1, data_15_30601.2]

/-- Complete interval computation for depth 15, residue 30602. -/
theorem bounds_15_30602 : exactInterval 15 30602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30602 : oddCount 30602 15 = 4 ∧ acceleratedOrbit 15 30602 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30602) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30602.1, data_15_30602.2]

/-- Complete interval computation for depth 15, residue 30603. -/
theorem bounds_15_30603 : exactInterval 15 30603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30603 : oddCount 30603 15 = 10 ∧ acceleratedOrbit 15 30603 = 55154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30603) = 3 ^ 10 * m + 55154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30603.1, data_15_30603.2]

/-- Complete interval computation for depth 15, residue 30604. -/
theorem bounds_15_30604 : exactInterval 15 30604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30604 : oddCount 30604 15 = 4 ∧ acceleratedOrbit 15 30604 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30604) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30604.1, data_15_30604.2]

end Collatz.Research.PassageAtlas.Batch0934
