import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0568

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18579. -/
theorem bounds_15_18579 : exactInterval 15 18579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18579 : oddCount 18579 15 = 8 ∧ acceleratedOrbit 15 18579 = 3721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18579) = 3 ^ 8 * m + 3721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18579.1, data_15_18579.2]

/-- Complete interval computation for depth 15, residue 18580. -/
theorem bounds_15_18580 : exactInterval 15 18580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18580 : oddCount 18580 15 = 9 ∧ acceleratedOrbit 15 18580 = 11177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18580) = 3 ^ 9 * m + 11177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18580.1, data_15_18580.2]

/-- Complete interval computation for depth 15, residue 18581. -/
theorem bounds_15_18581 : exactInterval 15 18581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18581 : oddCount 18581 15 = 9 ∧ acceleratedOrbit 15 18581 = 11177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18581) = 3 ^ 9 * m + 11177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18581.1, data_15_18581.2]

/-- Complete interval computation for depth 15, residue 18582. -/
theorem bounds_15_18582 : exactInterval 15 18582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18582 : oddCount 18582 15 = 4 ∧ acceleratedOrbit 15 18582 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18582) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18582.1, data_15_18582.2]

/-- Complete interval computation for depth 15, residue 18583. -/
theorem bounds_15_18583 : exactInterval 15 18583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18583 : oddCount 18583 15 = 4 ∧ acceleratedOrbit 15 18583 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18583) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18583.1, data_15_18583.2]

/-- Complete interval computation for depth 15, residue 18584. -/
theorem bounds_15_18584 : exactInterval 15 18584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18584 : oddCount 18584 15 = 9 ∧ acceleratedOrbit 15 18584 = 11177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18584) = 3 ^ 9 * m + 11177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18584.1, data_15_18584.2]

/-- Complete interval computation for depth 15, residue 18585. -/
theorem bounds_15_18585 : exactInterval 15 18585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18585 : oddCount 18585 15 = 9 ∧ acceleratedOrbit 15 18585 = 11168 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18585) = 3 ^ 9 * m + 11168 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18585.1, data_15_18585.2]

/-- Complete interval computation for depth 15, residue 18586. -/
theorem bounds_15_18586 : exactInterval 15 18586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18586 : oddCount 18586 15 = 9 ∧ acceleratedOrbit 15 18586 = 11177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18586) = 3 ^ 9 * m + 11177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18586.1, data_15_18586.2]

/-- Complete interval computation for depth 15, residue 18587. -/
theorem bounds_15_18587 : exactInterval 15 18587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18587 : oddCount 18587 15 = 8 ∧ acceleratedOrbit 15 18587 = 3722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18587) = 3 ^ 8 * m + 3722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18587.1, data_15_18587.2]

/-- Complete interval computation for depth 15, residue 18588. -/
theorem bounds_15_18588 : exactInterval 15 18588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18588 : oddCount 18588 15 = 8 ∧ acceleratedOrbit 15 18588 = 3725 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18588) = 3 ^ 8 * m + 3725 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18588.1, data_15_18588.2]

/-- Complete interval computation for depth 15, residue 18589. -/
theorem bounds_15_18589 : exactInterval 15 18589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18589 : oddCount 18589 15 = 8 ∧ acceleratedOrbit 15 18589 = 3725 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18589) = 3 ^ 8 * m + 3725 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18589.1, data_15_18589.2]

/-- Complete interval computation for depth 15, residue 18590. -/
theorem bounds_15_18590 : exactInterval 15 18590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18590 : oddCount 18590 15 = 8 ∧ acceleratedOrbit 15 18590 = 3725 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18590) = 3 ^ 8 * m + 3725 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18590.1, data_15_18590.2]

/-- Complete interval computation for depth 15, residue 18591. -/
theorem bounds_15_18591 : exactInterval 15 18591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18591 : oddCount 18591 15 = 13 ∧ acceleratedOrbit 15 18591 = 904598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18591) = 3 ^ 13 * m + 904598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18591.1, data_15_18591.2]

/-- Complete interval computation for depth 15, residue 18592. -/
theorem bounds_15_18592 : exactInterval 15 18592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18592 : oddCount 18592 15 = 4 ∧ acceleratedOrbit 15 18592 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18592) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18592.1, data_15_18592.2]

/-- Complete interval computation for depth 15, residue 18593. -/
theorem bounds_15_18593 : exactInterval 15 18593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18593 : oddCount 18593 15 = 9 ∧ acceleratedOrbit 15 18593 = 11171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18593) = 3 ^ 9 * m + 11171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18593.1, data_15_18593.2]

/-- Complete interval computation for depth 15, residue 18594. -/
theorem bounds_15_18594 : exactInterval 15 18594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18594 : oddCount 18594 15 = 9 ∧ acceleratedOrbit 15 18594 = 11177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18594) = 3 ^ 9 * m + 11177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18594.1, data_15_18594.2]

/-- Complete interval computation for depth 15, residue 18595. -/
theorem bounds_15_18595 : exactInterval 15 18595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18595 : oddCount 18595 15 = 9 ∧ acceleratedOrbit 15 18595 = 11177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18595) = 3 ^ 9 * m + 11177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18595.1, data_15_18595.2]

/-- Complete interval computation for depth 15, residue 18596. -/
theorem bounds_15_18596 : exactInterval 15 18596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18596 : oddCount 18596 15 = 10 ∧ acceleratedOrbit 15 18596 = 33524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18596) = 3 ^ 10 * m + 33524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18596.1, data_15_18596.2]

/-- Complete interval computation for depth 15, residue 18597. -/
theorem bounds_15_18597 : exactInterval 15 18597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18597 : oddCount 18597 15 = 10 ∧ acceleratedOrbit 15 18597 = 33524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18597) = 3 ^ 10 * m + 33524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18597.1, data_15_18597.2]

/-- Complete interval computation for depth 15, residue 18598. -/
theorem bounds_15_18598 : exactInterval 15 18598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18598 : oddCount 18598 15 = 10 ∧ acceleratedOrbit 15 18598 = 33524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18598) = 3 ^ 10 * m + 33524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18598.1, data_15_18598.2]

/-- Complete interval computation for depth 15, residue 18599. -/
theorem bounds_15_18599 : exactInterval 15 18599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18599 : oddCount 18599 15 = 12 ∧ acceleratedOrbit 15 18599 = 301670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18599) = 3 ^ 12 * m + 301670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18599.1, data_15_18599.2]

/-- Complete interval computation for depth 15, residue 18600. -/
theorem bounds_15_18600 : exactInterval 15 18600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18600 : oddCount 18600 15 = 4 ∧ acceleratedOrbit 15 18600 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18600) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18600.1, data_15_18600.2]

/-- Complete interval computation for depth 15, residue 18601. -/
theorem bounds_15_18601 : exactInterval 15 18601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18601 : oddCount 18601 15 = 11 ∧ acceleratedOrbit 15 18601 = 100568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18601) = 3 ^ 11 * m + 100568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18601.1, data_15_18601.2]

/-- Complete interval computation for depth 15, residue 18602. -/
theorem bounds_15_18602 : exactInterval 15 18602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18602 : oddCount 18602 15 = 4 ∧ acceleratedOrbit 15 18602 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18602) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18602.1, data_15_18602.2]

/-- Complete interval computation for depth 15, residue 18603. -/
theorem bounds_15_18603 : exactInterval 15 18603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18603 : oddCount 18603 15 = 10 ∧ acceleratedOrbit 15 18603 = 33533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18603) = 3 ^ 10 * m + 33533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18603.1, data_15_18603.2]

/-- Complete interval computation for depth 15, residue 18604. -/
theorem bounds_15_18604 : exactInterval 15 18604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18604 : oddCount 18604 15 = 4 ∧ acceleratedOrbit 15 18604 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18604) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18604.1, data_15_18604.2]

/-- Complete interval computation for depth 15, residue 18605. -/
theorem bounds_15_18605 : exactInterval 15 18605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18605 : oddCount 18605 15 = 4 ∧ acceleratedOrbit 15 18605 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18605) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18605.1, data_15_18605.2]

/-- Complete interval computation for depth 15, residue 18606. -/
theorem bounds_15_18606 : exactInterval 15 18606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18606 : oddCount 18606 15 = 4 ∧ acceleratedOrbit 15 18606 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18606) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18606.1, data_15_18606.2]

/-- Complete interval computation for depth 15, residue 18607. -/
theorem bounds_15_18607 : exactInterval 15 18607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18607 : oddCount 18607 15 = 12 ∧ acceleratedOrbit 15 18607 = 301805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18607) = 3 ^ 12 * m + 301805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18607.1, data_15_18607.2]

/-- Complete interval computation for depth 15, residue 18608. -/
theorem bounds_15_18608 : exactInterval 15 18608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18608 : oddCount 18608 15 = 6 ∧ acceleratedOrbit 15 18608 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18608) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18608.1, data_15_18608.2]

/-- Complete interval computation for depth 15, residue 18609. -/
theorem bounds_15_18609 : exactInterval 15 18609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18609 : oddCount 18609 15 = 7 ∧ acceleratedOrbit 15 18609 = 1243 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18609) = 3 ^ 7 * m + 1243 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18609.1, data_15_18609.2]

/-- Complete interval computation for depth 15, residue 18610. -/
theorem bounds_15_18610 : exactInterval 15 18610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18610 : oddCount 18610 15 = 7 ∧ acceleratedOrbit 15 18610 = 1243 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18610) = 3 ^ 7 * m + 1243 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18610.1, data_15_18610.2]

/-- Complete interval computation for depth 15, residue 18611. -/
theorem bounds_15_18611 : exactInterval 15 18611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18611 : oddCount 18611 15 = 7 ∧ acceleratedOrbit 15 18611 = 1243 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18611) = 3 ^ 7 * m + 1243 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18611.1, data_15_18611.2]

end Collatz.Research.PassageAtlas.Batch0568
