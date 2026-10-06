import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0955

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7485. -/
theorem bounds_13_7485 : exactInterval 13 7485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7485 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7485) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7485 : oddCount 7485 13 = 7 ∧ acceleratedOrbit 13 7485 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7485 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7485) = 3 ^ 7 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7485.1, data_13_7485.2]

/-- Complete interval computation for depth 13, residue 7486. -/
theorem bounds_13_7486 : exactInterval 13 7486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7486 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7486) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7486 : oddCount 7486 13 = 9 ∧ acceleratedOrbit 13 7486 = 17992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7486 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7486) = 3 ^ 9 * m + 17992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7486.1, data_13_7486.2]

/-- Complete interval computation for depth 13, residue 7487. -/
theorem bounds_13_7487 : exactInterval 13 7487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7487 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7487) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7487 : oddCount 7487 13 = 9 ∧ acceleratedOrbit 13 7487 = 17992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7487 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7487) = 3 ^ 9 * m + 17992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7487.1, data_13_7487.2]

/-- Complete interval computation for depth 13, residue 7488. -/
theorem bounds_13_7488 : exactInterval 13 7488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7488 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7488) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7488 : oddCount 7488 13 = 3 ∧ acceleratedOrbit 13 7488 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7488 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7488) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7488.1, data_13_7488.2]

/-- Complete interval computation for depth 13, residue 7489. -/
theorem bounds_13_7489 : exactInterval 13 7489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7489 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7489) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7489 : oddCount 7489 13 = 6 ∧ acceleratedOrbit 13 7489 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7489 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7489) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7489.1, data_13_7489.2]

/-- Complete interval computation for depth 13, residue 7490. -/
theorem bounds_13_7490 : exactInterval 13 7490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7490 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7490) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7490 : oddCount 7490 13 = 6 ∧ acceleratedOrbit 13 7490 = 667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7490 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7490) = 3 ^ 6 * m + 667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7490.1, data_13_7490.2]

/-- Complete interval computation for depth 13, residue 7491. -/
theorem bounds_13_7491 : exactInterval 13 7491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7491 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7491) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7491 : oddCount 7491 13 = 6 ∧ acceleratedOrbit 13 7491 = 667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7491 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7491) = 3 ^ 6 * m + 667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7491.1, data_13_7491.2]

/-- Complete interval computation for depth 13, residue 7492. -/
theorem bounds_13_7492 : exactInterval 13 7492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7492 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7492) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7492 : oddCount 7492 13 = 6 ∧ acceleratedOrbit 13 7492 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7492 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7492) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7492.1, data_13_7492.2]

/-- Complete interval computation for depth 13, residue 7493. -/
theorem bounds_13_7493 : exactInterval 13 7493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7493 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7493) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7493 : oddCount 7493 13 = 6 ∧ acceleratedOrbit 13 7493 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7493 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7493) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7493.1, data_13_7493.2]

/-- Complete interval computation for depth 13, residue 7494. -/
theorem bounds_13_7494 : exactInterval 13 7494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7494 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7494) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7494 : oddCount 7494 13 = 6 ∧ acceleratedOrbit 13 7494 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7494 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7494) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7494.1, data_13_7494.2]

/-- Complete interval computation for depth 13, residue 7495. -/
theorem bounds_13_7495 : exactInterval 13 7495 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7495 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7495) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7495 : oddCount 7495 13 = 8 ∧ acceleratedOrbit 13 7495 = 6004 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7495 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7495) = 3 ^ 8 * m + 6004 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7495.1, data_13_7495.2]

/-- Complete interval computation for depth 13, residue 7496. -/
theorem bounds_13_7496 : exactInterval 13 7496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7496 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7496) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7496 : oddCount 7496 13 = 8 ∧ acceleratedOrbit 13 7496 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7496 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7496) = 3 ^ 8 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7496.1, data_13_7496.2]

/-- Complete interval computation for depth 13, residue 7497. -/
theorem bounds_13_7497 : exactInterval 13 7497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7497 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7497) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7497 : oddCount 7497 13 = 8 ∧ acceleratedOrbit 13 7497 = 6007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7497 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7497) = 3 ^ 8 * m + 6007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7497.1, data_13_7497.2]

/-- Complete interval computation for depth 13, residue 7498. -/
theorem bounds_13_7498 : exactInterval 13 7498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7498 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7498) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7498 : oddCount 7498 13 = 8 ∧ acceleratedOrbit 13 7498 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7498 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7498) = 3 ^ 8 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7498.1, data_13_7498.2]

/-- Complete interval computation for depth 13, residue 7499. -/
theorem bounds_13_7499 : exactInterval 13 7499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7499 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7499) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7499 : oddCount 7499 13 = 6 ∧ acceleratedOrbit 13 7499 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7499 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7499) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7499.1, data_13_7499.2]

end Collatz.Research.StoppingAtlas.Batch0955
