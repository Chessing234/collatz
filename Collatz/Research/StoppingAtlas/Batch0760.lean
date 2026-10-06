import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0760

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4490. -/
theorem bounds_13_4490 : exactInterval 13 4490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4490 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4490) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4490 : oddCount 4490 13 = 6 ∧ acceleratedOrbit 13 4490 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4490 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4490) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4490.1, data_13_4490.2]

/-- Complete interval computation for depth 13, residue 4491. -/
theorem bounds_13_4491 : exactInterval 13 4491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4491 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4491) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4491 : oddCount 4491 13 = 9 ∧ acceleratedOrbit 13 4491 = 10799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4491 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4491) = 3 ^ 9 * m + 10799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4491.1, data_13_4491.2]

/-- Complete interval computation for depth 13, residue 4492. -/
theorem bounds_13_4492 : exactInterval 13 4492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4492 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4492) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4492 : oddCount 4492 13 = 6 ∧ acceleratedOrbit 13 4492 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4492 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4492) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4492.1, data_13_4492.2]

/-- Complete interval computation for depth 13, residue 4493. -/
theorem bounds_13_4493 : exactInterval 13 4493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4493 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4493) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4493 : oddCount 4493 13 = 6 ∧ acceleratedOrbit 13 4493 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4493 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4493) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4493.1, data_13_4493.2]

/-- Complete interval computation for depth 13, residue 4494. -/
theorem bounds_13_4494 : exactInterval 13 4494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4494 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4494) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4494 : oddCount 4494 13 = 7 ∧ acceleratedOrbit 13 4494 = 1201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4494 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4494) = 3 ^ 7 * m + 1201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4494.1, data_13_4494.2]

/-- Complete interval computation for depth 13, residue 4495. -/
theorem bounds_13_4495 : exactInterval 13 4495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4495 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4495) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4495 : oddCount 4495 13 = 7 ∧ acceleratedOrbit 13 4495 = 1201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4495 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4495) = 3 ^ 7 * m + 1201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4495.1, data_13_4495.2]

/-- Complete interval computation for depth 13, residue 4496. -/
theorem bounds_13_4496 : exactInterval 13 4496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4496 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4496) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4496 : oddCount 4496 13 = 6 ∧ acceleratedOrbit 13 4496 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4496 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4496) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4496.1, data_13_4496.2]

/-- Complete interval computation for depth 13, residue 4497. -/
theorem bounds_13_4497 : exactInterval 13 4497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4497 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4497) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4497 : oddCount 4497 13 = 5 ∧ acceleratedOrbit 13 4497 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4497 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4497) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4497.1, data_13_4497.2]

/-- Complete interval computation for depth 13, residue 4498. -/
theorem bounds_13_4498 : exactInterval 13 4498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4498 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4498) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4498 : oddCount 4498 13 = 5 ∧ acceleratedOrbit 13 4498 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4498 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4498) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4498.1, data_13_4498.2]

/-- Complete interval computation for depth 13, residue 4499. -/
theorem bounds_13_4499 : exactInterval 13 4499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4499 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4499) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4499 : oddCount 4499 13 = 5 ∧ acceleratedOrbit 13 4499 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4499 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4499) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4499.1, data_13_4499.2]

/-- Complete interval computation for depth 13, residue 4500. -/
theorem bounds_13_4500 : exactInterval 13 4500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4500 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4500) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4500 : oddCount 4500 13 = 6 ∧ acceleratedOrbit 13 4500 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4500 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4500) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4500.1, data_13_4500.2]

/-- Complete interval computation for depth 13, residue 4501. -/
theorem bounds_13_4501 : exactInterval 13 4501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4501 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4501) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4501 : oddCount 4501 13 = 6 ∧ acceleratedOrbit 13 4501 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4501 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4501) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4501.1, data_13_4501.2]

/-- Complete interval computation for depth 13, residue 4502. -/
theorem bounds_13_4502 : exactInterval 13 4502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4502 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4502) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4502 : oddCount 4502 13 = 7 ∧ acceleratedOrbit 13 4502 = 1205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4502 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4502) = 3 ^ 7 * m + 1205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4502.1, data_13_4502.2]

/-- Complete interval computation for depth 13, residue 4503. -/
theorem bounds_13_4503 : exactInterval 13 4503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4503 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4503) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4503 : oddCount 4503 13 = 7 ∧ acceleratedOrbit 13 4503 = 1205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4503 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4503) = 3 ^ 7 * m + 1205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4503.1, data_13_4503.2]

/-- Complete interval computation for depth 13, residue 4504. -/
theorem bounds_13_4504 : exactInterval 13 4504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4504 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4504) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4504 : oddCount 4504 13 = 6 ∧ acceleratedOrbit 13 4504 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4504 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4504) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4504.1, data_13_4504.2]

end Collatz.Research.StoppingAtlas.Batch0760
