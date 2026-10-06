import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0767

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4597. -/
theorem bounds_13_4597 : exactInterval 13 4597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4597 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4597) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4597 : oddCount 4597 13 = 6 ∧ acceleratedOrbit 13 4597 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4597 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4597) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4597.1, data_13_4597.2]

/-- Complete interval computation for depth 13, residue 4598. -/
theorem bounds_13_4598 : exactInterval 13 4598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4598 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4598) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4598 : oddCount 4598 13 = 9 ∧ acceleratedOrbit 13 4598 = 11056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4598 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4598) = 3 ^ 9 * m + 11056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4598.1, data_13_4598.2]

/-- Complete interval computation for depth 13, residue 4599. -/
theorem bounds_13_4599 : exactInterval 13 4599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4599 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4599) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4599 : oddCount 4599 13 = 9 ∧ acceleratedOrbit 13 4599 = 11056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4599 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4599) = 3 ^ 9 * m + 11056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4599.1, data_13_4599.2]

/-- Complete interval computation for depth 13, residue 4600. -/
theorem bounds_13_4600 : exactInterval 13 4600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4600 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4600) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4600 : oddCount 4600 13 = 6 ∧ acceleratedOrbit 13 4600 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4600 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4600) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4600.1, data_13_4600.2]

/-- Complete interval computation for depth 13, residue 4601. -/
theorem bounds_13_4601 : exactInterval 13 4601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4601 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4601) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4601 : oddCount 4601 13 = 7 ∧ acceleratedOrbit 13 4601 = 1229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4601 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4601) = 3 ^ 7 * m + 1229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4601.1, data_13_4601.2]

/-- Complete interval computation for depth 13, residue 4602. -/
theorem bounds_13_4602 : exactInterval 13 4602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4602 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4602) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4602 : oddCount 4602 13 = 6 ∧ acceleratedOrbit 13 4602 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4602 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4602) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4602.1, data_13_4602.2]

/-- Complete interval computation for depth 13, residue 4603. -/
theorem bounds_13_4603 : exactInterval 13 4603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4603 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4603) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4603 : oddCount 4603 13 = 8 ∧ acceleratedOrbit 13 4603 = 3689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4603 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4603) = 3 ^ 8 * m + 3689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4603.1, data_13_4603.2]

/-- Complete interval computation for depth 13, residue 4604. -/
theorem bounds_13_4604 : exactInterval 13 4604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4604 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4604) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4604 : oddCount 4604 13 = 9 ∧ acceleratedOrbit 13 4604 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4604 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4604) = 3 ^ 9 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4604.1, data_13_4604.2]

/-- Complete interval computation for depth 13, residue 4605. -/
theorem bounds_13_4605 : exactInterval 13 4605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4605 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4605) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4605 : oddCount 4605 13 = 9 ∧ acceleratedOrbit 13 4605 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4605 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4605) = 3 ^ 9 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4605.1, data_13_4605.2]

/-- Complete interval computation for depth 13, residue 4606. -/
theorem bounds_13_4606 : exactInterval 13 4606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4606 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4606) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4606 : oddCount 4606 13 = 9 ∧ acceleratedOrbit 13 4606 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4606 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4606) = 3 ^ 9 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4606.1, data_13_4606.2]

/-- Complete interval computation for depth 13, residue 4607. -/
theorem bounds_13_4607 : exactInterval 13 4607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4607 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4607) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4607 : oddCount 4607 13 = 10 ∧ acceleratedOrbit 13 4607 = 33215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4607 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4607) = 3 ^ 10 * m + 33215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4607.1, data_13_4607.2]

/-- Complete interval computation for depth 13, residue 4608. -/
theorem bounds_13_4608 : exactInterval 13 4608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4608 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4608) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4608 : oddCount 4608 13 = 3 ∧ acceleratedOrbit 13 4608 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4608 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4608) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4608.1, data_13_4608.2]

/-- Complete interval computation for depth 13, residue 4609. -/
theorem bounds_13_4609 : exactInterval 13 4609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4609 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4609) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4609 : oddCount 4609 13 = 7 ∧ acceleratedOrbit 13 4609 = 1232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4609 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4609) = 3 ^ 7 * m + 1232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4609.1, data_13_4609.2]

/-- Complete interval computation for depth 13, residue 4610. -/
theorem bounds_13_4610 : exactInterval 13 4610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4610 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4610) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4610 : oddCount 4610 13 = 5 ∧ acceleratedOrbit 13 4610 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4610 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4610) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4610.1, data_13_4610.2]

/-- Complete interval computation for depth 13, residue 4611. -/
theorem bounds_13_4611 : exactInterval 13 4611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4611 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4611) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4611 : oddCount 4611 13 = 5 ∧ acceleratedOrbit 13 4611 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4611 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4611) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4611.1, data_13_4611.2]

/-- Complete interval computation for depth 13, residue 4612. -/
theorem bounds_13_4612 : exactInterval 13 4612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4612 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4612) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4612 : oddCount 4612 13 = 7 ∧ acceleratedOrbit 13 4612 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4612 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4612) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4612.1, data_13_4612.2]

end Collatz.Research.StoppingAtlas.Batch0767
