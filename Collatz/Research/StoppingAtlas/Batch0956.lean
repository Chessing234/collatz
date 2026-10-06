import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0956

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7500. -/
theorem bounds_13_7500 : exactInterval 13 7500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7500 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7500) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7500 : oddCount 7500 13 = 8 ∧ acceleratedOrbit 13 7500 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7500 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7500) = 3 ^ 8 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7500.1, data_13_7500.2]

/-- Complete interval computation for depth 13, residue 7501. -/
theorem bounds_13_7501 : exactInterval 13 7501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7501 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7501) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7501 : oddCount 7501 13 = 8 ∧ acceleratedOrbit 13 7501 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7501 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7501) = 3 ^ 8 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7501.1, data_13_7501.2]

/-- Complete interval computation for depth 13, residue 7502. -/
theorem bounds_13_7502 : exactInterval 13 7502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7502 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7502) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7502 : oddCount 7502 13 = 8 ∧ acceleratedOrbit 13 7502 = 6011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7502 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7502) = 3 ^ 8 * m + 6011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7502.1, data_13_7502.2]

/-- Complete interval computation for depth 13, residue 7503. -/
theorem bounds_13_7503 : exactInterval 13 7503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7503 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7503) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7503 : oddCount 7503 13 = 8 ∧ acceleratedOrbit 13 7503 = 6011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7503 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7503) = 3 ^ 8 * m + 6011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7503.1, data_13_7503.2]

/-- Complete interval computation for depth 13, residue 7504. -/
theorem bounds_13_7504 : exactInterval 13 7504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7504 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7504) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7504 : oddCount 7504 13 = 3 ∧ acceleratedOrbit 13 7504 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7504 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7504) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7504.1, data_13_7504.2]

/-- Complete interval computation for depth 13, residue 7505. -/
theorem bounds_13_7505 : exactInterval 13 7505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7505 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7505) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7505 : oddCount 7505 13 = 8 ∧ acceleratedOrbit 13 7505 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7505 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7505) = 3 ^ 8 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7505.1, data_13_7505.2]

/-- Complete interval computation for depth 13, residue 7506. -/
theorem bounds_13_7506 : exactInterval 13 7506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7506 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7506) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7506 : oddCount 7506 13 = 10 ∧ acceleratedOrbit 13 7506 = 54128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7506 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7506) = 3 ^ 10 * m + 54128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7506.1, data_13_7506.2]

/-- Complete interval computation for depth 13, residue 7507. -/
theorem bounds_13_7507 : exactInterval 13 7507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7507 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7507) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7507 : oddCount 7507 13 = 10 ∧ acceleratedOrbit 13 7507 = 54128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7507 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7507) = 3 ^ 10 * m + 54128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7507.1, data_13_7507.2]

/-- Complete interval computation for depth 13, residue 7508. -/
theorem bounds_13_7508 : exactInterval 13 7508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7508 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7508) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7508 : oddCount 7508 13 = 3 ∧ acceleratedOrbit 13 7508 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7508 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7508) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7508.1, data_13_7508.2]

/-- Complete interval computation for depth 13, residue 7509. -/
theorem bounds_13_7509 : exactInterval 13 7509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7509 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7509) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7509 : oddCount 7509 13 = 3 ∧ acceleratedOrbit 13 7509 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7509 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7509) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7509.1, data_13_7509.2]

/-- Complete interval computation for depth 13, residue 7510. -/
theorem bounds_13_7510 : exactInterval 13 7510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7510 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7510) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7510 : oddCount 7510 13 = 8 ∧ acceleratedOrbit 13 7510 = 6020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7510 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7510) = 3 ^ 8 * m + 6020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7510.1, data_13_7510.2]

/-- Complete interval computation for depth 13, residue 7511. -/
theorem bounds_13_7511 : exactInterval 13 7511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7511 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7511) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7511 : oddCount 7511 13 = 8 ∧ acceleratedOrbit 13 7511 = 6020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7511 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7511) = 3 ^ 8 * m + 6020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7511.1, data_13_7511.2]

/-- Complete interval computation for depth 13, residue 7512. -/
theorem bounds_13_7512 : exactInterval 13 7512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7512 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7512) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7512 : oddCount 7512 13 = 6 ∧ acceleratedOrbit 13 7512 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7512 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7512) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7512.1, data_13_7512.2]

/-- Complete interval computation for depth 13, residue 7513. -/
theorem bounds_13_7513 : exactInterval 13 7513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7513 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7513) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7513 : oddCount 7513 13 = 5 ∧ acceleratedOrbit 13 7513 = 223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7513 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7513) = 3 ^ 5 * m + 223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7513.1, data_13_7513.2]

/-- Complete interval computation for depth 13, residue 7514. -/
theorem bounds_13_7514 : exactInterval 13 7514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7514 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7514) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7514 : oddCount 7514 13 = 6 ∧ acceleratedOrbit 13 7514 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7514 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7514) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7514.1, data_13_7514.2]

/-- Complete interval computation for depth 13, residue 7515. -/
theorem bounds_13_7515 : exactInterval 13 7515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7515 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7515) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7515 : oddCount 7515 13 = 9 ∧ acceleratedOrbit 13 7515 = 18062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7515 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7515) = 3 ^ 9 * m + 18062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7515.1, data_13_7515.2]

end Collatz.Research.StoppingAtlas.Batch0956
