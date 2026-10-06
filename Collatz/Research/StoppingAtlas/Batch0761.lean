import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0761

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4505. -/
theorem bounds_13_4505 : exactInterval 13 4505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4505 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4505) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4505 : oddCount 4505 13 = 7 ∧ acceleratedOrbit 13 4505 = 1205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4505 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4505) = 3 ^ 7 * m + 1205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4505.1, data_13_4505.2]

/-- Complete interval computation for depth 13, residue 4506. -/
theorem bounds_13_4506 : exactInterval 13 4506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4506 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4506) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4506 : oddCount 4506 13 = 6 ∧ acceleratedOrbit 13 4506 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4506 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4506) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4506.1, data_13_4506.2]

/-- Complete interval computation for depth 13, residue 4507. -/
theorem bounds_13_4507 : exactInterval 13 4507 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4507 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4507) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4507 : oddCount 4507 13 = 8 ∧ acceleratedOrbit 13 4507 = 3611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4507 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4507) = 3 ^ 8 * m + 3611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4507.1, data_13_4507.2]

/-- Complete interval computation for depth 13, residue 4508. -/
theorem bounds_13_4508 : exactInterval 13 4508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4508 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4508) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4508 : oddCount 4508 13 = 9 ∧ acceleratedOrbit 13 4508 = 10844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4508 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4508) = 3 ^ 9 * m + 10844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4508.1, data_13_4508.2]

/-- Complete interval computation for depth 13, residue 4509. -/
theorem bounds_13_4509 : exactInterval 13 4509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4509 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4509) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4509 : oddCount 4509 13 = 9 ∧ acceleratedOrbit 13 4509 = 10844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4509 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4509) = 3 ^ 9 * m + 10844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4509.1, data_13_4509.2]

/-- Complete interval computation for depth 13, residue 4510. -/
theorem bounds_13_4510 : exactInterval 13 4510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4510 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4510) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4510 : oddCount 4510 13 = 9 ∧ acceleratedOrbit 13 4510 = 10844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4510 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4510) = 3 ^ 9 * m + 10844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4510.1, data_13_4510.2]

/-- Complete interval computation for depth 13, residue 4511. -/
theorem bounds_13_4511 : exactInterval 13 4511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4511 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4511) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4511 : oddCount 4511 13 = 10 ∧ acceleratedOrbit 13 4511 = 32525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4511 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4511) = 3 ^ 10 * m + 32525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4511.1, data_13_4511.2]

/-- Complete interval computation for depth 13, residue 4512. -/
theorem bounds_13_4512 : exactInterval 13 4512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4512 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4512) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4512 : oddCount 4512 13 = 2 ∧ acceleratedOrbit 13 4512 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4512 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4512) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4512.1, data_13_4512.2]

/-- Complete interval computation for depth 13, residue 4513. -/
theorem bounds_13_4513 : exactInterval 13 4513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4513 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4513) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4513 : oddCount 4513 13 = 9 ∧ acceleratedOrbit 13 4513 = 10853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4513 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4513) = 3 ^ 9 * m + 10853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4513.1, data_13_4513.2]

/-- Complete interval computation for depth 13, residue 4514. -/
theorem bounds_13_4514 : exactInterval 13 4514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4514 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4514) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4514 : oddCount 4514 13 = 7 ∧ acceleratedOrbit 13 4514 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4514 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4514) = 3 ^ 7 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4514.1, data_13_4514.2]

/-- Complete interval computation for depth 13, residue 4515. -/
theorem bounds_13_4515 : exactInterval 13 4515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4515 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4515) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4515 : oddCount 4515 13 = 7 ∧ acceleratedOrbit 13 4515 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4515 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4515) = 3 ^ 7 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4515.1, data_13_4515.2]

/-- Complete interval computation for depth 13, residue 4516. -/
theorem bounds_13_4516 : exactInterval 13 4516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4516 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4516) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4516 : oddCount 4516 13 = 7 ∧ acceleratedOrbit 13 4516 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4516 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4516) = 3 ^ 7 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4516.1, data_13_4516.2]

/-- Complete interval computation for depth 13, residue 4517. -/
theorem bounds_13_4517 : exactInterval 13 4517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4517 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4517) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4517 : oddCount 4517 13 = 7 ∧ acceleratedOrbit 13 4517 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4517 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4517) = 3 ^ 7 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4517.1, data_13_4517.2]

/-- Complete interval computation for depth 13, residue 4518. -/
theorem bounds_13_4518 : exactInterval 13 4518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4518 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4518) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4518 : oddCount 4518 13 = 7 ∧ acceleratedOrbit 13 4518 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4518 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4518) = 3 ^ 7 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4518.1, data_13_4518.2]

/-- Complete interval computation for depth 13, residue 4519. -/
theorem bounds_13_4519 : exactInterval 13 4519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4519 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4519) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4519 : oddCount 4519 13 = 7 ∧ acceleratedOrbit 13 4519 = 1207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4519 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4519) = 3 ^ 7 * m + 1207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4519.1, data_13_4519.2]

end Collatz.Research.StoppingAtlas.Batch0761
