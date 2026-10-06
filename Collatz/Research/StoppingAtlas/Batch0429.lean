import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0429

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3502. -/
theorem bounds_12_3502 : exactInterval 12 3502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3502 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3502) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3502 : oddCount 3502 12 = 5 ∧ acceleratedOrbit 12 3502 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3502 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3502) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3502.1, data_12_3502.2]

/-- Complete interval computation for depth 12, residue 3503. -/
theorem bounds_12_3503 : exactInterval 12 3503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3503 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3503) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3503 : oddCount 3503 12 = 8 ∧ acceleratedOrbit 12 3503 = 5615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3503 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3503) = 3 ^ 8 * m + 5615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3503.1, data_12_3503.2]

/-- Complete interval computation for depth 12, residue 3504. -/
theorem bounds_12_3504 : exactInterval 12 3504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3504 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3504) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3504 : oddCount 3504 12 = 5 ∧ acceleratedOrbit 12 3504 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3504 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3504) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3504.1, data_12_3504.2]

/-- Complete interval computation for depth 12, residue 3505. -/
theorem bounds_12_3505 : exactInterval 12 3505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3505 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3505) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3505 : oddCount 3505 12 = 5 ∧ acceleratedOrbit 12 3505 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3505 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3505) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3505.1, data_12_3505.2]

/-- Complete interval computation for depth 12, residue 3506. -/
theorem bounds_12_3506 : exactInterval 12 3506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3506 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3506) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3506 : oddCount 3506 12 = 5 ∧ acceleratedOrbit 12 3506 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3506 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3506) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3506.1, data_12_3506.2]

/-- Complete interval computation for depth 12, residue 3507. -/
theorem bounds_12_3507 : exactInterval 12 3507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3507 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3507) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3507 : oddCount 3507 12 = 5 ∧ acceleratedOrbit 12 3507 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3507 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3507) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3507.1, data_12_3507.2]

/-- Complete interval computation for depth 12, residue 3508. -/
theorem bounds_12_3508 : exactInterval 12 3508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3508 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3508) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3508 : oddCount 3508 12 = 5 ∧ acceleratedOrbit 12 3508 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3508 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3508) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3508.1, data_12_3508.2]

/-- Complete interval computation for depth 12, residue 3509. -/
theorem bounds_12_3509 : exactInterval 12 3509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3509 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3509) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3509 : oddCount 3509 12 = 5 ∧ acceleratedOrbit 12 3509 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3509 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3509) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3509.1, data_12_3509.2]

/-- Complete interval computation for depth 12, residue 3510. -/
theorem bounds_12_3510 : exactInterval 12 3510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3510 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3510) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3510 : oddCount 3510 12 = 7 ∧ acceleratedOrbit 12 3510 = 1876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3510 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3510) = 3 ^ 7 * m + 1876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3510.1, data_12_3510.2]

/-- Complete interval computation for depth 12, residue 3511. -/
theorem bounds_12_3511 : exactInterval 12 3511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3511 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3511) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3511 : oddCount 3511 12 = 7 ∧ acceleratedOrbit 12 3511 = 1876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3511 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3511) = 3 ^ 7 * m + 1876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3511.1, data_12_3511.2]

/-- Complete interval computation for depth 12, residue 3512. -/
theorem bounds_12_3512 : exactInterval 12 3512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3512 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3512) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3512 : oddCount 3512 12 = 5 ∧ acceleratedOrbit 12 3512 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3512 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3512) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3512.1, data_12_3512.2]

/-- Complete interval computation for depth 12, residue 3513. -/
theorem bounds_12_3513 : exactInterval 12 3513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3513 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3513) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3513 : oddCount 3513 12 = 5 ∧ acceleratedOrbit 12 3513 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3513 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3513) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3513.1, data_12_3513.2]

/-- Complete interval computation for depth 12, residue 3514. -/
theorem bounds_12_3514 : exactInterval 12 3514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3514 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3514) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3514 : oddCount 3514 12 = 5 ∧ acceleratedOrbit 12 3514 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3514 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3514) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3514.1, data_12_3514.2]

/-- Complete interval computation for depth 12, residue 3515. -/
theorem bounds_12_3515 : exactInterval 12 3515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3515 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3515) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3515 : oddCount 3515 12 = 6 ∧ acceleratedOrbit 12 3515 = 626 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3515 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3515) = 3 ^ 6 * m + 626 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3515.1, data_12_3515.2]

/-- Complete interval computation for depth 12, residue 3516. -/
theorem bounds_12_3516 : exactInterval 12 3516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3516 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3516) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3516 : oddCount 3516 12 = 7 ∧ acceleratedOrbit 12 3516 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3516 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3516) = 3 ^ 7 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3516.1, data_12_3516.2]

end Collatz.Research.StoppingAtlas.Batch0429
