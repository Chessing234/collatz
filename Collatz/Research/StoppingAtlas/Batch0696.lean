import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0696

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3507. -/
theorem bounds_13_3507 : exactInterval 13 3507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3507 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3507) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3507 : oddCount 3507 13 = 6 ∧ acceleratedOrbit 13 3507 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3507 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3507) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3507.1, data_13_3507.2]

/-- Complete interval computation for depth 13, residue 3508. -/
theorem bounds_13_3508 : exactInterval 13 3508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3508 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3508) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3508 : oddCount 3508 13 = 6 ∧ acceleratedOrbit 13 3508 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3508 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3508) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3508.1, data_13_3508.2]

/-- Complete interval computation for depth 13, residue 3509. -/
theorem bounds_13_3509 : exactInterval 13 3509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3509 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3509) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3509 : oddCount 3509 13 = 6 ∧ acceleratedOrbit 13 3509 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3509 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3509) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3509.1, data_13_3509.2]

/-- Complete interval computation for depth 13, residue 3510. -/
theorem bounds_13_3510 : exactInterval 13 3510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3510 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3510) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3510 : oddCount 3510 13 = 7 ∧ acceleratedOrbit 13 3510 = 938 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3510 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3510) = 3 ^ 7 * m + 938 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3510.1, data_13_3510.2]

/-- Complete interval computation for depth 13, residue 3511. -/
theorem bounds_13_3511 : exactInterval 13 3511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3511 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3511) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3511 : oddCount 3511 13 = 7 ∧ acceleratedOrbit 13 3511 = 938 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3511 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3511) = 3 ^ 7 * m + 938 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3511.1, data_13_3511.2]

/-- Complete interval computation for depth 13, residue 3512. -/
theorem bounds_13_3512 : exactInterval 13 3512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3512 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3512) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3512 : oddCount 3512 13 = 6 ∧ acceleratedOrbit 13 3512 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3512 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3512) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3512.1, data_13_3512.2]

/-- Complete interval computation for depth 13, residue 3513. -/
theorem bounds_13_3513 : exactInterval 13 3513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3513 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3513) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3513 : oddCount 3513 13 = 6 ∧ acceleratedOrbit 13 3513 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3513 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3513) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3513.1, data_13_3513.2]

/-- Complete interval computation for depth 13, residue 3514. -/
theorem bounds_13_3514 : exactInterval 13 3514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3514 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3514) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3514 : oddCount 3514 13 = 6 ∧ acceleratedOrbit 13 3514 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3514 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3514) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3514.1, data_13_3514.2]

/-- Complete interval computation for depth 13, residue 3515. -/
theorem bounds_13_3515 : exactInterval 13 3515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3515 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3515) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3515 : oddCount 3515 13 = 6 ∧ acceleratedOrbit 13 3515 = 313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3515 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3515) = 3 ^ 6 * m + 313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3515.1, data_13_3515.2]

/-- Complete interval computation for depth 13, residue 3516. -/
theorem bounds_13_3516 : exactInterval 13 3516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3516 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3516) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3516 : oddCount 3516 13 = 7 ∧ acceleratedOrbit 13 3516 = 940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3516 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3516) = 3 ^ 7 * m + 940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3516.1, data_13_3516.2]

/-- Complete interval computation for depth 13, residue 3517. -/
theorem bounds_13_3517 : exactInterval 13 3517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3517 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3517) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3517 : oddCount 3517 13 = 7 ∧ acceleratedOrbit 13 3517 = 940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3517 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3517) = 3 ^ 7 * m + 940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3517.1, data_13_3517.2]

/-- Complete interval computation for depth 13, residue 3518. -/
theorem bounds_13_3518 : exactInterval 13 3518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3518 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3518) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3518 : oddCount 3518 13 = 7 ∧ acceleratedOrbit 13 3518 = 940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3518 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3518) = 3 ^ 7 * m + 940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3518.1, data_13_3518.2]

/-- Complete interval computation for depth 13, residue 3519. -/
theorem bounds_13_3519 : exactInterval 13 3519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3519 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3519) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3519 : oddCount 3519 13 = 10 ∧ acceleratedOrbit 13 3519 = 25373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3519 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3519) = 3 ^ 10 * m + 25373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3519.1, data_13_3519.2]

/-- Complete interval computation for depth 13, residue 3520. -/
theorem bounds_13_3520 : exactInterval 13 3520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3520 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3520) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3520 : oddCount 3520 13 = 5 ∧ acceleratedOrbit 13 3520 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3520 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3520) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3520.1, data_13_3520.2]

/-- Complete interval computation for depth 13, residue 3521. -/
theorem bounds_13_3521 : exactInterval 13 3521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3521 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3521) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3521 : oddCount 3521 13 = 8 ∧ acceleratedOrbit 13 3521 = 2825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3521 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3521) = 3 ^ 8 * m + 2825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3521.1, data_13_3521.2]

end Collatz.Research.StoppingAtlas.Batch0696
