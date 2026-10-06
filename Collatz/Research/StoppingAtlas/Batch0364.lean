import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0364

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2503. -/
theorem bounds_12_2503 : exactInterval 12 2503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2503 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2503) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2503 : oddCount 2503 12 = 8 ∧ acceleratedOrbit 12 2503 = 4013 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2503 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2503) = 3 ^ 8 * m + 4013 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2503.1, data_12_2503.2]

/-- Complete interval computation for depth 12, residue 2504. -/
theorem bounds_12_2504 : exactInterval 12 2504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2504 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2504) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2504 : oddCount 2504 12 = 6 ∧ acceleratedOrbit 12 2504 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2504 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2504) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2504.1, data_12_2504.2]

/-- Complete interval computation for depth 12, residue 2505. -/
theorem bounds_12_2505 : exactInterval 12 2505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2505 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2505) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2505 : oddCount 2505 12 = 7 ∧ acceleratedOrbit 12 2505 = 1340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2505 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2505) = 3 ^ 7 * m + 1340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2505.1, data_12_2505.2]

/-- Complete interval computation for depth 12, residue 2506. -/
theorem bounds_12_2506 : exactInterval 12 2506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2506 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2506) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2506 : oddCount 2506 12 = 6 ∧ acceleratedOrbit 12 2506 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2506 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2506) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2506.1, data_12_2506.2]

/-- Complete interval computation for depth 12, residue 2507. -/
theorem bounds_12_2507 : exactInterval 12 2507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2507 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2507) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2507 : oddCount 2507 12 = 5 ∧ acceleratedOrbit 12 2507 = 149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2507 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2507) = 3 ^ 5 * m + 149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2507.1, data_12_2507.2]

/-- Complete interval computation for depth 12, residue 2508. -/
theorem bounds_12_2508 : exactInterval 12 2508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2508 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2508) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2508 : oddCount 2508 12 = 6 ∧ acceleratedOrbit 12 2508 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2508 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2508) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2508.1, data_12_2508.2]

/-- Complete interval computation for depth 12, residue 2509. -/
theorem bounds_12_2509 : exactInterval 12 2509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2509 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2509) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2509 : oddCount 2509 12 = 6 ∧ acceleratedOrbit 12 2509 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2509 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2509) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2509.1, data_12_2509.2]

/-- Complete interval computation for depth 12, residue 2510. -/
theorem bounds_12_2510 : exactInterval 12 2510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2510 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2510) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2510 : oddCount 2510 12 = 8 ∧ acceleratedOrbit 12 2510 = 4025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2510 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2510) = 3 ^ 8 * m + 4025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2510.1, data_12_2510.2]

/-- Complete interval computation for depth 12, residue 2511. -/
theorem bounds_12_2511 : exactInterval 12 2511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2511 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2511) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2511 : oddCount 2511 12 = 8 ∧ acceleratedOrbit 12 2511 = 4025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2511 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2511) = 3 ^ 8 * m + 4025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2511.1, data_12_2511.2]

/-- Complete interval computation for depth 12, residue 2512. -/
theorem bounds_12_2512 : exactInterval 12 2512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2512 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2512) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2512 : oddCount 2512 12 = 5 ∧ acceleratedOrbit 12 2512 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2512 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2512) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2512.1, data_12_2512.2]

/-- Complete interval computation for depth 12, residue 2513. -/
theorem bounds_12_2513 : exactInterval 12 2513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2513 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2513) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2513 : oddCount 2513 12 = 6 ∧ acceleratedOrbit 12 2513 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2513 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2513) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2513.1, data_12_2513.2]

/-- Complete interval computation for depth 12, residue 2514. -/
theorem bounds_12_2514 : exactInterval 12 2514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2514 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2514) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2514 : oddCount 2514 12 = 6 ∧ acceleratedOrbit 12 2514 = 448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2514 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2514) = 3 ^ 6 * m + 448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2514.1, data_12_2514.2]

/-- Complete interval computation for depth 12, residue 2515. -/
theorem bounds_12_2515 : exactInterval 12 2515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2515 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2515) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2515 : oddCount 2515 12 = 6 ∧ acceleratedOrbit 12 2515 = 448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2515 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2515) = 3 ^ 6 * m + 448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2515.1, data_12_2515.2]

/-- Complete interval computation for depth 12, residue 2516. -/
theorem bounds_12_2516 : exactInterval 12 2516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2516 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2516) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2516 : oddCount 2516 12 = 5 ∧ acceleratedOrbit 12 2516 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2516 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2516) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2516.1, data_12_2516.2]

/-- Complete interval computation for depth 12, residue 2517. -/
theorem bounds_12_2517 : exactInterval 12 2517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2517 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2517) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2517 : oddCount 2517 12 = 5 ∧ acceleratedOrbit 12 2517 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2517 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2517) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2517.1, data_12_2517.2]

/-- Complete interval computation for depth 12, residue 2518. -/
theorem bounds_12_2518 : exactInterval 12 2518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2518 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2518) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2518 : oddCount 2518 12 = 8 ∧ acceleratedOrbit 12 2518 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2518 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2518) = 3 ^ 8 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2518.1, data_12_2518.2]

end Collatz.Research.StoppingAtlas.Batch0364
