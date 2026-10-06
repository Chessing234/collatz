import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0631

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2508. -/
theorem bounds_13_2508 : exactInterval 13 2508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2508 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2508) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2508 : oddCount 2508 13 = 7 ∧ acceleratedOrbit 13 2508 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2508 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2508) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2508.1, data_13_2508.2]

/-- Complete interval computation for depth 13, residue 2509. -/
theorem bounds_13_2509 : exactInterval 13 2509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2509 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2509) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2509 : oddCount 2509 13 = 7 ∧ acceleratedOrbit 13 2509 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2509 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2509) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2509.1, data_13_2509.2]

/-- Complete interval computation for depth 13, residue 2510. -/
theorem bounds_13_2510 : exactInterval 13 2510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2510 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2510) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2510 : oddCount 2510 13 = 9 ∧ acceleratedOrbit 13 2510 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2510 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2510) = 3 ^ 9 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2510.1, data_13_2510.2]

/-- Complete interval computation for depth 13, residue 2511. -/
theorem bounds_13_2511 : exactInterval 13 2511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2511 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2511) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2511 : oddCount 2511 13 = 9 ∧ acceleratedOrbit 13 2511 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2511 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2511) = 3 ^ 9 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2511.1, data_13_2511.2]

/-- Complete interval computation for depth 13, residue 2512. -/
theorem bounds_13_2512 : exactInterval 13 2512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2512 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2512) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2512 : oddCount 2512 13 = 5 ∧ acceleratedOrbit 13 2512 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2512 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2512) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2512.1, data_13_2512.2]

/-- Complete interval computation for depth 13, residue 2513. -/
theorem bounds_13_2513 : exactInterval 13 2513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2513 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2513) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2513 : oddCount 2513 13 = 7 ∧ acceleratedOrbit 13 2513 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2513 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2513) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2513.1, data_13_2513.2]

/-- Complete interval computation for depth 13, residue 2514. -/
theorem bounds_13_2514 : exactInterval 13 2514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2514 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2514) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2514 : oddCount 2514 13 = 6 ∧ acceleratedOrbit 13 2514 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2514 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2514) = 3 ^ 6 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2514.1, data_13_2514.2]

/-- Complete interval computation for depth 13, residue 2515. -/
theorem bounds_13_2515 : exactInterval 13 2515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2515 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2515) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2515 : oddCount 2515 13 = 6 ∧ acceleratedOrbit 13 2515 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2515 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2515) = 3 ^ 6 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2515.1, data_13_2515.2]

/-- Complete interval computation for depth 13, residue 2516. -/
theorem bounds_13_2516 : exactInterval 13 2516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2516 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2516) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2516 : oddCount 2516 13 = 5 ∧ acceleratedOrbit 13 2516 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2516 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2516) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2516.1, data_13_2516.2]

/-- Complete interval computation for depth 13, residue 2517. -/
theorem bounds_13_2517 : exactInterval 13 2517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2517 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2517) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2517 : oddCount 2517 13 = 5 ∧ acceleratedOrbit 13 2517 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2517 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2517) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2517.1, data_13_2517.2]

/-- Complete interval computation for depth 13, residue 2518. -/
theorem bounds_13_2518 : exactInterval 13 2518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2518 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2518) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2518 : oddCount 2518 13 = 8 ∧ acceleratedOrbit 13 2518 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2518 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2518) = 3 ^ 8 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2518.1, data_13_2518.2]

/-- Complete interval computation for depth 13, residue 2519. -/
theorem bounds_13_2519 : exactInterval 13 2519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2519 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2519) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2519 : oddCount 2519 13 = 8 ∧ acceleratedOrbit 13 2519 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2519 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2519) = 3 ^ 8 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2519.1, data_13_2519.2]

/-- Complete interval computation for depth 13, residue 2520. -/
theorem bounds_13_2520 : exactInterval 13 2520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2520 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2520) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2520 : oddCount 2520 13 = 4 ∧ acceleratedOrbit 13 2520 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2520 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2520) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2520.1, data_13_2520.2]

/-- Complete interval computation for depth 13, residue 2521. -/
theorem bounds_13_2521 : exactInterval 13 2521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2521 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2521) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2521 : oddCount 2521 13 = 4 ∧ acceleratedOrbit 13 2521 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2521 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2521) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2521.1, data_13_2521.2]

/-- Complete interval computation for depth 13, residue 2522. -/
theorem bounds_13_2522 : exactInterval 13 2522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2522 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2522) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2522 : oddCount 2522 13 = 4 ∧ acceleratedOrbit 13 2522 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2522 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2522) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2522.1, data_13_2522.2]

/-- Complete interval computation for depth 13, residue 2523. -/
theorem bounds_13_2523 : exactInterval 13 2523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2523 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2523) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2523 : oddCount 2523 13 = 8 ∧ acceleratedOrbit 13 2523 = 2024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2523 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2523) = 3 ^ 8 * m + 2024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2523.1, data_13_2523.2]

end Collatz.Research.StoppingAtlas.Batch0631
