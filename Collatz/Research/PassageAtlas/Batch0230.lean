import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0230

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7503. -/
theorem bounds_15_7503 : exactInterval 15 7503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7503 : oddCount 7503 15 = 10 ∧ acceleratedOrbit 15 7503 = 13526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7503) = 3 ^ 10 * m + 13526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7503.1, data_15_7503.2]

/-- Complete interval computation for depth 15, residue 7504. -/
theorem bounds_15_7504 : exactInterval 15 7504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7504 : oddCount 7504 15 = 4 ∧ acceleratedOrbit 15 7504 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7504) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7504.1, data_15_7504.2]

/-- Complete interval computation for depth 15, residue 7505. -/
theorem bounds_15_7505 : exactInterval 15 7505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7505 : oddCount 7505 15 = 9 ∧ acceleratedOrbit 15 7505 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7505) = 3 ^ 9 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7505.1, data_15_7505.2]

/-- Complete interval computation for depth 15, residue 7506. -/
theorem bounds_15_7506 : exactInterval 15 7506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7506 : oddCount 7506 15 = 10 ∧ acceleratedOrbit 15 7506 = 13532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7506) = 3 ^ 10 * m + 13532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7506.1, data_15_7506.2]

/-- Complete interval computation for depth 15, residue 7507. -/
theorem bounds_15_7507 : exactInterval 15 7507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7507 : oddCount 7507 15 = 10 ∧ acceleratedOrbit 15 7507 = 13532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7507) = 3 ^ 10 * m + 13532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7507.1, data_15_7507.2]

/-- Complete interval computation for depth 15, residue 7508. -/
theorem bounds_15_7508 : exactInterval 15 7508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7508 : oddCount 7508 15 = 4 ∧ acceleratedOrbit 15 7508 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7508) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7508.1, data_15_7508.2]

/-- Complete interval computation for depth 15, residue 7509. -/
theorem bounds_15_7509 : exactInterval 15 7509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7509 : oddCount 7509 15 = 4 ∧ acceleratedOrbit 15 7509 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7509) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7509.1, data_15_7509.2]

/-- Complete interval computation for depth 15, residue 7510. -/
theorem bounds_15_7510 : exactInterval 15 7510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7510 : oddCount 7510 15 = 8 ∧ acceleratedOrbit 15 7510 = 1505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7510) = 3 ^ 8 * m + 1505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7510.1, data_15_7510.2]

/-- Complete interval computation for depth 15, residue 7511. -/
theorem bounds_15_7511 : exactInterval 15 7511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7511 : oddCount 7511 15 = 8 ∧ acceleratedOrbit 15 7511 = 1505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7511) = 3 ^ 8 * m + 1505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7511.1, data_15_7511.2]

/-- Complete interval computation for depth 15, residue 7512. -/
theorem bounds_15_7512 : exactInterval 15 7512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7512 : oddCount 7512 15 = 7 ∧ acceleratedOrbit 15 7512 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7512) = 3 ^ 7 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7512.1, data_15_7512.2]

/-- Complete interval computation for depth 15, residue 7513. -/
theorem bounds_15_7513 : exactInterval 15 7513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7513 : oddCount 7513 15 = 7 ∧ acceleratedOrbit 15 7513 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7513) = 3 ^ 7 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7513.1, data_15_7513.2]

/-- Complete interval computation for depth 15, residue 7514. -/
theorem bounds_15_7514 : exactInterval 15 7514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7514 : oddCount 7514 15 = 7 ∧ acceleratedOrbit 15 7514 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7514) = 3 ^ 7 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7514.1, data_15_7514.2]

/-- Complete interval computation for depth 15, residue 7515. -/
theorem bounds_15_7515 : exactInterval 15 7515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7515 : oddCount 7515 15 = 10 ∧ acceleratedOrbit 15 7515 = 13547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7515) = 3 ^ 10 * m + 13547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7515.1, data_15_7515.2]

/-- Complete interval computation for depth 15, residue 7516. -/
theorem bounds_15_7516 : exactInterval 15 7516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7516 : oddCount 7516 15 = 7 ∧ acceleratedOrbit 15 7516 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7516) = 3 ^ 7 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7516.1, data_15_7516.2]

/-- Complete interval computation for depth 15, residue 7517. -/
theorem bounds_15_7517 : exactInterval 15 7517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7517 : oddCount 7517 15 = 7 ∧ acceleratedOrbit 15 7517 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7517) = 3 ^ 7 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7517.1, data_15_7517.2]

/-- Complete interval computation for depth 15, residue 7518. -/
theorem bounds_15_7518 : exactInterval 15 7518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7518 : oddCount 7518 15 = 7 ∧ acceleratedOrbit 15 7518 = 502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7518) = 3 ^ 7 * m + 502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7518.1, data_15_7518.2]

/-- Complete interval computation for depth 15, residue 7519. -/
theorem bounds_15_7519 : exactInterval 15 7519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7519 : oddCount 7519 15 = 7 ∧ acceleratedOrbit 15 7519 = 502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7519) = 3 ^ 7 * m + 502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7519.1, data_15_7519.2]

/-- Complete interval computation for depth 15, residue 7520. -/
theorem bounds_15_7520 : exactInterval 15 7520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7520 : oddCount 7520 15 = 7 ∧ acceleratedOrbit 15 7520 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7520) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7520.1, data_15_7520.2]

/-- Complete interval computation for depth 15, residue 7521. -/
theorem bounds_15_7521 : exactInterval 15 7521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7521 : oddCount 7521 15 = 8 ∧ acceleratedOrbit 15 7521 = 1507 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7521) = 3 ^ 8 * m + 1507 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7521.1, data_15_7521.2]

/-- Complete interval computation for depth 15, residue 7522. -/
theorem bounds_15_7522 : exactInterval 15 7522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7522 : oddCount 7522 15 = 5 ∧ acceleratedOrbit 15 7522 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7522) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7522.1, data_15_7522.2]

/-- Complete interval computation for depth 15, residue 7523. -/
theorem bounds_15_7523 : exactInterval 15 7523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7523 : oddCount 7523 15 = 5 ∧ acceleratedOrbit 15 7523 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7523) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7523.1, data_15_7523.2]

/-- Complete interval computation for depth 15, residue 7524. -/
theorem bounds_15_7524 : exactInterval 15 7524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7524 : oddCount 7524 15 = 5 ∧ acceleratedOrbit 15 7524 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7524) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7524.1, data_15_7524.2]

/-- Complete interval computation for depth 15, residue 7525. -/
theorem bounds_15_7525 : exactInterval 15 7525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7525 : oddCount 7525 15 = 5 ∧ acceleratedOrbit 15 7525 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7525) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7525.1, data_15_7525.2]

/-- Complete interval computation for depth 15, residue 7526. -/
theorem bounds_15_7526 : exactInterval 15 7526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7526 : oddCount 7526 15 = 5 ∧ acceleratedOrbit 15 7526 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7526) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7526.1, data_15_7526.2]

/-- Complete interval computation for depth 15, residue 7527. -/
theorem bounds_15_7527 : exactInterval 15 7527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7527 : oddCount 7527 15 = 11 ∧ acceleratedOrbit 15 7527 = 40699 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7527) = 3 ^ 11 * m + 40699 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7527.1, data_15_7527.2]

/-- Complete interval computation for depth 15, residue 7528. -/
theorem bounds_15_7528 : exactInterval 15 7528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7528 : oddCount 7528 15 = 7 ∧ acceleratedOrbit 15 7528 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7528) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7528.1, data_15_7528.2]

/-- Complete interval computation for depth 15, residue 7529. -/
theorem bounds_15_7529 : exactInterval 15 7529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7529 : oddCount 7529 15 = 9 ∧ acceleratedOrbit 15 7529 = 4526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7529) = 3 ^ 9 * m + 4526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7529.1, data_15_7529.2]

/-- Complete interval computation for depth 15, residue 7530. -/
theorem bounds_15_7530 : exactInterval 15 7530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7530 : oddCount 7530 15 = 7 ∧ acceleratedOrbit 15 7530 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7530) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7530.1, data_15_7530.2]

/-- Complete interval computation for depth 15, residue 7531. -/
theorem bounds_15_7531 : exactInterval 15 7531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7531 : oddCount 7531 15 = 9 ∧ acceleratedOrbit 15 7531 = 4526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7531) = 3 ^ 9 * m + 4526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7531.1, data_15_7531.2]

/-- Complete interval computation for depth 15, residue 7532. -/
theorem bounds_15_7532 : exactInterval 15 7532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7532 : oddCount 7532 15 = 9 ∧ acceleratedOrbit 15 7532 = 4529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7532) = 3 ^ 9 * m + 4529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7532.1, data_15_7532.2]

/-- Complete interval computation for depth 15, residue 7533. -/
theorem bounds_15_7533 : exactInterval 15 7533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7533 : oddCount 7533 15 = 9 ∧ acceleratedOrbit 15 7533 = 4529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7533) = 3 ^ 9 * m + 4529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7533.1, data_15_7533.2]

/-- Complete interval computation for depth 15, residue 7534. -/
theorem bounds_15_7534 : exactInterval 15 7534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7534 : oddCount 7534 15 = 9 ∧ acceleratedOrbit 15 7534 = 4529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7534) = 3 ^ 9 * m + 4529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7534.1, data_15_7534.2]

/-- Complete interval computation for depth 15, residue 7535. -/
theorem bounds_15_7535 : exactInterval 15 7535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7535 : oddCount 7535 15 = 7 ∧ acceleratedOrbit 15 7535 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7535) = 3 ^ 7 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7535.1, data_15_7535.2]

end Collatz.Research.PassageAtlas.Batch0230
