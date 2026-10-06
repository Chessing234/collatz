import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0474

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15499. -/
theorem bounds_15_15499 : exactInterval 15 15499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15499 : oddCount 15499 15 = 9 ∧ acceleratedOrbit 15 15499 = 9314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15499) = 3 ^ 9 * m + 9314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15499.1, data_15_15499.2]

/-- Complete interval computation for depth 15, residue 15500. -/
theorem bounds_15_15500 : exactInterval 15 15500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15500 : oddCount 15500 15 = 6 ∧ acceleratedOrbit 15 15500 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15500) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15500.1, data_15_15500.2]

/-- Complete interval computation for depth 15, residue 15501. -/
theorem bounds_15_15501 : exactInterval 15 15501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15501 : oddCount 15501 15 = 6 ∧ acceleratedOrbit 15 15501 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15501) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15501.1, data_15_15501.2]

/-- Complete interval computation for depth 15, residue 15502. -/
theorem bounds_15_15502 : exactInterval 15 15502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15502 : oddCount 15502 15 = 10 ∧ acceleratedOrbit 15 15502 = 27944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15502) = 3 ^ 10 * m + 27944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15502.1, data_15_15502.2]

/-- Complete interval computation for depth 15, residue 15503. -/
theorem bounds_15_15503 : exactInterval 15 15503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15503 : oddCount 15503 15 = 10 ∧ acceleratedOrbit 15 15503 = 27944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15503) = 3 ^ 10 * m + 27944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15503.1, data_15_15503.2]

/-- Complete interval computation for depth 15, residue 15504. -/
theorem bounds_15_15504 : exactInterval 15 15504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15504 : oddCount 15504 15 = 6 ∧ acceleratedOrbit 15 15504 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15504) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15504.1, data_15_15504.2]

/-- Complete interval computation for depth 15, residue 15505. -/
theorem bounds_15_15505 : exactInterval 15 15505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15505 : oddCount 15505 15 = 8 ∧ acceleratedOrbit 15 15505 = 3106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15505) = 3 ^ 8 * m + 3106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15505.1, data_15_15505.2]

/-- Complete interval computation for depth 15, residue 15506. -/
theorem bounds_15_15506 : exactInterval 15 15506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15506 : oddCount 15506 15 = 8 ∧ acceleratedOrbit 15 15506 = 3106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15506) = 3 ^ 8 * m + 3106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15506.1, data_15_15506.2]

/-- Complete interval computation for depth 15, residue 15507. -/
theorem bounds_15_15507 : exactInterval 15 15507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15507 : oddCount 15507 15 = 8 ∧ acceleratedOrbit 15 15507 = 3106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15507) = 3 ^ 8 * m + 3106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15507.1, data_15_15507.2]

/-- Complete interval computation for depth 15, residue 15508. -/
theorem bounds_15_15508 : exactInterval 15 15508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15508 : oddCount 15508 15 = 6 ∧ acceleratedOrbit 15 15508 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15508) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15508.1, data_15_15508.2]

/-- Complete interval computation for depth 15, residue 15509. -/
theorem bounds_15_15509 : exactInterval 15 15509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15509 : oddCount 15509 15 = 6 ∧ acceleratedOrbit 15 15509 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15509) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15509.1, data_15_15509.2]

/-- Complete interval computation for depth 15, residue 15510. -/
theorem bounds_15_15510 : exactInterval 15 15510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15510 : oddCount 15510 15 = 6 ∧ acceleratedOrbit 15 15510 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15510) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15510.1, data_15_15510.2]

/-- Complete interval computation for depth 15, residue 15511. -/
theorem bounds_15_15511 : exactInterval 15 15511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15511 : oddCount 15511 15 = 6 ∧ acceleratedOrbit 15 15511 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15511) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15511.1, data_15_15511.2]

/-- Complete interval computation for depth 15, residue 15512. -/
theorem bounds_15_15512 : exactInterval 15 15512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15512 : oddCount 15512 15 = 6 ∧ acceleratedOrbit 15 15512 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15512) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15512.1, data_15_15512.2]

/-- Complete interval computation for depth 15, residue 15513. -/
theorem bounds_15_15513 : exactInterval 15 15513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15513 : oddCount 15513 15 = 7 ∧ acceleratedOrbit 15 15513 = 1036 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15513) = 3 ^ 7 * m + 1036 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15513.1, data_15_15513.2]

/-- Complete interval computation for depth 15, residue 15514. -/
theorem bounds_15_15514 : exactInterval 15 15514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15514 : oddCount 15514 15 = 6 ∧ acceleratedOrbit 15 15514 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15514) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15514.1, data_15_15514.2]

/-- Complete interval computation for depth 15, residue 15515. -/
theorem bounds_15_15515 : exactInterval 15 15515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15515 : oddCount 15515 15 = 10 ∧ acceleratedOrbit 15 15515 = 27962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15515) = 3 ^ 10 * m + 27962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15515.1, data_15_15515.2]

/-- Complete interval computation for depth 15, residue 15516. -/
theorem bounds_15_15516 : exactInterval 15 15516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15516 : oddCount 15516 15 = 7 ∧ acceleratedOrbit 15 15516 = 1036 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15516) = 3 ^ 7 * m + 1036 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15516.1, data_15_15516.2]

/-- Complete interval computation for depth 15, residue 15517. -/
theorem bounds_15_15517 : exactInterval 15 15517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15517 : oddCount 15517 15 = 7 ∧ acceleratedOrbit 15 15517 = 1036 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15517) = 3 ^ 7 * m + 1036 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15517.1, data_15_15517.2]

/-- Complete interval computation for depth 15, residue 15518. -/
theorem bounds_15_15518 : exactInterval 15 15518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15518 : oddCount 15518 15 = 7 ∧ acceleratedOrbit 15 15518 = 1036 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15518) = 3 ^ 7 * m + 1036 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15518.1, data_15_15518.2]

/-- Complete interval computation for depth 15, residue 15519. -/
theorem bounds_15_15519 : exactInterval 15 15519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15519 : oddCount 15519 15 = 12 ∧ acceleratedOrbit 15 15519 = 251711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15519) = 3 ^ 12 * m + 251711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15519.1, data_15_15519.2]

/-- Complete interval computation for depth 15, residue 15520. -/
theorem bounds_15_15520 : exactInterval 15 15520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15520 : oddCount 15520 15 = 6 ∧ acceleratedOrbit 15 15520 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15520) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15520.1, data_15_15520.2]

/-- Complete interval computation for depth 15, residue 15521. -/
theorem bounds_15_15521 : exactInterval 15 15521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15521 : oddCount 15521 15 = 9 ∧ acceleratedOrbit 15 15521 = 9325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15521) = 3 ^ 9 * m + 9325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15521.1, data_15_15521.2]

/-- Complete interval computation for depth 15, residue 15522. -/
theorem bounds_15_15522 : exactInterval 15 15522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15522 : oddCount 15522 15 = 7 ∧ acceleratedOrbit 15 15522 = 1037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15522) = 3 ^ 7 * m + 1037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15522.1, data_15_15522.2]

/-- Complete interval computation for depth 15, residue 15523. -/
theorem bounds_15_15523 : exactInterval 15 15523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15523 : oddCount 15523 15 = 7 ∧ acceleratedOrbit 15 15523 = 1037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15523) = 3 ^ 7 * m + 1037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15523.1, data_15_15523.2]

/-- Complete interval computation for depth 15, residue 15524. -/
theorem bounds_15_15524 : exactInterval 15 15524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15524 : oddCount 15524 15 = 7 ∧ acceleratedOrbit 15 15524 = 1037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15524) = 3 ^ 7 * m + 1037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15524.1, data_15_15524.2]

/-- Complete interval computation for depth 15, residue 15525. -/
theorem bounds_15_15525 : exactInterval 15 15525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15525 : oddCount 15525 15 = 7 ∧ acceleratedOrbit 15 15525 = 1037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15525) = 3 ^ 7 * m + 1037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15525.1, data_15_15525.2]

/-- Complete interval computation for depth 15, residue 15526. -/
theorem bounds_15_15526 : exactInterval 15 15526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15526 : oddCount 15526 15 = 7 ∧ acceleratedOrbit 15 15526 = 1037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15526) = 3 ^ 7 * m + 1037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15526.1, data_15_15526.2]

/-- Complete interval computation for depth 15, residue 15527. -/
theorem bounds_15_15527 : exactInterval 15 15527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15527 : oddCount 15527 15 = 10 ∧ acceleratedOrbit 15 15527 = 27983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15527) = 3 ^ 10 * m + 27983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15527.1, data_15_15527.2]

/-- Complete interval computation for depth 15, residue 15528. -/
theorem bounds_15_15528 : exactInterval 15 15528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15528 : oddCount 15528 15 = 6 ∧ acceleratedOrbit 15 15528 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15528) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15528.1, data_15_15528.2]

/-- Complete interval computation for depth 15, residue 15529. -/
theorem bounds_15_15529 : exactInterval 15 15529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15529 : oddCount 15529 15 = 9 ∧ acceleratedOrbit 15 15529 = 9329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15529) = 3 ^ 9 * m + 9329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15529.1, data_15_15529.2]

/-- Complete interval computation for depth 15, residue 15530. -/
theorem bounds_15_15530 : exactInterval 15 15530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15530 : oddCount 15530 15 = 6 ∧ acceleratedOrbit 15 15530 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15530) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15530.1, data_15_15530.2]

/-- Complete interval computation for depth 15, residue 15531. -/
theorem bounds_15_15531 : exactInterval 15 15531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15531 : oddCount 15531 15 = 7 ∧ acceleratedOrbit 15 15531 = 1037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15531) = 3 ^ 7 * m + 1037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15531.1, data_15_15531.2]

end Collatz.Research.PassageAtlas.Batch0474
