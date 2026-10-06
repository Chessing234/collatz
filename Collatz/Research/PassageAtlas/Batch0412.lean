import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0412

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13467. -/
theorem bounds_15_13467 : exactInterval 15 13467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13467 : oddCount 13467 15 = 10 ∧ acceleratedOrbit 15 13467 = 24272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13467) = 3 ^ 10 * m + 24272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13467.1, data_15_13467.2]

/-- Complete interval computation for depth 15, residue 13468. -/
theorem bounds_15_13468 : exactInterval 15 13468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13468 : oddCount 13468 15 = 8 ∧ acceleratedOrbit 15 13468 = 2699 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13468) = 3 ^ 8 * m + 2699 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13468.1, data_15_13468.2]

/-- Complete interval computation for depth 15, residue 13469. -/
theorem bounds_15_13469 : exactInterval 15 13469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13469 : oddCount 13469 15 = 8 ∧ acceleratedOrbit 15 13469 = 2699 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13469) = 3 ^ 8 * m + 2699 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13469.1, data_15_13469.2]

/-- Complete interval computation for depth 15, residue 13470. -/
theorem bounds_15_13470 : exactInterval 15 13470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13470 : oddCount 13470 15 = 8 ∧ acceleratedOrbit 15 13470 = 2699 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13470) = 3 ^ 8 * m + 2699 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13470.1, data_15_13470.2]

/-- Complete interval computation for depth 15, residue 13471. -/
theorem bounds_15_13471 : exactInterval 15 13471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13471 : oddCount 13471 15 = 11 ∧ acceleratedOrbit 15 13471 = 72832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13471) = 3 ^ 11 * m + 72832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13471.1, data_15_13471.2]

/-- Complete interval computation for depth 15, residue 13472. -/
theorem bounds_15_13472 : exactInterval 15 13472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13472 : oddCount 13472 15 = 5 ∧ acceleratedOrbit 15 13472 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13472) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13472.1, data_15_13472.2]

/-- Complete interval computation for depth 15, residue 13473. -/
theorem bounds_15_13473 : exactInterval 15 13473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13473 : oddCount 13473 15 = 9 ∧ acceleratedOrbit 15 13473 = 8095 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13473) = 3 ^ 9 * m + 8095 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13473.1, data_15_13473.2]

/-- Complete interval computation for depth 15, residue 13474. -/
theorem bounds_15_13474 : exactInterval 15 13474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13474 : oddCount 13474 15 = 10 ∧ acceleratedOrbit 15 13474 = 24299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13474) = 3 ^ 10 * m + 24299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13474.1, data_15_13474.2]

/-- Complete interval computation for depth 15, residue 13475. -/
theorem bounds_15_13475 : exactInterval 15 13475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13475 : oddCount 13475 15 = 10 ∧ acceleratedOrbit 15 13475 = 24299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13475) = 3 ^ 10 * m + 24299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13475.1, data_15_13475.2]

/-- Complete interval computation for depth 15, residue 13476. -/
theorem bounds_15_13476 : exactInterval 15 13476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13476 : oddCount 13476 15 = 10 ∧ acceleratedOrbit 15 13476 = 24299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13476) = 3 ^ 10 * m + 24299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13476.1, data_15_13476.2]

/-- Complete interval computation for depth 15, residue 13477. -/
theorem bounds_15_13477 : exactInterval 15 13477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13477 : oddCount 13477 15 = 10 ∧ acceleratedOrbit 15 13477 = 24299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13477) = 3 ^ 10 * m + 24299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13477.1, data_15_13477.2]

/-- Complete interval computation for depth 15, residue 13478. -/
theorem bounds_15_13478 : exactInterval 15 13478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13478 : oddCount 13478 15 = 10 ∧ acceleratedOrbit 15 13478 = 24299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13478) = 3 ^ 10 * m + 24299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13478.1, data_15_13478.2]

/-- Complete interval computation for depth 15, residue 13479. -/
theorem bounds_15_13479 : exactInterval 15 13479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13479 : oddCount 13479 15 = 10 ∧ acceleratedOrbit 15 13479 = 24293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13479) = 3 ^ 10 * m + 24293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13479.1, data_15_13479.2]

/-- Complete interval computation for depth 15, residue 13480. -/
theorem bounds_15_13480 : exactInterval 15 13480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13480 : oddCount 13480 15 = 5 ∧ acceleratedOrbit 15 13480 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13480) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13480.1, data_15_13480.2]

/-- Complete interval computation for depth 15, residue 13481. -/
theorem bounds_15_13481 : exactInterval 15 13481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13481 : oddCount 13481 15 = 11 ∧ acceleratedOrbit 15 13481 = 72890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13481) = 3 ^ 11 * m + 72890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13481.1, data_15_13481.2]

/-- Complete interval computation for depth 15, residue 13482. -/
theorem bounds_15_13482 : exactInterval 15 13482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13482 : oddCount 13482 15 = 5 ∧ acceleratedOrbit 15 13482 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13482) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13482.1, data_15_13482.2]

/-- Complete interval computation for depth 15, residue 13483. -/
theorem bounds_15_13483 : exactInterval 15 13483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13483 : oddCount 13483 15 = 5 ∧ acceleratedOrbit 15 13483 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13483) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13483.1, data_15_13483.2]

/-- Complete interval computation for depth 15, residue 13484. -/
theorem bounds_15_13484 : exactInterval 15 13484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13484 : oddCount 13484 15 = 7 ∧ acceleratedOrbit 15 13484 = 901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13484) = 3 ^ 7 * m + 901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13484.1, data_15_13484.2]

/-- Complete interval computation for depth 15, residue 13485. -/
theorem bounds_15_13485 : exactInterval 15 13485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13485 : oddCount 13485 15 = 7 ∧ acceleratedOrbit 15 13485 = 901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13485) = 3 ^ 7 * m + 901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13485.1, data_15_13485.2]

/-- Complete interval computation for depth 15, residue 13486. -/
theorem bounds_15_13486 : exactInterval 15 13486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13486 : oddCount 13486 15 = 7 ∧ acceleratedOrbit 15 13486 = 901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13486) = 3 ^ 7 * m + 901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13486.1, data_15_13486.2]

/-- Complete interval computation for depth 15, residue 13487. -/
theorem bounds_15_13487 : exactInterval 15 13487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13487 : oddCount 13487 15 = 8 ∧ acceleratedOrbit 15 13487 = 2701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13487) = 3 ^ 8 * m + 2701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13487.1, data_15_13487.2]

/-- Complete interval computation for depth 15, residue 13488. -/
theorem bounds_15_13488 : exactInterval 15 13488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13488 : oddCount 13488 15 = 5 ∧ acceleratedOrbit 15 13488 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13488) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13488.1, data_15_13488.2]

/-- Complete interval computation for depth 15, residue 13489. -/
theorem bounds_15_13489 : exactInterval 15 13489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13489 : oddCount 13489 15 = 7 ∧ acceleratedOrbit 15 13489 = 901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13489) = 3 ^ 7 * m + 901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13489.1, data_15_13489.2]

/-- Complete interval computation for depth 15, residue 13490. -/
theorem bounds_15_13490 : exactInterval 15 13490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13490 : oddCount 13490 15 = 7 ∧ acceleratedOrbit 15 13490 = 901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13490) = 3 ^ 7 * m + 901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13490.1, data_15_13490.2]

/-- Complete interval computation for depth 15, residue 13491. -/
theorem bounds_15_13491 : exactInterval 15 13491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13491 : oddCount 13491 15 = 7 ∧ acceleratedOrbit 15 13491 = 901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13491) = 3 ^ 7 * m + 901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13491.1, data_15_13491.2]

/-- Complete interval computation for depth 15, residue 13492. -/
theorem bounds_15_13492 : exactInterval 15 13492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13492 : oddCount 13492 15 = 5 ∧ acceleratedOrbit 15 13492 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13492) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13492.1, data_15_13492.2]

/-- Complete interval computation for depth 15, residue 13493. -/
theorem bounds_15_13493 : exactInterval 15 13493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13493 : oddCount 13493 15 = 5 ∧ acceleratedOrbit 15 13493 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13493) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13493.1, data_15_13493.2]

/-- Complete interval computation for depth 15, residue 13494. -/
theorem bounds_15_13494 : exactInterval 15 13494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13494 : oddCount 13494 15 = 9 ∧ acceleratedOrbit 15 13494 = 8108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13494) = 3 ^ 9 * m + 8108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13494.1, data_15_13494.2]

/-- Complete interval computation for depth 15, residue 13495. -/
theorem bounds_15_13495 : exactInterval 15 13495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13495 : oddCount 13495 15 = 9 ∧ acceleratedOrbit 15 13495 = 8108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13495) = 3 ^ 9 * m + 8108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13495.1, data_15_13495.2]

/-- Complete interval computation for depth 15, residue 13496. -/
theorem bounds_15_13496 : exactInterval 15 13496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13496 : oddCount 13496 15 = 5 ∧ acceleratedOrbit 15 13496 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13496) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13496.1, data_15_13496.2]

/-- Complete interval computation for depth 15, residue 13497. -/
theorem bounds_15_13497 : exactInterval 15 13497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13497 : oddCount 13497 15 = 9 ∧ acceleratedOrbit 15 13497 = 8110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13497) = 3 ^ 9 * m + 8110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13497.1, data_15_13497.2]

/-- Complete interval computation for depth 15, residue 13498. -/
theorem bounds_15_13498 : exactInterval 15 13498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13498 : oddCount 13498 15 = 5 ∧ acceleratedOrbit 15 13498 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13498) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13498.1, data_15_13498.2]

/-- Complete interval computation for depth 15, residue 13499. -/
theorem bounds_15_13499 : exactInterval 15 13499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13499 : oddCount 13499 15 = 9 ∧ acceleratedOrbit 15 13499 = 8110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13499) = 3 ^ 9 * m + 8110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13499.1, data_15_13499.2]

end Collatz.Research.PassageAtlas.Batch0412
