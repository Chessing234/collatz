import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0505

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16515. -/
theorem bounds_15_16515 : exactInterval 15 16515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16515 : oddCount 16515 15 = 8 ∧ acceleratedOrbit 15 16515 = 3311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16515) = 3 ^ 8 * m + 3311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16515.1, data_15_16515.2]

/-- Complete interval computation for depth 15, residue 16516. -/
theorem bounds_15_16516 : exactInterval 15 16516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16516 : oddCount 16516 15 = 8 ∧ acceleratedOrbit 15 16516 = 3311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16516) = 3 ^ 8 * m + 3311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16516.1, data_15_16516.2]

/-- Complete interval computation for depth 15, residue 16517. -/
theorem bounds_15_16517 : exactInterval 15 16517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16517 : oddCount 16517 15 = 8 ∧ acceleratedOrbit 15 16517 = 3311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16517) = 3 ^ 8 * m + 3311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16517.1, data_15_16517.2]

/-- Complete interval computation for depth 15, residue 16518. -/
theorem bounds_15_16518 : exactInterval 15 16518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16518 : oddCount 16518 15 = 8 ∧ acceleratedOrbit 15 16518 = 3311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16518) = 3 ^ 8 * m + 3311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16518.1, data_15_16518.2]

/-- Complete interval computation for depth 15, residue 16519. -/
theorem bounds_15_16519 : exactInterval 15 16519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16519 : oddCount 16519 15 = 9 ∧ acceleratedOrbit 15 16519 = 9926 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16519) = 3 ^ 9 * m + 9926 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16519.1, data_15_16519.2]

/-- Complete interval computation for depth 15, residue 16520. -/
theorem bounds_15_16520 : exactInterval 15 16520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16520 : oddCount 16520 15 = 4 ∧ acceleratedOrbit 15 16520 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16520) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16520.1, data_15_16520.2]

/-- Complete interval computation for depth 15, residue 16521. -/
theorem bounds_15_16521 : exactInterval 15 16521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16521 : oddCount 16521 15 = 9 ∧ acceleratedOrbit 15 16521 = 9925 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16521) = 3 ^ 9 * m + 9925 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16521.1, data_15_16521.2]

/-- Complete interval computation for depth 15, residue 16522. -/
theorem bounds_15_16522 : exactInterval 15 16522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16522 : oddCount 16522 15 = 4 ∧ acceleratedOrbit 15 16522 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16522) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16522.1, data_15_16522.2]

/-- Complete interval computation for depth 15, residue 16523. -/
theorem bounds_15_16523 : exactInterval 15 16523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16523 : oddCount 16523 15 = 7 ∧ acceleratedOrbit 15 16523 = 1103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16523) = 3 ^ 7 * m + 1103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16523.1, data_15_16523.2]

/-- Complete interval computation for depth 15, residue 16524. -/
theorem bounds_15_16524 : exactInterval 15 16524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16524 : oddCount 16524 15 = 4 ∧ acceleratedOrbit 15 16524 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16524) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16524.1, data_15_16524.2]

/-- Complete interval computation for depth 15, residue 16525. -/
theorem bounds_15_16525 : exactInterval 15 16525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16525 : oddCount 16525 15 = 4 ∧ acceleratedOrbit 15 16525 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16525) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16525.1, data_15_16525.2]

/-- Complete interval computation for depth 15, residue 16526. -/
theorem bounds_15_16526 : exactInterval 15 16526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16526 : oddCount 16526 15 = 9 ∧ acceleratedOrbit 15 16526 = 9929 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16526) = 3 ^ 9 * m + 9929 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16526.1, data_15_16526.2]

/-- Complete interval computation for depth 15, residue 16527. -/
theorem bounds_15_16527 : exactInterval 15 16527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16527 : oddCount 16527 15 = 9 ∧ acceleratedOrbit 15 16527 = 9929 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16527) = 3 ^ 9 * m + 9929 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16527.1, data_15_16527.2]

/-- Complete interval computation for depth 15, residue 16528. -/
theorem bounds_15_16528 : exactInterval 15 16528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16528 : oddCount 16528 15 = 7 ∧ acceleratedOrbit 15 16528 = 1106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16528) = 3 ^ 7 * m + 1106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16528.1, data_15_16528.2]

/-- Complete interval computation for depth 15, residue 16529. -/
theorem bounds_15_16529 : exactInterval 15 16529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16529 : oddCount 16529 15 = 10 ∧ acceleratedOrbit 15 16529 = 29798 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16529) = 3 ^ 10 * m + 29798 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16529.1, data_15_16529.2]

/-- Complete interval computation for depth 15, residue 16530. -/
theorem bounds_15_16530 : exactInterval 15 16530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16530 : oddCount 16530 15 = 10 ∧ acceleratedOrbit 15 16530 = 29798 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16530) = 3 ^ 10 * m + 29798 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16530.1, data_15_16530.2]

/-- Complete interval computation for depth 15, residue 16531. -/
theorem bounds_15_16531 : exactInterval 15 16531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16531 : oddCount 16531 15 = 10 ∧ acceleratedOrbit 15 16531 = 29798 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16531) = 3 ^ 10 * m + 29798 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16531.1, data_15_16531.2]

/-- Complete interval computation for depth 15, residue 16532. -/
theorem bounds_15_16532 : exactInterval 15 16532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16532 : oddCount 16532 15 = 7 ∧ acceleratedOrbit 15 16532 = 1106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16532) = 3 ^ 7 * m + 1106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16532.1, data_15_16532.2]

/-- Complete interval computation for depth 15, residue 16533. -/
theorem bounds_15_16533 : exactInterval 15 16533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16533 : oddCount 16533 15 = 7 ∧ acceleratedOrbit 15 16533 = 1106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16533) = 3 ^ 7 * m + 1106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16533.1, data_15_16533.2]

/-- Complete interval computation for depth 15, residue 16534. -/
theorem bounds_15_16534 : exactInterval 15 16534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16534 : oddCount 16534 15 = 4 ∧ acceleratedOrbit 15 16534 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16534) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16534.1, data_15_16534.2]

/-- Complete interval computation for depth 15, residue 16535. -/
theorem bounds_15_16535 : exactInterval 15 16535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16535 : oddCount 16535 15 = 4 ∧ acceleratedOrbit 15 16535 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16535) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16535.1, data_15_16535.2]

/-- Complete interval computation for depth 15, residue 16536. -/
theorem bounds_15_16536 : exactInterval 15 16536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16536 : oddCount 16536 15 = 7 ∧ acceleratedOrbit 15 16536 = 1106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16536) = 3 ^ 7 * m + 1106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16536.1, data_15_16536.2]

/-- Complete interval computation for depth 15, residue 16537. -/
theorem bounds_15_16537 : exactInterval 15 16537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16537 : oddCount 16537 15 = 6 ∧ acceleratedOrbit 15 16537 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16537) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16537.1, data_15_16537.2]

/-- Complete interval computation for depth 15, residue 16538. -/
theorem bounds_15_16538 : exactInterval 15 16538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16538 : oddCount 16538 15 = 7 ∧ acceleratedOrbit 15 16538 = 1106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16538) = 3 ^ 7 * m + 1106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16538.1, data_15_16538.2]

/-- Complete interval computation for depth 15, residue 16539. -/
theorem bounds_15_16539 : exactInterval 15 16539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16539 : oddCount 16539 15 = 11 ∧ acceleratedOrbit 15 16539 = 89423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16539) = 3 ^ 11 * m + 89423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16539.1, data_15_16539.2]

/-- Complete interval computation for depth 15, residue 16540. -/
theorem bounds_15_16540 : exactInterval 15 16540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16540 : oddCount 16540 15 = 8 ∧ acceleratedOrbit 15 16540 = 3314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16540) = 3 ^ 8 * m + 3314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16540.1, data_15_16540.2]

/-- Complete interval computation for depth 15, residue 16541. -/
theorem bounds_15_16541 : exactInterval 15 16541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16541 : oddCount 16541 15 = 8 ∧ acceleratedOrbit 15 16541 = 3314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16541) = 3 ^ 8 * m + 3314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16541.1, data_15_16541.2]

/-- Complete interval computation for depth 15, residue 16542. -/
theorem bounds_15_16542 : exactInterval 15 16542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16542 : oddCount 16542 15 = 8 ∧ acceleratedOrbit 15 16542 = 3314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16542) = 3 ^ 8 * m + 3314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16542.1, data_15_16542.2]

/-- Complete interval computation for depth 15, residue 16543. -/
theorem bounds_15_16543 : exactInterval 15 16543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16543 : oddCount 16543 15 = 10 ∧ acceleratedOrbit 15 16543 = 29813 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16543) = 3 ^ 10 * m + 29813 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16543.1, data_15_16543.2]

/-- Complete interval computation for depth 15, residue 16544. -/
theorem bounds_15_16544 : exactInterval 15 16544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16544 : oddCount 16544 15 = 5 ∧ acceleratedOrbit 15 16544 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16544) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16544.1, data_15_16544.2]

/-- Complete interval computation for depth 15, residue 16545. -/
theorem bounds_15_16545 : exactInterval 15 16545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16545 : oddCount 16545 15 = 10 ∧ acceleratedOrbit 15 16545 = 29821 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16545) = 3 ^ 10 * m + 29821 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16545.1, data_15_16545.2]

/-- Complete interval computation for depth 15, residue 16546. -/
theorem bounds_15_16546 : exactInterval 15 16546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16546 : oddCount 16546 15 = 7 ∧ acceleratedOrbit 15 16546 = 1106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16546) = 3 ^ 7 * m + 1106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16546.1, data_15_16546.2]

end Collatz.Research.PassageAtlas.Batch0505
