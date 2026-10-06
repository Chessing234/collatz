import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0627

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20512. -/
theorem bounds_15_20512 : exactInterval 15 20512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20512 : oddCount 20512 15 = 7 ∧ acceleratedOrbit 15 20512 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20512) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20512.1, data_15_20512.2]

/-- Complete interval computation for depth 15, residue 20513. -/
theorem bounds_15_20513 : exactInterval 15 20513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20513 : oddCount 20513 15 = 9 ∧ acceleratedOrbit 15 20513 = 12325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20513) = 3 ^ 9 * m + 12325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20513.1, data_15_20513.2]

/-- Complete interval computation for depth 15, residue 20514. -/
theorem bounds_15_20514 : exactInterval 15 20514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20514 : oddCount 20514 15 = 6 ∧ acceleratedOrbit 15 20514 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20514) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20514.1, data_15_20514.2]

/-- Complete interval computation for depth 15, residue 20515. -/
theorem bounds_15_20515 : exactInterval 15 20515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20515 : oddCount 20515 15 = 6 ∧ acceleratedOrbit 15 20515 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20515) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20515.1, data_15_20515.2]

/-- Complete interval computation for depth 15, residue 20516. -/
theorem bounds_15_20516 : exactInterval 15 20516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20516 : oddCount 20516 15 = 7 ∧ acceleratedOrbit 15 20516 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20516) = 3 ^ 7 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20516.1, data_15_20516.2]

/-- Complete interval computation for depth 15, residue 20517. -/
theorem bounds_15_20517 : exactInterval 15 20517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20517 : oddCount 20517 15 = 7 ∧ acceleratedOrbit 15 20517 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20517) = 3 ^ 7 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20517.1, data_15_20517.2]

/-- Complete interval computation for depth 15, residue 20518. -/
theorem bounds_15_20518 : exactInterval 15 20518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20518 : oddCount 20518 15 = 7 ∧ acceleratedOrbit 15 20518 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20518) = 3 ^ 7 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20518.1, data_15_20518.2]

/-- Complete interval computation for depth 15, residue 20519. -/
theorem bounds_15_20519 : exactInterval 15 20519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20519 : oddCount 20519 15 = 8 ∧ acceleratedOrbit 15 20519 = 4109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20519) = 3 ^ 8 * m + 4109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20519.1, data_15_20519.2]

/-- Complete interval computation for depth 15, residue 20520. -/
theorem bounds_15_20520 : exactInterval 15 20520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20520 : oddCount 20520 15 = 7 ∧ acceleratedOrbit 15 20520 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20520) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20520.1, data_15_20520.2]

/-- Complete interval computation for depth 15, residue 20521. -/
theorem bounds_15_20521 : exactInterval 15 20521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20521 : oddCount 20521 15 = 10 ∧ acceleratedOrbit 15 20521 = 36983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20521) = 3 ^ 10 * m + 36983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20521.1, data_15_20521.2]

/-- Complete interval computation for depth 15, residue 20522. -/
theorem bounds_15_20522 : exactInterval 15 20522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20522 : oddCount 20522 15 = 7 ∧ acceleratedOrbit 15 20522 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20522) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20522.1, data_15_20522.2]

/-- Complete interval computation for depth 15, residue 20523. -/
theorem bounds_15_20523 : exactInterval 15 20523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20523 : oddCount 20523 15 = 9 ∧ acceleratedOrbit 15 20523 = 12332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20523) = 3 ^ 9 * m + 12332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20523.1, data_15_20523.2]

/-- Complete interval computation for depth 15, residue 20524. -/
theorem bounds_15_20524 : exactInterval 15 20524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20524 : oddCount 20524 15 = 6 ∧ acceleratedOrbit 15 20524 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20524) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20524.1, data_15_20524.2]

/-- Complete interval computation for depth 15, residue 20525. -/
theorem bounds_15_20525 : exactInterval 15 20525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20525 : oddCount 20525 15 = 6 ∧ acceleratedOrbit 15 20525 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20525) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20525.1, data_15_20525.2]

/-- Complete interval computation for depth 15, residue 20526. -/
theorem bounds_15_20526 : exactInterval 15 20526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20526 : oddCount 20526 15 = 6 ∧ acceleratedOrbit 15 20526 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20526) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20526.1, data_15_20526.2]

/-- Complete interval computation for depth 15, residue 20527. -/
theorem bounds_15_20527 : exactInterval 15 20527 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20527) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20527 : oddCount 20527 15 = 9 ∧ acceleratedOrbit 15 20527 = 12331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20527) = 3 ^ 9 * m + 12331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20527.1, data_15_20527.2]

/-- Complete interval computation for depth 15, residue 20528. -/
theorem bounds_15_20528 : exactInterval 15 20528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20528 : oddCount 20528 15 = 7 ∧ acceleratedOrbit 15 20528 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20528) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20528.1, data_15_20528.2]

/-- Complete interval computation for depth 15, residue 20529. -/
theorem bounds_15_20529 : exactInterval 15 20529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20529 : oddCount 20529 15 = 9 ∧ acceleratedOrbit 15 20529 = 12338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20529) = 3 ^ 9 * m + 12338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20529.1, data_15_20529.2]

/-- Complete interval computation for depth 15, residue 20530. -/
theorem bounds_15_20530 : exactInterval 15 20530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20530 : oddCount 20530 15 = 9 ∧ acceleratedOrbit 15 20530 = 12338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20530) = 3 ^ 9 * m + 12338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20530.1, data_15_20530.2]

/-- Complete interval computation for depth 15, residue 20531. -/
theorem bounds_15_20531 : exactInterval 15 20531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20531 : oddCount 20531 15 = 9 ∧ acceleratedOrbit 15 20531 = 12338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20531) = 3 ^ 9 * m + 12338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20531.1, data_15_20531.2]

/-- Complete interval computation for depth 15, residue 20532. -/
theorem bounds_15_20532 : exactInterval 15 20532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20532 : oddCount 20532 15 = 7 ∧ acceleratedOrbit 15 20532 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20532) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20532.1, data_15_20532.2]

/-- Complete interval computation for depth 15, residue 20533. -/
theorem bounds_15_20533 : exactInterval 15 20533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20533 : oddCount 20533 15 = 7 ∧ acceleratedOrbit 15 20533 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20533) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20533.1, data_15_20533.2]

/-- Complete interval computation for depth 15, residue 20534. -/
theorem bounds_15_20534 : exactInterval 15 20534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20534 : oddCount 20534 15 = 8 ∧ acceleratedOrbit 15 20534 = 4112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20534) = 3 ^ 8 * m + 4112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20534.1, data_15_20534.2]

/-- Complete interval computation for depth 15, residue 20535. -/
theorem bounds_15_20535 : exactInterval 15 20535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20535 : oddCount 20535 15 = 8 ∧ acceleratedOrbit 15 20535 = 4112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20535) = 3 ^ 8 * m + 4112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20535.1, data_15_20535.2]

/-- Complete interval computation for depth 15, residue 20536. -/
theorem bounds_15_20536 : exactInterval 15 20536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20536 : oddCount 20536 15 = 7 ∧ acceleratedOrbit 15 20536 = 1372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20536) = 3 ^ 7 * m + 1372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20536.1, data_15_20536.2]

/-- Complete interval computation for depth 15, residue 20537. -/
theorem bounds_15_20537 : exactInterval 15 20537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20537 : oddCount 20537 15 = 6 ∧ acceleratedOrbit 15 20537 = 457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20537) = 3 ^ 6 * m + 457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20537.1, data_15_20537.2]

/-- Complete interval computation for depth 15, residue 20538. -/
theorem bounds_15_20538 : exactInterval 15 20538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20538 : oddCount 20538 15 = 7 ∧ acceleratedOrbit 15 20538 = 1372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20538) = 3 ^ 7 * m + 1372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20538.1, data_15_20538.2]

/-- Complete interval computation for depth 15, residue 20539. -/
theorem bounds_15_20539 : exactInterval 15 20539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20539 : oddCount 20539 15 = 6 ∧ acceleratedOrbit 15 20539 = 457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20539) = 3 ^ 6 * m + 457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20539.1, data_15_20539.2]

/-- Complete interval computation for depth 15, residue 20540. -/
theorem bounds_15_20540 : exactInterval 15 20540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20540 : oddCount 20540 15 = 7 ∧ acceleratedOrbit 15 20540 = 1372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20540) = 3 ^ 7 * m + 1372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20540.1, data_15_20540.2]

/-- Complete interval computation for depth 15, residue 20541. -/
theorem bounds_15_20541 : exactInterval 15 20541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20541 : oddCount 20541 15 = 7 ∧ acceleratedOrbit 15 20541 = 1372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20541) = 3 ^ 7 * m + 1372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20541.1, data_15_20541.2]

/-- Complete interval computation for depth 15, residue 20542. -/
theorem bounds_15_20542 : exactInterval 15 20542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20542 : oddCount 20542 15 = 9 ∧ acceleratedOrbit 15 20542 = 12341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20542) = 3 ^ 9 * m + 12341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20542.1, data_15_20542.2]

/-- Complete interval computation for depth 15, residue 20543. -/
theorem bounds_15_20543 : exactInterval 15 20543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20543 : oddCount 20543 15 = 9 ∧ acceleratedOrbit 15 20543 = 12341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20543) = 3 ^ 9 * m + 12341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20543.1, data_15_20543.2]

/-- Complete interval computation for depth 15, residue 20544. -/
theorem bounds_15_20544 : exactInterval 15 20544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20544 : oddCount 20544 15 = 3 ∧ acceleratedOrbit 15 20544 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20544) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20544.1, data_15_20544.2]

end Collatz.Research.PassageAtlas.Batch0627
