import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0322

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10518. -/
theorem bounds_15_10518 : exactInterval 15 10518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10518 : oddCount 10518 15 = 8 ∧ acceleratedOrbit 15 10518 = 2108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10518) = 3 ^ 8 * m + 2108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10518.1, data_15_10518.2]

/-- Complete interval computation for depth 15, residue 10519. -/
theorem bounds_15_10519 : exactInterval 15 10519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10519 : oddCount 10519 15 = 8 ∧ acceleratedOrbit 15 10519 = 2108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10519) = 3 ^ 8 * m + 2108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10519.1, data_15_10519.2]

/-- Complete interval computation for depth 15, residue 10520. -/
theorem bounds_15_10520 : exactInterval 15 10520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10520 : oddCount 10520 15 = 6 ∧ acceleratedOrbit 15 10520 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10520) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10520.1, data_15_10520.2]

/-- Complete interval computation for depth 15, residue 10521. -/
theorem bounds_15_10521 : exactInterval 15 10521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10521 : oddCount 10521 15 = 8 ∧ acceleratedOrbit 15 10521 = 2108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10521) = 3 ^ 8 * m + 2108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10521.1, data_15_10521.2]

/-- Complete interval computation for depth 15, residue 10522. -/
theorem bounds_15_10522 : exactInterval 15 10522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10522 : oddCount 10522 15 = 6 ∧ acceleratedOrbit 15 10522 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10522) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10522.1, data_15_10522.2]

/-- Complete interval computation for depth 15, residue 10523. -/
theorem bounds_15_10523 : exactInterval 15 10523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10523 : oddCount 10523 15 = 9 ∧ acceleratedOrbit 15 10523 = 6322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10523) = 3 ^ 9 * m + 6322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10523.1, data_15_10523.2]

/-- Complete interval computation for depth 15, residue 10524. -/
theorem bounds_15_10524 : exactInterval 15 10524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10524 : oddCount 10524 15 = 7 ∧ acceleratedOrbit 15 10524 = 703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10524) = 3 ^ 7 * m + 703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10524.1, data_15_10524.2]

/-- Complete interval computation for depth 15, residue 10525. -/
theorem bounds_15_10525 : exactInterval 15 10525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10525 : oddCount 10525 15 = 7 ∧ acceleratedOrbit 15 10525 = 703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10525) = 3 ^ 7 * m + 703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10525.1, data_15_10525.2]

/-- Complete interval computation for depth 15, residue 10526. -/
theorem bounds_15_10526 : exactInterval 15 10526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10526 : oddCount 10526 15 = 7 ∧ acceleratedOrbit 15 10526 = 703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10526) = 3 ^ 7 * m + 703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10526.1, data_15_10526.2]

/-- Complete interval computation for depth 15, residue 10527. -/
theorem bounds_15_10527 : exactInterval 15 10527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10527 : oddCount 10527 15 = 10 ∧ acceleratedOrbit 15 10527 = 18974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10527) = 3 ^ 10 * m + 18974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10527.1, data_15_10527.2]

/-- Complete interval computation for depth 15, residue 10528. -/
theorem bounds_15_10528 : exactInterval 15 10528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10528 : oddCount 10528 15 = 6 ∧ acceleratedOrbit 15 10528 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10528) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10528.1, data_15_10528.2]

/-- Complete interval computation for depth 15, residue 10529. -/
theorem bounds_15_10529 : exactInterval 15 10529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10529 : oddCount 10529 15 = 7 ∧ acceleratedOrbit 15 10529 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10529) = 3 ^ 7 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10529.1, data_15_10529.2]

/-- Complete interval computation for depth 15, residue 10530. -/
theorem bounds_15_10530 : exactInterval 15 10530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10530 : oddCount 10530 15 = 7 ∧ acceleratedOrbit 15 10530 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10530) = 3 ^ 7 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10530.1, data_15_10530.2]

/-- Complete interval computation for depth 15, residue 10531. -/
theorem bounds_15_10531 : exactInterval 15 10531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10531 : oddCount 10531 15 = 7 ∧ acceleratedOrbit 15 10531 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10531) = 3 ^ 7 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10531.1, data_15_10531.2]

/-- Complete interval computation for depth 15, residue 10532. -/
theorem bounds_15_10532 : exactInterval 15 10532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10532 : oddCount 10532 15 = 7 ∧ acceleratedOrbit 15 10532 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10532) = 3 ^ 7 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10532.1, data_15_10532.2]

/-- Complete interval computation for depth 15, residue 10533. -/
theorem bounds_15_10533 : exactInterval 15 10533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10533 : oddCount 10533 15 = 7 ∧ acceleratedOrbit 15 10533 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10533) = 3 ^ 7 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10533.1, data_15_10533.2]

/-- Complete interval computation for depth 15, residue 10534. -/
theorem bounds_15_10534 : exactInterval 15 10534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10534 : oddCount 10534 15 = 7 ∧ acceleratedOrbit 15 10534 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10534) = 3 ^ 7 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10534.1, data_15_10534.2]

/-- Complete interval computation for depth 15, residue 10535. -/
theorem bounds_15_10535 : exactInterval 15 10535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10535 : oddCount 10535 15 = 8 ∧ acceleratedOrbit 15 10535 = 2110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10535) = 3 ^ 8 * m + 2110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10535.1, data_15_10535.2]

/-- Complete interval computation for depth 15, residue 10536. -/
theorem bounds_15_10536 : exactInterval 15 10536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10536 : oddCount 10536 15 = 6 ∧ acceleratedOrbit 15 10536 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10536) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10536.1, data_15_10536.2]

/-- Complete interval computation for depth 15, residue 10537. -/
theorem bounds_15_10537 : exactInterval 15 10537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10537 : oddCount 10537 15 = 9 ∧ acceleratedOrbit 15 10537 = 6331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10537) = 3 ^ 9 * m + 6331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10537.1, data_15_10537.2]

/-- Complete interval computation for depth 15, residue 10538. -/
theorem bounds_15_10538 : exactInterval 15 10538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10538 : oddCount 10538 15 = 6 ∧ acceleratedOrbit 15 10538 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10538) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10538.1, data_15_10538.2]

/-- Complete interval computation for depth 15, residue 10539. -/
theorem bounds_15_10539 : exactInterval 15 10539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10539 : oddCount 10539 15 = 8 ∧ acceleratedOrbit 15 10539 = 2111 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10539) = 3 ^ 8 * m + 2111 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10539.1, data_15_10539.2]

/-- Complete interval computation for depth 15, residue 10540. -/
theorem bounds_15_10540 : exactInterval 15 10540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10540 : oddCount 10540 15 = 6 ∧ acceleratedOrbit 15 10540 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10540) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10540.1, data_15_10540.2]

/-- Complete interval computation for depth 15, residue 10541. -/
theorem bounds_15_10541 : exactInterval 15 10541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10541 : oddCount 10541 15 = 6 ∧ acceleratedOrbit 15 10541 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10541) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10541.1, data_15_10541.2]

/-- Complete interval computation for depth 15, residue 10542. -/
theorem bounds_15_10542 : exactInterval 15 10542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10542 : oddCount 10542 15 = 6 ∧ acceleratedOrbit 15 10542 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10542) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10542.1, data_15_10542.2]

/-- Complete interval computation for depth 15, residue 10543. -/
theorem bounds_15_10543 : exactInterval 15 10543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10543 : oddCount 10543 15 = 9 ∧ acceleratedOrbit 15 10543 = 6335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10543) = 3 ^ 9 * m + 6335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10543.1, data_15_10543.2]

/-- Complete interval computation for depth 15, residue 10544. -/
theorem bounds_15_10544 : exactInterval 15 10544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10544 : oddCount 10544 15 = 6 ∧ acceleratedOrbit 15 10544 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10544) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10544.1, data_15_10544.2]

/-- Complete interval computation for depth 15, residue 10545. -/
theorem bounds_15_10545 : exactInterval 15 10545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10545 : oddCount 10545 15 = 6 ∧ acceleratedOrbit 15 10545 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10545) = 3 ^ 6 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10545.1, data_15_10545.2]

/-- Complete interval computation for depth 15, residue 10546. -/
theorem bounds_15_10546 : exactInterval 15 10546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10546 : oddCount 10546 15 = 6 ∧ acceleratedOrbit 15 10546 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10546) = 3 ^ 6 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10546.1, data_15_10546.2]

/-- Complete interval computation for depth 15, residue 10547. -/
theorem bounds_15_10547 : exactInterval 15 10547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10547 : oddCount 10547 15 = 6 ∧ acceleratedOrbit 15 10547 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10547) = 3 ^ 6 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10547.1, data_15_10547.2]

/-- Complete interval computation for depth 15, residue 10548. -/
theorem bounds_15_10548 : exactInterval 15 10548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10548 : oddCount 10548 15 = 6 ∧ acceleratedOrbit 15 10548 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10548) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10548.1, data_15_10548.2]

/-- Complete interval computation for depth 15, residue 10549. -/
theorem bounds_15_10549 : exactInterval 15 10549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10549 : oddCount 10549 15 = 6 ∧ acceleratedOrbit 15 10549 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10549) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10549.1, data_15_10549.2]

/-- Complete interval computation for depth 15, residue 10550. -/
theorem bounds_15_10550 : exactInterval 15 10550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10550 : oddCount 10550 15 = 8 ∧ acceleratedOrbit 15 10550 = 2113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10550) = 3 ^ 8 * m + 2113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10550.1, data_15_10550.2]

end Collatz.Research.PassageAtlas.Batch0322
