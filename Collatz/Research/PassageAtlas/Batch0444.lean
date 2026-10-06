import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0444

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14516. -/
theorem bounds_15_14516 : exactInterval 15 14516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14516 : oddCount 14516 15 = 8 ∧ acceleratedOrbit 15 14516 = 2915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14516) = 3 ^ 8 * m + 2915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14516.1, data_15_14516.2]

/-- Complete interval computation for depth 15, residue 14517. -/
theorem bounds_15_14517 : exactInterval 15 14517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14517 : oddCount 14517 15 = 8 ∧ acceleratedOrbit 15 14517 = 2915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14517) = 3 ^ 8 * m + 2915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14517.1, data_15_14517.2]

/-- Complete interval computation for depth 15, residue 14518. -/
theorem bounds_15_14518 : exactInterval 15 14518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14518 : oddCount 14518 15 = 9 ∧ acceleratedOrbit 15 14518 = 8723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14518) = 3 ^ 9 * m + 8723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14518.1, data_15_14518.2]

/-- Complete interval computation for depth 15, residue 14519. -/
theorem bounds_15_14519 : exactInterval 15 14519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14519 : oddCount 14519 15 = 9 ∧ acceleratedOrbit 15 14519 = 8723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14519) = 3 ^ 9 * m + 8723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14519.1, data_15_14519.2]

/-- Complete interval computation for depth 15, residue 14520. -/
theorem bounds_15_14520 : exactInterval 15 14520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14520 : oddCount 14520 15 = 8 ∧ acceleratedOrbit 15 14520 = 2915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14520) = 3 ^ 8 * m + 2915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14520.1, data_15_14520.2]

/-- Complete interval computation for depth 15, residue 14521. -/
theorem bounds_15_14521 : exactInterval 15 14521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14521 : oddCount 14521 15 = 8 ∧ acceleratedOrbit 15 14521 = 2909 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14521) = 3 ^ 8 * m + 2909 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14521.1, data_15_14521.2]

/-- Complete interval computation for depth 15, residue 14522. -/
theorem bounds_15_14522 : exactInterval 15 14522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14522 : oddCount 14522 15 = 8 ∧ acceleratedOrbit 15 14522 = 2915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14522) = 3 ^ 8 * m + 2915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14522.1, data_15_14522.2]

/-- Complete interval computation for depth 15, residue 14523. -/
theorem bounds_15_14523 : exactInterval 15 14523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14523 : oddCount 14523 15 = 10 ∧ acceleratedOrbit 15 14523 = 26176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14523) = 3 ^ 10 * m + 26176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14523.1, data_15_14523.2]

/-- Complete interval computation for depth 15, residue 14524. -/
theorem bounds_15_14524 : exactInterval 15 14524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14524 : oddCount 14524 15 = 10 ∧ acceleratedOrbit 15 14524 = 26183 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14524) = 3 ^ 10 * m + 26183 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14524.1, data_15_14524.2]

/-- Complete interval computation for depth 15, residue 14525. -/
theorem bounds_15_14525 : exactInterval 15 14525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14525 : oddCount 14525 15 = 10 ∧ acceleratedOrbit 15 14525 = 26183 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14525) = 3 ^ 10 * m + 26183 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14525.1, data_15_14525.2]

/-- Complete interval computation for depth 15, residue 14526. -/
theorem bounds_15_14526 : exactInterval 15 14526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14526 : oddCount 14526 15 = 10 ∧ acceleratedOrbit 15 14526 = 26183 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14526) = 3 ^ 10 * m + 26183 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14526.1, data_15_14526.2]

/-- Complete interval computation for depth 15, residue 14527. -/
theorem bounds_15_14527 : exactInterval 15 14527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14527 : oddCount 14527 15 = 8 ∧ acceleratedOrbit 15 14527 = 2909 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14527) = 3 ^ 8 * m + 2909 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14527.1, data_15_14527.2]

/-- Complete interval computation for depth 15, residue 14528. -/
theorem bounds_15_14528 : exactInterval 15 14528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14528 : oddCount 14528 15 = 2 ∧ acceleratedOrbit 15 14528 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14528) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14528.1, data_15_14528.2]

/-- Complete interval computation for depth 15, residue 14529. -/
theorem bounds_15_14529 : exactInterval 15 14529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14529 : oddCount 14529 15 = 8 ∧ acceleratedOrbit 15 14529 = 2911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14529) = 3 ^ 8 * m + 2911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14529.1, data_15_14529.2]

/-- Complete interval computation for depth 15, residue 14530. -/
theorem bounds_15_14530 : exactInterval 15 14530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14530 : oddCount 14530 15 = 8 ∧ acceleratedOrbit 15 14530 = 2911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14530) = 3 ^ 8 * m + 2911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14530.1, data_15_14530.2]

/-- Complete interval computation for depth 15, residue 14531. -/
theorem bounds_15_14531 : exactInterval 15 14531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14531 : oddCount 14531 15 = 8 ∧ acceleratedOrbit 15 14531 = 2911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14531) = 3 ^ 8 * m + 2911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14531.1, data_15_14531.2]

/-- Complete interval computation for depth 15, residue 14532. -/
theorem bounds_15_14532 : exactInterval 15 14532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14532 : oddCount 14532 15 = 9 ∧ acceleratedOrbit 15 14532 = 8747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14532) = 3 ^ 9 * m + 8747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14532.1, data_15_14532.2]

/-- Complete interval computation for depth 15, residue 14533. -/
theorem bounds_15_14533 : exactInterval 15 14533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14533 : oddCount 14533 15 = 9 ∧ acceleratedOrbit 15 14533 = 8747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14533) = 3 ^ 9 * m + 8747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14533.1, data_15_14533.2]

/-- Complete interval computation for depth 15, residue 14534. -/
theorem bounds_15_14534 : exactInterval 15 14534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14534 : oddCount 14534 15 = 9 ∧ acceleratedOrbit 15 14534 = 8747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14534) = 3 ^ 9 * m + 8747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14534.1, data_15_14534.2]

/-- Complete interval computation for depth 15, residue 14535. -/
theorem bounds_15_14535 : exactInterval 15 14535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14535 : oddCount 14535 15 = 8 ∧ acceleratedOrbit 15 14535 = 2911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14535) = 3 ^ 8 * m + 2911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14535.1, data_15_14535.2]

/-- Complete interval computation for depth 15, residue 14536. -/
theorem bounds_15_14536 : exactInterval 15 14536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14536 : oddCount 14536 15 = 9 ∧ acceleratedOrbit 15 14536 = 8747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14536) = 3 ^ 9 * m + 8747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14536.1, data_15_14536.2]

/-- Complete interval computation for depth 15, residue 14537. -/
theorem bounds_15_14537 : exactInterval 15 14537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14537 : oddCount 14537 15 = 8 ∧ acceleratedOrbit 15 14537 = 2915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14537) = 3 ^ 8 * m + 2915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14537.1, data_15_14537.2]

/-- Complete interval computation for depth 15, residue 14538. -/
theorem bounds_15_14538 : exactInterval 15 14538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14538 : oddCount 14538 15 = 9 ∧ acceleratedOrbit 15 14538 = 8747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14538) = 3 ^ 9 * m + 8747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14538.1, data_15_14538.2]

/-- Complete interval computation for depth 15, residue 14539. -/
theorem bounds_15_14539 : exactInterval 15 14539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14539 : oddCount 14539 15 = 9 ∧ acceleratedOrbit 15 14539 = 8738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14539) = 3 ^ 9 * m + 8738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14539.1, data_15_14539.2]

/-- Complete interval computation for depth 15, residue 14540. -/
theorem bounds_15_14540 : exactInterval 15 14540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14540 : oddCount 14540 15 = 9 ∧ acceleratedOrbit 15 14540 = 8747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14540) = 3 ^ 9 * m + 8747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14540.1, data_15_14540.2]

/-- Complete interval computation for depth 15, residue 14541. -/
theorem bounds_15_14541 : exactInterval 15 14541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14541 : oddCount 14541 15 = 9 ∧ acceleratedOrbit 15 14541 = 8747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14541) = 3 ^ 9 * m + 8747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14541.1, data_15_14541.2]

/-- Complete interval computation for depth 15, residue 14542. -/
theorem bounds_15_14542 : exactInterval 15 14542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14542 : oddCount 14542 15 = 10 ∧ acceleratedOrbit 15 14542 = 26210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14542) = 3 ^ 10 * m + 26210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14542.1, data_15_14542.2]

/-- Complete interval computation for depth 15, residue 14543. -/
theorem bounds_15_14543 : exactInterval 15 14543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14543 : oddCount 14543 15 = 10 ∧ acceleratedOrbit 15 14543 = 26210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14543) = 3 ^ 10 * m + 26210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14543.1, data_15_14543.2]

/-- Complete interval computation for depth 15, residue 14544. -/
theorem bounds_15_14544 : exactInterval 15 14544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14544 : oddCount 14544 15 = 2 ∧ acceleratedOrbit 15 14544 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14544) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14544.1, data_15_14544.2]

/-- Complete interval computation for depth 15, residue 14545. -/
theorem bounds_15_14545 : exactInterval 15 14545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14545 : oddCount 14545 15 = 9 ∧ acceleratedOrbit 15 14545 = 8741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14545) = 3 ^ 9 * m + 8741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14545.1, data_15_14545.2]

/-- Complete interval computation for depth 15, residue 14546. -/
theorem bounds_15_14546 : exactInterval 15 14546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14546 : oddCount 14546 15 = 9 ∧ acceleratedOrbit 15 14546 = 8741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14546) = 3 ^ 9 * m + 8741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14546.1, data_15_14546.2]

/-- Complete interval computation for depth 15, residue 14547. -/
theorem bounds_15_14547 : exactInterval 15 14547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14547 : oddCount 14547 15 = 9 ∧ acceleratedOrbit 15 14547 = 8741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14547) = 3 ^ 9 * m + 8741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14547.1, data_15_14547.2]

end Collatz.Research.PassageAtlas.Batch0444
