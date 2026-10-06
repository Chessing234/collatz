import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0235

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 522. -/
theorem bounds_12_522 : exactInterval 12 522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_522 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 522) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_522 : oddCount 522 12 = 4 ∧ acceleratedOrbit 12 522 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_522 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 522) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_522.1, data_12_522.2]

/-- Complete interval computation for depth 12, residue 523. -/
theorem bounds_12_523 : exactInterval 12 523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_523 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 523) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_523 : oddCount 523 12 = 6 ∧ acceleratedOrbit 12 523 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_523 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 523) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_523.1, data_12_523.2]

/-- Complete interval computation for depth 12, residue 524. -/
theorem bounds_12_524 : exactInterval 12 524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_524 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 524) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_524 : oddCount 524 12 = 4 ∧ acceleratedOrbit 12 524 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_524 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 524) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_524.1, data_12_524.2]

/-- Complete interval computation for depth 12, residue 525. -/
theorem bounds_12_525 : exactInterval 12 525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_525 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 525) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_525 : oddCount 525 12 = 4 ∧ acceleratedOrbit 12 525 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_525 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 525) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_525.1, data_12_525.2]

/-- Complete interval computation for depth 12, residue 526. -/
theorem bounds_12_526 : exactInterval 12 526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_526 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 526) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_526 : oddCount 526 12 = 7 ∧ acceleratedOrbit 12 526 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_526 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 526) = 3 ^ 7 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_526.1, data_12_526.2]

/-- Complete interval computation for depth 12, residue 527. -/
theorem bounds_12_527 : exactInterval 12 527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_527 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 527) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_527 : oddCount 527 12 = 7 ∧ acceleratedOrbit 12 527 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_527 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 527) = 3 ^ 7 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_527.1, data_12_527.2]

/-- Complete interval computation for depth 12, residue 528. -/
theorem bounds_12_528 : exactInterval 12 528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_528 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 528) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_528 : oddCount 528 12 = 4 ∧ acceleratedOrbit 12 528 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_528 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 528) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_528.1, data_12_528.2]

/-- Complete interval computation for depth 12, residue 529. -/
theorem bounds_12_529 : exactInterval 12 529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_529 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 529) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_529 : oddCount 529 12 = 4 ∧ acceleratedOrbit 12 529 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_529 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 529) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_529.1, data_12_529.2]

/-- Complete interval computation for depth 12, residue 530. -/
theorem bounds_12_530 : exactInterval 12 530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_530 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 530) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_530 : oddCount 530 12 = 6 ∧ acceleratedOrbit 12 530 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_530 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 530) = 3 ^ 6 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_530.1, data_12_530.2]

/-- Complete interval computation for depth 12, residue 531. -/
theorem bounds_12_531 : exactInterval 12 531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_531 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 531) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_531 : oddCount 531 12 = 6 ∧ acceleratedOrbit 12 531 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_531 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 531) = 3 ^ 6 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_531.1, data_12_531.2]

/-- Complete interval computation for depth 12, residue 532. -/
theorem bounds_12_532 : exactInterval 12 532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_532 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 532) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_532 : oddCount 532 12 = 4 ∧ acceleratedOrbit 12 532 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_532 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 532) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_532.1, data_12_532.2]

/-- Complete interval computation for depth 12, residue 533. -/
theorem bounds_12_533 : exactInterval 12 533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_533 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 533) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_533 : oddCount 533 12 = 4 ∧ acceleratedOrbit 12 533 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_533 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 533) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_533.1, data_12_533.2]

/-- Complete interval computation for depth 12, residue 534. -/
theorem bounds_12_534 : exactInterval 12 534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_534 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 534) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_534 : oddCount 534 12 = 5 ∧ acceleratedOrbit 12 534 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_534 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 534) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_534.1, data_12_534.2]

/-- Complete interval computation for depth 12, residue 535. -/
theorem bounds_12_535 : exactInterval 12 535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_535 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 535) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_535 : oddCount 535 12 = 5 ∧ acceleratedOrbit 12 535 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_535 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 535) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_535.1, data_12_535.2]

/-- Complete interval computation for depth 12, residue 536. -/
theorem bounds_12_536 : exactInterval 12 536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_536 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 536) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_536 : oddCount 536 12 = 4 ∧ acceleratedOrbit 12 536 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_536 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 536) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_536.1, data_12_536.2]

end Collatz.Research.StoppingAtlas.Batch0235
