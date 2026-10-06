import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0035

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 522. -/
theorem bounds_10_522 : exactInterval 10 522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_522 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 522) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_522 : oddCount 522 10 = 3 ∧ acceleratedOrbit 10 522 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_522 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 522) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_522.1, data_10_522.2]

/-- Complete interval computation for depth 10, residue 523. -/
theorem bounds_10_523 : exactInterval 10 523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_523 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 523) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_523 : oddCount 523 10 = 5 ∧ acceleratedOrbit 10 523 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_523 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 523) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_523.1, data_10_523.2]

/-- Complete interval computation for depth 10, residue 524. -/
theorem bounds_10_524 : exactInterval 10 524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_524 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 524) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_524 : oddCount 524 10 = 3 ∧ acceleratedOrbit 10 524 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_524 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 524) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_524.1, data_10_524.2]

/-- Complete interval computation for depth 10, residue 525. -/
theorem bounds_10_525 : exactInterval 10 525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_525 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 525) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_525 : oddCount 525 10 = 3 ∧ acceleratedOrbit 10 525 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_525 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 525) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_525.1, data_10_525.2]

/-- Complete interval computation for depth 10, residue 526. -/
theorem bounds_10_526 : exactInterval 10 526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_526 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 526) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_526 : oddCount 526 10 = 6 ∧ acceleratedOrbit 10 526 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_526 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 526) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_526.1, data_10_526.2]

/-- Complete interval computation for depth 10, residue 527. -/
theorem bounds_10_527 : exactInterval 10 527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_527 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 527) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_527 : oddCount 527 10 = 6 ∧ acceleratedOrbit 10 527 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_527 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 527) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_527.1, data_10_527.2]

/-- Complete interval computation for depth 10, residue 528. -/
theorem bounds_10_528 : exactInterval 10 528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_528 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 528) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_528 : oddCount 528 10 = 4 ∧ acceleratedOrbit 10 528 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_528 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 528) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_528.1, data_10_528.2]

/-- Complete interval computation for depth 10, residue 529. -/
theorem bounds_10_529 : exactInterval 10 529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_529 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 529) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_529 : oddCount 529 10 = 3 ∧ acceleratedOrbit 10 529 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_529 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 529) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_529.1, data_10_529.2]

/-- Complete interval computation for depth 10, residue 530. -/
theorem bounds_10_530 : exactInterval 10 530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_530 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 530) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_530 : oddCount 530 10 = 6 ∧ acceleratedOrbit 10 530 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_530 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 530) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_530.1, data_10_530.2]

/-- Complete interval computation for depth 10, residue 531. -/
theorem bounds_10_531 : exactInterval 10 531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_531 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 531) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_531 : oddCount 531 10 = 6 ∧ acceleratedOrbit 10 531 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_531 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 531) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_531.1, data_10_531.2]

/-- Complete interval computation for depth 10, residue 532. -/
theorem bounds_10_532 : exactInterval 10 532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_532 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 532) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_532 : oddCount 532 10 = 4 ∧ acceleratedOrbit 10 532 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_532 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 532) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_532.1, data_10_532.2]

/-- Complete interval computation for depth 10, residue 533. -/
theorem bounds_10_533 : exactInterval 10 533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_533 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 533) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_533 : oddCount 533 10 = 4 ∧ acceleratedOrbit 10 533 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_533 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 533) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_533.1, data_10_533.2]

/-- Complete interval computation for depth 10, residue 534. -/
theorem bounds_10_534 : exactInterval 10 534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_534 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 534) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_534 : oddCount 534 10 = 5 ∧ acceleratedOrbit 10 534 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_534 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 534) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_534.1, data_10_534.2]

/-- Complete interval computation for depth 10, residue 535. -/
theorem bounds_10_535 : exactInterval 10 535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_535 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 535) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_535 : oddCount 535 10 = 5 ∧ acceleratedOrbit 10 535 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_535 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 535) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_535.1, data_10_535.2]

/-- Complete interval computation for depth 10, residue 536. -/
theorem bounds_10_536 : exactInterval 10 536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_536 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 536) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_536 : oddCount 536 10 = 4 ∧ acceleratedOrbit 10 536 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_536 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 536) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_536.1, data_10_536.2]

end Collatz.Research.StoppingAtlas.Batch0035
