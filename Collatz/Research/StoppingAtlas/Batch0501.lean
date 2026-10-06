import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0501

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 512. -/
theorem bounds_13_512 : exactInterval 13 512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_512 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 512) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_512 : oddCount 512 13 = 2 ∧ acceleratedOrbit 13 512 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_512 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 512) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_512.1, data_13_512.2]

/-- Complete interval computation for depth 13, residue 513. -/
theorem bounds_13_513 : exactInterval 13 513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_513 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 513) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_513 : oddCount 513 13 = 6 ∧ acceleratedOrbit 13 513 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_513 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 513) = 3 ^ 6 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_513.1, data_13_513.2]

/-- Complete interval computation for depth 13, residue 514. -/
theorem bounds_13_514 : exactInterval 13 514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_514 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 514) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_514 : oddCount 514 13 = 6 ∧ acceleratedOrbit 13 514 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_514 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 514) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_514.1, data_13_514.2]

/-- Complete interval computation for depth 13, residue 515. -/
theorem bounds_13_515 : exactInterval 13 515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_515 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 515) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_515 : oddCount 515 13 = 6 ∧ acceleratedOrbit 13 515 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_515 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 515) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_515.1, data_13_515.2]

/-- Complete interval computation for depth 13, residue 516. -/
theorem bounds_13_516 : exactInterval 13 516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_516 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 516) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_516 : oddCount 516 13 = 6 ∧ acceleratedOrbit 13 516 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_516 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 516) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_516.1, data_13_516.2]

/-- Complete interval computation for depth 13, residue 517. -/
theorem bounds_13_517 : exactInterval 13 517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_517 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 517) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_517 : oddCount 517 13 = 6 ∧ acceleratedOrbit 13 517 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_517 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 517) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_517.1, data_13_517.2]

/-- Complete interval computation for depth 13, residue 518. -/
theorem bounds_13_518 : exactInterval 13 518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_518 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 518) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_518 : oddCount 518 13 = 6 ∧ acceleratedOrbit 13 518 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_518 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 518) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_518.1, data_13_518.2]

/-- Complete interval computation for depth 13, residue 519. -/
theorem bounds_13_519 : exactInterval 13 519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_519 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 519) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_519 : oddCount 519 13 = 8 ∧ acceleratedOrbit 13 519 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_519 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 519) = 3 ^ 8 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_519.1, data_13_519.2]

/-- Complete interval computation for depth 13, residue 520. -/
theorem bounds_13_520 : exactInterval 13 520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_520 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 520) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_520 : oddCount 520 13 = 5 ∧ acceleratedOrbit 13 520 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_520 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 520) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_520.1, data_13_520.2]

/-- Complete interval computation for depth 13, residue 521. -/
theorem bounds_13_521 : exactInterval 13 521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_521 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 521) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_521 : oddCount 521 13 = 6 ∧ acceleratedOrbit 13 521 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_521 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 521) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_521.1, data_13_521.2]

/-- Complete interval computation for depth 13, residue 522. -/
theorem bounds_13_522 : exactInterval 13 522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_522 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 522) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_522 : oddCount 522 13 = 5 ∧ acceleratedOrbit 13 522 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_522 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 522) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_522.1, data_13_522.2]

/-- Complete interval computation for depth 13, residue 523. -/
theorem bounds_13_523 : exactInterval 13 523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_523 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 523) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_523 : oddCount 523 13 = 6 ∧ acceleratedOrbit 13 523 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_523 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 523) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_523.1, data_13_523.2]

/-- Complete interval computation for depth 13, residue 524. -/
theorem bounds_13_524 : exactInterval 13 524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_524 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 524) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_524 : oddCount 524 13 = 5 ∧ acceleratedOrbit 13 524 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_524 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 524) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_524.1, data_13_524.2]

/-- Complete interval computation for depth 13, residue 525. -/
theorem bounds_13_525 : exactInterval 13 525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_525 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 525) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_525 : oddCount 525 13 = 5 ∧ acceleratedOrbit 13 525 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_525 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 525) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_525.1, data_13_525.2]

/-- Complete interval computation for depth 13, residue 526. -/
theorem bounds_13_526 : exactInterval 13 526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_526 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 526) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_526 : oddCount 526 13 = 8 ∧ acceleratedOrbit 13 526 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_526 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 526) = 3 ^ 8 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_526.1, data_13_526.2]

end Collatz.Research.StoppingAtlas.Batch0501
