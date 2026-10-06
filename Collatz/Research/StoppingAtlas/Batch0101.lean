import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0101

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 512. -/
theorem bounds_11_512 : exactInterval 11 512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_512 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 512) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_512 : oddCount 512 11 = 1 ∧ acceleratedOrbit 11 512 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_512 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 512) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_512.1, data_11_512.2]

/-- Complete interval computation for depth 11, residue 513. -/
theorem bounds_11_513 : exactInterval 11 513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_513 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 513) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_513 : oddCount 513 11 = 6 ∧ acceleratedOrbit 11 513 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_513 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 513) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_513.1, data_11_513.2]

/-- Complete interval computation for depth 11, residue 514. -/
theorem bounds_11_514 : exactInterval 11 514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_514 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 514) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_514 : oddCount 514 11 = 5 ∧ acceleratedOrbit 11 514 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_514 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 514) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_514.1, data_11_514.2]

/-- Complete interval computation for depth 11, residue 515. -/
theorem bounds_11_515 : exactInterval 11 515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_515 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 515) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_515 : oddCount 515 11 = 5 ∧ acceleratedOrbit 11 515 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_515 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 515) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_515.1, data_11_515.2]

/-- Complete interval computation for depth 11, residue 516. -/
theorem bounds_11_516 : exactInterval 11 516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_516 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 516) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_516 : oddCount 516 11 = 6 ∧ acceleratedOrbit 11 516 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_516 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 516) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_516.1, data_11_516.2]

/-- Complete interval computation for depth 11, residue 517. -/
theorem bounds_11_517 : exactInterval 11 517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_517 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 517) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_517 : oddCount 517 11 = 6 ∧ acceleratedOrbit 11 517 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_517 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 517) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_517.1, data_11_517.2]

/-- Complete interval computation for depth 11, residue 518. -/
theorem bounds_11_518 : exactInterval 11 518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_518 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 518) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_518 : oddCount 518 11 = 6 ∧ acceleratedOrbit 11 518 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_518 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 518) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_518.1, data_11_518.2]

/-- Complete interval computation for depth 11, residue 519. -/
theorem bounds_11_519 : exactInterval 11 519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_519 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 519) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_519 : oddCount 519 11 = 7 ∧ acceleratedOrbit 11 519 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_519 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 519) = 3 ^ 7 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_519.1, data_11_519.2]

/-- Complete interval computation for depth 11, residue 520. -/
theorem bounds_11_520 : exactInterval 11 520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_520 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 520) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_520 : oddCount 520 11 = 3 ∧ acceleratedOrbit 11 520 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_520 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 520) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_520.1, data_11_520.2]

/-- Complete interval computation for depth 11, residue 521. -/
theorem bounds_11_521 : exactInterval 11 521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_521 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 521) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_521 : oddCount 521 11 = 5 ∧ acceleratedOrbit 11 521 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_521 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 521) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_521.1, data_11_521.2]

/-- Complete interval computation for depth 11, residue 522. -/
theorem bounds_11_522 : exactInterval 11 522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_522 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 522) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_522 : oddCount 522 11 = 3 ∧ acceleratedOrbit 11 522 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_522 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 522) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_522.1, data_11_522.2]

/-- Complete interval computation for depth 11, residue 523. -/
theorem bounds_11_523 : exactInterval 11 523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_523 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 523) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_523 : oddCount 523 11 = 6 ∧ acceleratedOrbit 11 523 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_523 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 523) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_523.1, data_11_523.2]

/-- Complete interval computation for depth 11, residue 524. -/
theorem bounds_11_524 : exactInterval 11 524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_524 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 524) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_524 : oddCount 524 11 = 3 ∧ acceleratedOrbit 11 524 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_524 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 524) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_524.1, data_11_524.2]

/-- Complete interval computation for depth 11, residue 525. -/
theorem bounds_11_525 : exactInterval 11 525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_525 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 525) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_525 : oddCount 525 11 = 3 ∧ acceleratedOrbit 11 525 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_525 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 525) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_525.1, data_11_525.2]

/-- Complete interval computation for depth 11, residue 526. -/
theorem bounds_11_526 : exactInterval 11 526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_526 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 526) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_526 : oddCount 526 11 = 7 ∧ acceleratedOrbit 11 526 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_526 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 526) = 3 ^ 7 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_526.1, data_11_526.2]

end Collatz.Research.StoppingAtlas.Batch0101
