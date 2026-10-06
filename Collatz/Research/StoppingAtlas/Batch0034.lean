import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0034

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 506. -/
theorem bounds_10_506 : exactInterval 10 506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_506 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 506) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_506 : oddCount 506 10 = 6 ∧ acceleratedOrbit 10 506 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_506 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 506) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_506.1, data_10_506.2]

/-- Complete interval computation for depth 10, residue 507. -/
theorem bounds_10_507 : exactInterval 10 507 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_507 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 507) 10 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_507 : oddCount 507 10 = 6 ∧ acceleratedOrbit 10 507 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_507 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 507) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_507.1, data_10_507.2]

/-- Complete interval computation for depth 10, residue 508. -/
theorem bounds_10_508 : exactInterval 10 508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_508 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 508) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_508 : oddCount 508 10 = 7 ∧ acceleratedOrbit 10 508 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_508 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 508) = 3 ^ 7 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_508.1, data_10_508.2]

/-- Complete interval computation for depth 10, residue 509. -/
theorem bounds_10_509 : exactInterval 10 509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_509 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 509) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_509 : oddCount 509 10 = 7 ∧ acceleratedOrbit 10 509 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_509 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 509) = 3 ^ 7 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_509.1, data_10_509.2]

/-- Complete interval computation for depth 10, residue 510. -/
theorem bounds_10_510 : exactInterval 10 510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_510 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 510) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_510 : oddCount 510 10 = 8 ∧ acceleratedOrbit 10 510 = 3280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_510 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 510) = 3 ^ 8 * m + 3280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_510.1, data_10_510.2]

/-- Complete interval computation for depth 10, residue 511. -/
theorem bounds_10_511 : exactInterval 10 511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_511 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 511) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_511 : oddCount 511 10 = 9 ∧ acceleratedOrbit 10 511 = 9841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_511 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 511) = 3 ^ 9 * m + 9841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_511.1, data_10_511.2]

/-- Complete interval computation for depth 10, residue 512. -/
theorem bounds_10_512 : exactInterval 10 512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_512 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 512) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_512 : oddCount 512 10 = 1 ∧ acceleratedOrbit 10 512 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_512 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 512) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_512.1, data_10_512.2]

/-- Complete interval computation for depth 10, residue 513. -/
theorem bounds_10_513 : exactInterval 10 513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_513 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 513) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_513 : oddCount 513 10 = 6 ∧ acceleratedOrbit 10 513 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_513 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 513) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_513.1, data_10_513.2]

/-- Complete interval computation for depth 10, residue 514. -/
theorem bounds_10_514 : exactInterval 10 514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_514 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 514) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_514 : oddCount 514 10 = 4 ∧ acceleratedOrbit 10 514 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_514 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 514) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_514.1, data_10_514.2]

/-- Complete interval computation for depth 10, residue 515. -/
theorem bounds_10_515 : exactInterval 10 515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_515 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 515) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_515 : oddCount 515 10 = 4 ∧ acceleratedOrbit 10 515 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_515 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 515) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_515.1, data_10_515.2]

/-- Complete interval computation for depth 10, residue 516. -/
theorem bounds_10_516 : exactInterval 10 516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_516 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 516) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_516 : oddCount 516 10 = 5 ∧ acceleratedOrbit 10 516 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_516 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 516) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_516.1, data_10_516.2]

/-- Complete interval computation for depth 10, residue 517. -/
theorem bounds_10_517 : exactInterval 10 517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_517 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 517) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_517 : oddCount 517 10 = 5 ∧ acceleratedOrbit 10 517 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_517 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 517) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_517.1, data_10_517.2]

/-- Complete interval computation for depth 10, residue 518. -/
theorem bounds_10_518 : exactInterval 10 518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_518 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 518) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_518 : oddCount 518 10 = 5 ∧ acceleratedOrbit 10 518 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_518 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 518) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_518.1, data_10_518.2]

/-- Complete interval computation for depth 10, residue 519. -/
theorem bounds_10_519 : exactInterval 10 519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_519 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 519) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_519 : oddCount 519 10 = 6 ∧ acceleratedOrbit 10 519 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_519 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 519) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_519.1, data_10_519.2]

/-- Complete interval computation for depth 10, residue 520. -/
theorem bounds_10_520 : exactInterval 10 520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_520 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 520) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_520 : oddCount 520 10 = 3 ∧ acceleratedOrbit 10 520 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_520 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 520) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_520.1, data_10_520.2]

/-- Complete interval computation for depth 10, residue 521. -/
theorem bounds_10_521 : exactInterval 10 521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_521 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 521) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_521 : oddCount 521 10 = 5 ∧ acceleratedOrbit 10 521 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_521 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 521) = 3 ^ 5 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_521.1, data_10_521.2]

end Collatz.Research.StoppingAtlas.Batch0034
