import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0234

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 506. -/
theorem bounds_12_506 : exactInterval 12 506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_506 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 506) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_506 : oddCount 506 12 = 6 ∧ acceleratedOrbit 12 506 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_506 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 506) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_506.1, data_12_506.2]

/-- Complete interval computation for depth 12, residue 507. -/
theorem bounds_12_507 : exactInterval 12 507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_507 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 507) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_507 : oddCount 507 12 = 7 ∧ acceleratedOrbit 12 507 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_507 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 507) = 3 ^ 7 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_507.1, data_12_507.2]

/-- Complete interval computation for depth 12, residue 508. -/
theorem bounds_12_508 : exactInterval 12 508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_508 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 508) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_508 : oddCount 508 12 = 8 ∧ acceleratedOrbit 12 508 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_508 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 508) = 3 ^ 8 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_508.1, data_12_508.2]

/-- Complete interval computation for depth 12, residue 509. -/
theorem bounds_12_509 : exactInterval 12 509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_509 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 509) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_509 : oddCount 509 12 = 8 ∧ acceleratedOrbit 12 509 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_509 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 509) = 3 ^ 8 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_509.1, data_12_509.2]

/-- Complete interval computation for depth 12, residue 510. -/
theorem bounds_12_510 : exactInterval 12 510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_510 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 510) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_510 : oddCount 510 12 = 8 ∧ acceleratedOrbit 12 510 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_510 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 510) = 3 ^ 8 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_510.1, data_12_510.2]

/-- Complete interval computation for depth 12, residue 511. -/
theorem bounds_12_511 : exactInterval 12 511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_511 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 511) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_511 : oddCount 511 12 = 10 ∧ acceleratedOrbit 12 511 = 7381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_511 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 511) = 3 ^ 10 * m + 7381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_511.1, data_12_511.2]

/-- Complete interval computation for depth 12, residue 512. -/
theorem bounds_12_512 : exactInterval 12 512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_512 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 512) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_512 : oddCount 512 12 = 2 ∧ acceleratedOrbit 12 512 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_512 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 512) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_512.1, data_12_512.2]

/-- Complete interval computation for depth 12, residue 513. -/
theorem bounds_12_513 : exactInterval 12 513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_513 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 513) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_513 : oddCount 513 12 = 6 ∧ acceleratedOrbit 12 513 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_513 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 513) = 3 ^ 6 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_513.1, data_12_513.2]

/-- Complete interval computation for depth 12, residue 514. -/
theorem bounds_12_514 : exactInterval 12 514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_514 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 514) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_514 : oddCount 514 12 = 5 ∧ acceleratedOrbit 12 514 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_514 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 514) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_514.1, data_12_514.2]

/-- Complete interval computation for depth 12, residue 515. -/
theorem bounds_12_515 : exactInterval 12 515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_515 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 515) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_515 : oddCount 515 12 = 5 ∧ acceleratedOrbit 12 515 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_515 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 515) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_515.1, data_12_515.2]

/-- Complete interval computation for depth 12, residue 516. -/
theorem bounds_12_516 : exactInterval 12 516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_516 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 516) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_516 : oddCount 516 12 = 6 ∧ acceleratedOrbit 12 516 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_516 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 516) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_516.1, data_12_516.2]

/-- Complete interval computation for depth 12, residue 517. -/
theorem bounds_12_517 : exactInterval 12 517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_517 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 517) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_517 : oddCount 517 12 = 6 ∧ acceleratedOrbit 12 517 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_517 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 517) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_517.1, data_12_517.2]

/-- Complete interval computation for depth 12, residue 518. -/
theorem bounds_12_518 : exactInterval 12 518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_518 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 518) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_518 : oddCount 518 12 = 6 ∧ acceleratedOrbit 12 518 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_518 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 518) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_518.1, data_12_518.2]

/-- Complete interval computation for depth 12, residue 519. -/
theorem bounds_12_519 : exactInterval 12 519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_519 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 519) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_519 : oddCount 519 12 = 8 ∧ acceleratedOrbit 12 519 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_519 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 519) = 3 ^ 8 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_519.1, data_12_519.2]

/-- Complete interval computation for depth 12, residue 520. -/
theorem bounds_12_520 : exactInterval 12 520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_520 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 520) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_520 : oddCount 520 12 = 4 ∧ acceleratedOrbit 12 520 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_520 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 520) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_520.1, data_12_520.2]

/-- Complete interval computation for depth 12, residue 521. -/
theorem bounds_12_521 : exactInterval 12 521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_521 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 521) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_521 : oddCount 521 12 = 5 ∧ acceleratedOrbit 12 521 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_521 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 521) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_521.1, data_12_521.2]

end Collatz.Research.StoppingAtlas.Batch0234
