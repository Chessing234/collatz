import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0169

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5505. -/
theorem bounds_15_5505 : exactInterval 15 5505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5505 : oddCount 5505 15 = 9 ∧ acceleratedOrbit 15 5505 = 3311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5505) = 3 ^ 9 * m + 3311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5505.1, data_15_5505.2]

/-- Complete interval computation for depth 15, residue 5506. -/
theorem bounds_15_5506 : exactInterval 15 5506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5506 : oddCount 5506 15 = 5 ∧ acceleratedOrbit 15 5506 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5506) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5506.1, data_15_5506.2]

/-- Complete interval computation for depth 15, residue 5507. -/
theorem bounds_15_5507 : exactInterval 15 5507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5507 : oddCount 5507 15 = 5 ∧ acceleratedOrbit 15 5507 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5507) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5507.1, data_15_5507.2]

/-- Complete interval computation for depth 15, residue 5508. -/
theorem bounds_15_5508 : exactInterval 15 5508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5508 : oddCount 5508 15 = 8 ∧ acceleratedOrbit 15 5508 = 1106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5508) = 3 ^ 8 * m + 1106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5508.1, data_15_5508.2]

/-- Complete interval computation for depth 15, residue 5509. -/
theorem bounds_15_5509 : exactInterval 15 5509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5509 : oddCount 5509 15 = 8 ∧ acceleratedOrbit 15 5509 = 1106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5509) = 3 ^ 8 * m + 1106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5509.1, data_15_5509.2]

/-- Complete interval computation for depth 15, residue 5510. -/
theorem bounds_15_5510 : exactInterval 15 5510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5510 : oddCount 5510 15 = 8 ∧ acceleratedOrbit 15 5510 = 1106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5510) = 3 ^ 8 * m + 1106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5510.1, data_15_5510.2]

/-- Complete interval computation for depth 15, residue 5511. -/
theorem bounds_15_5511 : exactInterval 15 5511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5511 : oddCount 5511 15 = 5 ∧ acceleratedOrbit 15 5511 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5511) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5511.1, data_15_5511.2]

/-- Complete interval computation for depth 15, residue 5512. -/
theorem bounds_15_5512 : exactInterval 15 5512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5512 : oddCount 5512 15 = 6 ∧ acceleratedOrbit 15 5512 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5512) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5512.1, data_15_5512.2]

/-- Complete interval computation for depth 15, residue 5513. -/
theorem bounds_15_5513 : exactInterval 15 5513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5513 : oddCount 5513 15 = 9 ∧ acceleratedOrbit 15 5513 = 3314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5513) = 3 ^ 9 * m + 3314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5513.1, data_15_5513.2]

/-- Complete interval computation for depth 15, residue 5514. -/
theorem bounds_15_5514 : exactInterval 15 5514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5514 : oddCount 5514 15 = 6 ∧ acceleratedOrbit 15 5514 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5514) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5514.1, data_15_5514.2]

/-- Complete interval computation for depth 15, residue 5515. -/
theorem bounds_15_5515 : exactInterval 15 5515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5515 : oddCount 5515 15 = 8 ∧ acceleratedOrbit 15 5515 = 1106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5515) = 3 ^ 8 * m + 1106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5515.1, data_15_5515.2]

/-- Complete interval computation for depth 15, residue 5516. -/
theorem bounds_15_5516 : exactInterval 15 5516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5516 : oddCount 5516 15 = 6 ∧ acceleratedOrbit 15 5516 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5516) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5516.1, data_15_5516.2]

/-- Complete interval computation for depth 15, residue 5517. -/
theorem bounds_15_5517 : exactInterval 15 5517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5517 : oddCount 5517 15 = 6 ∧ acceleratedOrbit 15 5517 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5517) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5517.1, data_15_5517.2]

/-- Complete interval computation for depth 15, residue 5518. -/
theorem bounds_15_5518 : exactInterval 15 5518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5518 : oddCount 5518 15 = 9 ∧ acceleratedOrbit 15 5518 = 3320 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5518) = 3 ^ 9 * m + 3320 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5518.1, data_15_5518.2]

/-- Complete interval computation for depth 15, residue 5519. -/
theorem bounds_15_5519 : exactInterval 15 5519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5519 : oddCount 5519 15 = 9 ∧ acceleratedOrbit 15 5519 = 3320 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5519) = 3 ^ 9 * m + 3320 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5519.1, data_15_5519.2]

/-- Complete interval computation for depth 15, residue 5520. -/
theorem bounds_15_5520 : exactInterval 15 5520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5520 : oddCount 5520 15 = 6 ∧ acceleratedOrbit 15 5520 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5520) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5520.1, data_15_5520.2]

/-- Complete interval computation for depth 15, residue 5521. -/
theorem bounds_15_5521 : exactInterval 15 5521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5521 : oddCount 5521 15 = 5 ∧ acceleratedOrbit 15 5521 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5521) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5521.1, data_15_5521.2]

/-- Complete interval computation for depth 15, residue 5522. -/
theorem bounds_15_5522 : exactInterval 15 5522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5522 : oddCount 5522 15 = 5 ∧ acceleratedOrbit 15 5522 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5522) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5522.1, data_15_5522.2]

/-- Complete interval computation for depth 15, residue 5523. -/
theorem bounds_15_5523 : exactInterval 15 5523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5523 : oddCount 5523 15 = 5 ∧ acceleratedOrbit 15 5523 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5523) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5523.1, data_15_5523.2]

/-- Complete interval computation for depth 15, residue 5524. -/
theorem bounds_15_5524 : exactInterval 15 5524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5524 : oddCount 5524 15 = 6 ∧ acceleratedOrbit 15 5524 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5524) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5524.1, data_15_5524.2]

/-- Complete interval computation for depth 15, residue 5525. -/
theorem bounds_15_5525 : exactInterval 15 5525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5525 : oddCount 5525 15 = 6 ∧ acceleratedOrbit 15 5525 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5525) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5525.1, data_15_5525.2]

/-- Complete interval computation for depth 15, residue 5526. -/
theorem bounds_15_5526 : exactInterval 15 5526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5526 : oddCount 5526 15 = 8 ∧ acceleratedOrbit 15 5526 = 1109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5526) = 3 ^ 8 * m + 1109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5526.1, data_15_5526.2]

/-- Complete interval computation for depth 15, residue 5527. -/
theorem bounds_15_5527 : exactInterval 15 5527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5527 : oddCount 5527 15 = 8 ∧ acceleratedOrbit 15 5527 = 1109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5527) = 3 ^ 8 * m + 1109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5527.1, data_15_5527.2]

/-- Complete interval computation for depth 15, residue 5528. -/
theorem bounds_15_5528 : exactInterval 15 5528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5528 : oddCount 5528 15 = 6 ∧ acceleratedOrbit 15 5528 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5528) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5528.1, data_15_5528.2]

/-- Complete interval computation for depth 15, residue 5529. -/
theorem bounds_15_5529 : exactInterval 15 5529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5529 : oddCount 5529 15 = 8 ∧ acceleratedOrbit 15 5529 = 1109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5529) = 3 ^ 8 * m + 1109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5529.1, data_15_5529.2]

/-- Complete interval computation for depth 15, residue 5530. -/
theorem bounds_15_5530 : exactInterval 15 5530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5530 : oddCount 5530 15 = 6 ∧ acceleratedOrbit 15 5530 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5530) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5530.1, data_15_5530.2]

/-- Complete interval computation for depth 15, residue 5531. -/
theorem bounds_15_5531 : exactInterval 15 5531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5531 : oddCount 5531 15 = 8 ∧ acceleratedOrbit 15 5531 = 1108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5531) = 3 ^ 8 * m + 1108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5531.1, data_15_5531.2]

/-- Complete interval computation for depth 15, residue 5532. -/
theorem bounds_15_5532 : exactInterval 15 5532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5532 : oddCount 5532 15 = 9 ∧ acceleratedOrbit 15 5532 = 3326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5532) = 3 ^ 9 * m + 3326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5532.1, data_15_5532.2]

/-- Complete interval computation for depth 15, residue 5533. -/
theorem bounds_15_5533 : exactInterval 15 5533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5533 : oddCount 5533 15 = 9 ∧ acceleratedOrbit 15 5533 = 3326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5533) = 3 ^ 9 * m + 3326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5533.1, data_15_5533.2]

/-- Complete interval computation for depth 15, residue 5534. -/
theorem bounds_15_5534 : exactInterval 15 5534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5534 : oddCount 5534 15 = 9 ∧ acceleratedOrbit 15 5534 = 3326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5534) = 3 ^ 9 * m + 3326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5534.1, data_15_5534.2]

/-- Complete interval computation for depth 15, residue 5535. -/
theorem bounds_15_5535 : exactInterval 15 5535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5535 : oddCount 5535 15 = 12 ∧ acceleratedOrbit 15 5535 = 89788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5535) = 3 ^ 12 * m + 89788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5535.1, data_15_5535.2]

/-- Complete interval computation for depth 15, residue 5536. -/
theorem bounds_15_5536 : exactInterval 15 5536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5536 : oddCount 5536 15 = 4 ∧ acceleratedOrbit 15 5536 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5536) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5536.1, data_15_5536.2]

end Collatz.Research.PassageAtlas.Batch0169
