import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0827

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5519. -/
theorem bounds_13_5519 : exactInterval 13 5519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5519 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5519) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5519 : oddCount 5519 13 = 7 ∧ acceleratedOrbit 13 5519 = 1475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5519 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5519) = 3 ^ 7 * m + 1475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5519.1, data_13_5519.2]

/-- Complete interval computation for depth 13, residue 5520. -/
theorem bounds_13_5520 : exactInterval 13 5520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5520 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5520) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5520 : oddCount 5520 13 = 4 ∧ acceleratedOrbit 13 5520 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5520 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5520) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5520.1, data_13_5520.2]

/-- Complete interval computation for depth 13, residue 5521. -/
theorem bounds_13_5521 : exactInterval 13 5521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5521 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5521) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5521 : oddCount 5521 13 = 5 ∧ acceleratedOrbit 13 5521 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5521 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5521) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5521.1, data_13_5521.2]

/-- Complete interval computation for depth 13, residue 5522. -/
theorem bounds_13_5522 : exactInterval 13 5522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5522 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5522) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5522 : oddCount 5522 13 = 5 ∧ acceleratedOrbit 13 5522 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5522 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5522) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5522.1, data_13_5522.2]

/-- Complete interval computation for depth 13, residue 5523. -/
theorem bounds_13_5523 : exactInterval 13 5523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5523 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5523) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5523 : oddCount 5523 13 = 5 ∧ acceleratedOrbit 13 5523 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5523 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5523) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5523.1, data_13_5523.2]

/-- Complete interval computation for depth 13, residue 5524. -/
theorem bounds_13_5524 : exactInterval 13 5524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5524 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5524) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5524 : oddCount 5524 13 = 4 ∧ acceleratedOrbit 13 5524 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5524 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5524) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5524.1, data_13_5524.2]

/-- Complete interval computation for depth 13, residue 5525. -/
theorem bounds_13_5525 : exactInterval 13 5525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5525 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5525) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5525 : oddCount 5525 13 = 4 ∧ acceleratedOrbit 13 5525 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5525 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5525) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5525.1, data_13_5525.2]

/-- Complete interval computation for depth 13, residue 5526. -/
theorem bounds_13_5526 : exactInterval 13 5526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5526 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5526) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5526 : oddCount 5526 13 = 7 ∧ acceleratedOrbit 13 5526 = 1478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5526 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5526) = 3 ^ 7 * m + 1478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5526.1, data_13_5526.2]

/-- Complete interval computation for depth 13, residue 5527. -/
theorem bounds_13_5527 : exactInterval 13 5527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5527 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5527) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5527 : oddCount 5527 13 = 7 ∧ acceleratedOrbit 13 5527 = 1478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5527 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5527) = 3 ^ 7 * m + 1478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5527.1, data_13_5527.2]

/-- Complete interval computation for depth 13, residue 5528. -/
theorem bounds_13_5528 : exactInterval 13 5528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5528 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5528) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5528 : oddCount 5528 13 = 4 ∧ acceleratedOrbit 13 5528 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5528 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5528) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5528.1, data_13_5528.2]

/-- Complete interval computation for depth 13, residue 5529. -/
theorem bounds_13_5529 : exactInterval 13 5529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5529 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5529) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5529 : oddCount 5529 13 = 7 ∧ acceleratedOrbit 13 5529 = 1478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5529 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5529) = 3 ^ 7 * m + 1478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5529.1, data_13_5529.2]

/-- Complete interval computation for depth 13, residue 5530. -/
theorem bounds_13_5530 : exactInterval 13 5530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5530 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5530) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5530 : oddCount 5530 13 = 4 ∧ acceleratedOrbit 13 5530 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5530 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5530) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5530.1, data_13_5530.2]

/-- Complete interval computation for depth 13, residue 5531. -/
theorem bounds_13_5531 : exactInterval 13 5531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5531 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5531) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5531 : oddCount 5531 13 = 7 ∧ acceleratedOrbit 13 5531 = 1477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5531 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5531) = 3 ^ 7 * m + 1477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5531.1, data_13_5531.2]

/-- Complete interval computation for depth 13, residue 5532. -/
theorem bounds_13_5532 : exactInterval 13 5532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5532 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5532) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5532 : oddCount 5532 13 = 9 ∧ acceleratedOrbit 13 5532 = 13304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5532 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5532) = 3 ^ 9 * m + 13304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5532.1, data_13_5532.2]

/-- Complete interval computation for depth 13, residue 5533. -/
theorem bounds_13_5533 : exactInterval 13 5533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5533 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5533) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5533 : oddCount 5533 13 = 9 ∧ acceleratedOrbit 13 5533 = 13304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5533 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5533) = 3 ^ 9 * m + 13304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5533.1, data_13_5533.2]

end Collatz.Research.StoppingAtlas.Batch0827
