import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0892

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6517. -/
theorem bounds_13_6517 : exactInterval 13 6517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6517 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6517) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6517 : oddCount 6517 13 = 4 ∧ acceleratedOrbit 13 6517 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6517 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6517) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6517.1, data_13_6517.2]

/-- Complete interval computation for depth 13, residue 6518. -/
theorem bounds_13_6518 : exactInterval 13 6518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6518 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6518) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6518 : oddCount 6518 13 = 8 ∧ acceleratedOrbit 13 6518 = 5224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6518 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6518) = 3 ^ 8 * m + 5224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6518.1, data_13_6518.2]

/-- Complete interval computation for depth 13, residue 6519. -/
theorem bounds_13_6519 : exactInterval 13 6519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6519 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6519) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6519 : oddCount 6519 13 = 8 ∧ acceleratedOrbit 13 6519 = 5224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6519 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6519) = 3 ^ 8 * m + 5224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6519.1, data_13_6519.2]

/-- Complete interval computation for depth 13, residue 6520. -/
theorem bounds_13_6520 : exactInterval 13 6520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6520 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6520) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6520 : oddCount 6520 13 = 6 ∧ acceleratedOrbit 13 6520 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6520 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6520) = 3 ^ 6 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6520.1, data_13_6520.2]

/-- Complete interval computation for depth 13, residue 6521. -/
theorem bounds_13_6521 : exactInterval 13 6521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6521 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6521) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6521 : oddCount 6521 13 = 10 ∧ acceleratedOrbit 13 6521 = 47020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6521 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6521) = 3 ^ 10 * m + 47020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6521.1, data_13_6521.2]

/-- Complete interval computation for depth 13, residue 6522. -/
theorem bounds_13_6522 : exactInterval 13 6522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6522 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6522) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6522 : oddCount 6522 13 = 6 ∧ acceleratedOrbit 13 6522 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6522 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6522) = 3 ^ 6 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6522.1, data_13_6522.2]

/-- Complete interval computation for depth 13, residue 6523. -/
theorem bounds_13_6523 : exactInterval 13 6523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6523 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6523) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6523 : oddCount 6523 13 = 7 ∧ acceleratedOrbit 13 6523 = 1742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6523 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6523) = 3 ^ 7 * m + 1742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6523.1, data_13_6523.2]

/-- Complete interval computation for depth 13, residue 6524. -/
theorem bounds_13_6524 : exactInterval 13 6524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6524 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6524) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6524 : oddCount 6524 13 = 6 ∧ acceleratedOrbit 13 6524 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6524 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6524) = 3 ^ 6 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6524.1, data_13_6524.2]

/-- Complete interval computation for depth 13, residue 6525. -/
theorem bounds_13_6525 : exactInterval 13 6525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6525 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6525) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6525 : oddCount 6525 13 = 6 ∧ acceleratedOrbit 13 6525 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6525 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6525) = 3 ^ 6 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6525.1, data_13_6525.2]

/-- Complete interval computation for depth 13, residue 6526. -/
theorem bounds_13_6526 : exactInterval 13 6526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6526 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6526) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6526 : oddCount 6526 13 = 9 ∧ acceleratedOrbit 13 6526 = 15686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6526 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6526) = 3 ^ 9 * m + 15686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6526.1, data_13_6526.2]

/-- Complete interval computation for depth 13, residue 6527. -/
theorem bounds_13_6527 : exactInterval 13 6527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6527 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6527) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6527 : oddCount 6527 13 = 9 ∧ acceleratedOrbit 13 6527 = 15686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6527 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6527) = 3 ^ 9 * m + 15686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6527.1, data_13_6527.2]

/-- Complete interval computation for depth 13, residue 6528. -/
theorem bounds_13_6528 : exactInterval 13 6528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6528 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6528) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6528 : oddCount 6528 13 = 3 ∧ acceleratedOrbit 13 6528 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6528 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6528) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6528.1, data_13_6528.2]

/-- Complete interval computation for depth 13, residue 6529. -/
theorem bounds_13_6529 : exactInterval 13 6529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6529 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6529) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6529 : oddCount 6529 13 = 7 ∧ acceleratedOrbit 13 6529 = 1745 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6529 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6529) = 3 ^ 7 * m + 1745 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6529.1, data_13_6529.2]

/-- Complete interval computation for depth 13, residue 6530. -/
theorem bounds_13_6530 : exactInterval 13 6530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6530 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6530) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6530 : oddCount 6530 13 = 5 ∧ acceleratedOrbit 13 6530 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6530 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6530) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6530.1, data_13_6530.2]

/-- Complete interval computation for depth 13, residue 6531. -/
theorem bounds_13_6531 : exactInterval 13 6531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6531 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6531) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6531 : oddCount 6531 13 = 5 ∧ acceleratedOrbit 13 6531 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6531 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6531) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6531.1, data_13_6531.2]

/-- Complete interval computation for depth 13, residue 6532. -/
theorem bounds_13_6532 : exactInterval 13 6532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6532 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6532) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6532 : oddCount 6532 13 = 5 ∧ acceleratedOrbit 13 6532 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6532 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6532) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6532.1, data_13_6532.2]

end Collatz.Research.StoppingAtlas.Batch0892
