import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0430

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3517. -/
theorem bounds_12_3517 : exactInterval 12 3517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3517 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3517) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3517 : oddCount 3517 12 = 7 ∧ acceleratedOrbit 12 3517 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3517 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3517) = 3 ^ 7 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3517.1, data_12_3517.2]

/-- Complete interval computation for depth 12, residue 3518. -/
theorem bounds_12_3518 : exactInterval 12 3518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3518 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3518) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3518 : oddCount 3518 12 = 7 ∧ acceleratedOrbit 12 3518 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3518 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3518) = 3 ^ 7 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3518.1, data_12_3518.2]

/-- Complete interval computation for depth 12, residue 3519. -/
theorem bounds_12_3519 : exactInterval 12 3519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3519 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3519) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3519 : oddCount 3519 12 = 10 ∧ acceleratedOrbit 12 3519 = 50746 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3519 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3519) = 3 ^ 10 * m + 50746 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3519.1, data_12_3519.2]

/-- Complete interval computation for depth 12, residue 3520. -/
theorem bounds_12_3520 : exactInterval 12 3520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3520 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3520) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3520 : oddCount 3520 12 = 4 ∧ acceleratedOrbit 12 3520 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3520 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3520) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3520.1, data_12_3520.2]

/-- Complete interval computation for depth 12, residue 3521. -/
theorem bounds_12_3521 : exactInterval 12 3521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3521 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3521) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3521 : oddCount 3521 12 = 7 ∧ acceleratedOrbit 12 3521 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3521 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3521) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3521.1, data_12_3521.2]

/-- Complete interval computation for depth 12, residue 3522. -/
theorem bounds_12_3522 : exactInterval 12 3522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3522 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3522) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3522 : oddCount 3522 12 = 7 ∧ acceleratedOrbit 12 3522 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3522 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3522) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3522.1, data_12_3522.2]

/-- Complete interval computation for depth 12, residue 3523. -/
theorem bounds_12_3523 : exactInterval 12 3523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3523 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3523) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3523 : oddCount 3523 12 = 7 ∧ acceleratedOrbit 12 3523 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3523 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3523) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3523.1, data_12_3523.2]

/-- Complete interval computation for depth 12, residue 3524. -/
theorem bounds_12_3524 : exactInterval 12 3524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3524 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3524) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3524 : oddCount 3524 12 = 4 ∧ acceleratedOrbit 12 3524 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3524 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3524) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3524.1, data_12_3524.2]

/-- Complete interval computation for depth 12, residue 3525. -/
theorem bounds_12_3525 : exactInterval 12 3525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3525 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3525) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3525 : oddCount 3525 12 = 4 ∧ acceleratedOrbit 12 3525 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3525 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3525) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3525.1, data_12_3525.2]

/-- Complete interval computation for depth 12, residue 3526. -/
theorem bounds_12_3526 : exactInterval 12 3526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3526 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3526) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3526 : oddCount 3526 12 = 4 ∧ acceleratedOrbit 12 3526 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3526 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3526) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3526.1, data_12_3526.2]

/-- Complete interval computation for depth 12, residue 3527. -/
theorem bounds_12_3527 : exactInterval 12 3527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3527 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3527) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3527 : oddCount 3527 12 = 6 ∧ acceleratedOrbit 12 3527 = 628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3527 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3527) = 3 ^ 6 * m + 628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3527.1, data_12_3527.2]

/-- Complete interval computation for depth 12, residue 3528. -/
theorem bounds_12_3528 : exactInterval 12 3528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3528 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3528) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3528 : oddCount 3528 12 = 4 ∧ acceleratedOrbit 12 3528 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3528 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3528) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3528.1, data_12_3528.2]

/-- Complete interval computation for depth 12, residue 3529. -/
theorem bounds_12_3529 : exactInterval 12 3529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3529 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3529) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3529 : oddCount 3529 12 = 6 ∧ acceleratedOrbit 12 3529 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3529 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3529) = 3 ^ 6 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3529.1, data_12_3529.2]

/-- Complete interval computation for depth 12, residue 3530. -/
theorem bounds_12_3530 : exactInterval 12 3530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3530 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3530) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3530 : oddCount 3530 12 = 4 ∧ acceleratedOrbit 12 3530 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3530 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3530) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3530.1, data_12_3530.2]

/-- Complete interval computation for depth 12, residue 3531. -/
theorem bounds_12_3531 : exactInterval 12 3531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3531 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3531) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3531 : oddCount 3531 12 = 7 ∧ acceleratedOrbit 12 3531 = 1889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3531 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3531) = 3 ^ 7 * m + 1889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3531.1, data_12_3531.2]

end Collatz.Research.StoppingAtlas.Batch0430
