import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0826

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5504. -/
theorem bounds_13_5504 : exactInterval 13 5504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5504 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5504) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5504 : oddCount 5504 13 = 4 ∧ acceleratedOrbit 13 5504 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5504 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5504) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5504.1, data_13_5504.2]

/-- Complete interval computation for depth 13, residue 5505. -/
theorem bounds_13_5505 : exactInterval 13 5505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5505 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5505) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5505 : oddCount 5505 13 = 7 ∧ acceleratedOrbit 13 5505 = 1471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5505 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5505) = 3 ^ 7 * m + 1471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5505.1, data_13_5505.2]

/-- Complete interval computation for depth 13, residue 5506. -/
theorem bounds_13_5506 : exactInterval 13 5506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5506 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5506) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5506 : oddCount 5506 13 = 5 ∧ acceleratedOrbit 13 5506 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5506 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5506) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5506.1, data_13_5506.2]

/-- Complete interval computation for depth 13, residue 5507. -/
theorem bounds_13_5507 : exactInterval 13 5507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5507 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5507) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5507 : oddCount 5507 13 = 5 ∧ acceleratedOrbit 13 5507 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5507 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5507) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5507.1, data_13_5507.2]

/-- Complete interval computation for depth 13, residue 5508. -/
theorem bounds_13_5508 : exactInterval 13 5508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5508 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5508) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5508 : oddCount 5508 13 = 6 ∧ acceleratedOrbit 13 5508 = 491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5508 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5508) = 3 ^ 6 * m + 491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5508.1, data_13_5508.2]

/-- Complete interval computation for depth 13, residue 5509. -/
theorem bounds_13_5509 : exactInterval 13 5509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5509 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5509) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5509 : oddCount 5509 13 = 6 ∧ acceleratedOrbit 13 5509 = 491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5509 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5509) = 3 ^ 6 * m + 491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5509.1, data_13_5509.2]

/-- Complete interval computation for depth 13, residue 5510. -/
theorem bounds_13_5510 : exactInterval 13 5510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5510 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5510) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5510 : oddCount 5510 13 = 6 ∧ acceleratedOrbit 13 5510 = 491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5510 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5510) = 3 ^ 6 * m + 491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5510.1, data_13_5510.2]

/-- Complete interval computation for depth 13, residue 5511. -/
theorem bounds_13_5511 : exactInterval 13 5511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5511 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5511) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5511 : oddCount 5511 13 = 5 ∧ acceleratedOrbit 13 5511 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5511 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5511) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5511.1, data_13_5511.2]

/-- Complete interval computation for depth 13, residue 5512. -/
theorem bounds_13_5512 : exactInterval 13 5512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5512 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5512) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5512 : oddCount 5512 13 = 4 ∧ acceleratedOrbit 13 5512 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5512 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5512) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5512.1, data_13_5512.2]

/-- Complete interval computation for depth 13, residue 5513. -/
theorem bounds_13_5513 : exactInterval 13 5513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5513 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5513) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5513 : oddCount 5513 13 = 8 ∧ acceleratedOrbit 13 5513 = 4418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5513 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5513) = 3 ^ 8 * m + 4418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5513.1, data_13_5513.2]

/-- Complete interval computation for depth 13, residue 5514. -/
theorem bounds_13_5514 : exactInterval 13 5514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5514 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5514) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5514 : oddCount 5514 13 = 4 ∧ acceleratedOrbit 13 5514 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5514 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5514) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5514.1, data_13_5514.2]

/-- Complete interval computation for depth 13, residue 5515. -/
theorem bounds_13_5515 : exactInterval 13 5515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5515 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5515) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5515 : oddCount 5515 13 = 6 ∧ acceleratedOrbit 13 5515 = 491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5515 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5515) = 3 ^ 6 * m + 491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5515.1, data_13_5515.2]

/-- Complete interval computation for depth 13, residue 5516. -/
theorem bounds_13_5516 : exactInterval 13 5516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5516 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5516) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5516 : oddCount 5516 13 = 4 ∧ acceleratedOrbit 13 5516 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5516 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5516) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5516.1, data_13_5516.2]

/-- Complete interval computation for depth 13, residue 5517. -/
theorem bounds_13_5517 : exactInterval 13 5517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5517 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5517) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5517 : oddCount 5517 13 = 4 ∧ acceleratedOrbit 13 5517 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5517 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5517) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5517.1, data_13_5517.2]

/-- Complete interval computation for depth 13, residue 5518. -/
theorem bounds_13_5518 : exactInterval 13 5518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5518 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5518) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5518 : oddCount 5518 13 = 7 ∧ acceleratedOrbit 13 5518 = 1475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5518 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5518) = 3 ^ 7 * m + 1475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5518.1, data_13_5518.2]

end Collatz.Research.StoppingAtlas.Batch0826
