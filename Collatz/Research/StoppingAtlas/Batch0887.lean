import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0887

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6440. -/
theorem bounds_13_6440 : exactInterval 13 6440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6440 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6440) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6440 : oddCount 6440 13 = 4 ∧ acceleratedOrbit 13 6440 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6440 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6440) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6440.1, data_13_6440.2]

/-- Complete interval computation for depth 13, residue 6441. -/
theorem bounds_13_6441 : exactInterval 13 6441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6441 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6441) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6441 : oddCount 6441 13 = 7 ∧ acceleratedOrbit 13 6441 = 1720 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6441 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6441) = 3 ^ 7 * m + 1720 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6441.1, data_13_6441.2]

/-- Complete interval computation for depth 13, residue 6442. -/
theorem bounds_13_6442 : exactInterval 13 6442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6442 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6442) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6442 : oddCount 6442 13 = 4 ∧ acceleratedOrbit 13 6442 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6442 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6442) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6442.1, data_13_6442.2]

/-- Complete interval computation for depth 13, residue 6443. -/
theorem bounds_13_6443 : exactInterval 13 6443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6443 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6443) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6443 : oddCount 6443 13 = 7 ∧ acceleratedOrbit 13 6443 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6443 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6443) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6443.1, data_13_6443.2]

/-- Complete interval computation for depth 13, residue 6444. -/
theorem bounds_13_6444 : exactInterval 13 6444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6444 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6444) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6444 : oddCount 6444 13 = 4 ∧ acceleratedOrbit 13 6444 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6444 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6444) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6444.1, data_13_6444.2]

/-- Complete interval computation for depth 13, residue 6445. -/
theorem bounds_13_6445 : exactInterval 13 6445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6445 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6445) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6445 : oddCount 6445 13 = 4 ∧ acceleratedOrbit 13 6445 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6445 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6445) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6445.1, data_13_6445.2]

/-- Complete interval computation for depth 13, residue 6446. -/
theorem bounds_13_6446 : exactInterval 13 6446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6446 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6446) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6446 : oddCount 6446 13 = 4 ∧ acceleratedOrbit 13 6446 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6446 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6446) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6446.1, data_13_6446.2]

/-- Complete interval computation for depth 13, residue 6447. -/
theorem bounds_13_6447 : exactInterval 13 6447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6447 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6447) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6447 : oddCount 6447 13 = 8 ∧ acceleratedOrbit 13 6447 = 5165 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6447 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6447) = 3 ^ 8 * m + 5165 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6447.1, data_13_6447.2]

/-- Complete interval computation for depth 13, residue 6448. -/
theorem bounds_13_6448 : exactInterval 13 6448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6448 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6448) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6448 : oddCount 6448 13 = 4 ∧ acceleratedOrbit 13 6448 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6448 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6448) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6448.1, data_13_6448.2]

/-- Complete interval computation for depth 13, residue 6449. -/
theorem bounds_13_6449 : exactInterval 13 6449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6449 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6449) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6449 : oddCount 6449 13 = 6 ∧ acceleratedOrbit 13 6449 = 575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6449 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6449) = 3 ^ 6 * m + 575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6449.1, data_13_6449.2]

/-- Complete interval computation for depth 13, residue 6450. -/
theorem bounds_13_6450 : exactInterval 13 6450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6450 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6450) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6450 : oddCount 6450 13 = 6 ∧ acceleratedOrbit 13 6450 = 575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6450 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6450) = 3 ^ 6 * m + 575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6450.1, data_13_6450.2]

/-- Complete interval computation for depth 13, residue 6451. -/
theorem bounds_13_6451 : exactInterval 13 6451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6451 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6451) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6451 : oddCount 6451 13 = 6 ∧ acceleratedOrbit 13 6451 = 575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6451 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6451) = 3 ^ 6 * m + 575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6451.1, data_13_6451.2]

/-- Complete interval computation for depth 13, residue 6452. -/
theorem bounds_13_6452 : exactInterval 13 6452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6452 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6452) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6452 : oddCount 6452 13 = 4 ∧ acceleratedOrbit 13 6452 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6452 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6452) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6452.1, data_13_6452.2]

/-- Complete interval computation for depth 13, residue 6453. -/
theorem bounds_13_6453 : exactInterval 13 6453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6453 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6453) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6453 : oddCount 6453 13 = 4 ∧ acceleratedOrbit 13 6453 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6453 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6453) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6453.1, data_13_6453.2]

/-- Complete interval computation for depth 13, residue 6454. -/
theorem bounds_13_6454 : exactInterval 13 6454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6454 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6454) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6454 : oddCount 6454 13 = 9 ∧ acceleratedOrbit 13 6454 = 15515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6454 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6454) = 3 ^ 9 * m + 15515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6454.1, data_13_6454.2]

/-- Complete interval computation for depth 13, residue 6455. -/
theorem bounds_13_6455 : exactInterval 13 6455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6455 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6455) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6455 : oddCount 6455 13 = 9 ∧ acceleratedOrbit 13 6455 = 15515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6455 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6455) = 3 ^ 9 * m + 15515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6455.1, data_13_6455.2]

end Collatz.Research.StoppingAtlas.Batch0887
