import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0822

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5442. -/
theorem bounds_13_5442 : exactInterval 13 5442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5442 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5442) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5442 : oddCount 5442 13 = 8 ∧ acceleratedOrbit 13 5442 = 4364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5442 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5442) = 3 ^ 8 * m + 4364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5442.1, data_13_5442.2]

/-- Complete interval computation for depth 13, residue 5443. -/
theorem bounds_13_5443 : exactInterval 13 5443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5443 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5443) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5443 : oddCount 5443 13 = 8 ∧ acceleratedOrbit 13 5443 = 4364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5443 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5443) = 3 ^ 8 * m + 4364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5443.1, data_13_5443.2]

/-- Complete interval computation for depth 13, residue 5444. -/
theorem bounds_13_5444 : exactInterval 13 5444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5444 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5444) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5444 : oddCount 5444 13 = 8 ∧ acceleratedOrbit 13 5444 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5444 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5444) = 3 ^ 8 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5444.1, data_13_5444.2]

/-- Complete interval computation for depth 13, residue 5445. -/
theorem bounds_13_5445 : exactInterval 13 5445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5445 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5445) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5445 : oddCount 5445 13 = 8 ∧ acceleratedOrbit 13 5445 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5445 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5445) = 3 ^ 8 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5445.1, data_13_5445.2]

/-- Complete interval computation for depth 13, residue 5446. -/
theorem bounds_13_5446 : exactInterval 13 5446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5446 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5446) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5446 : oddCount 5446 13 = 8 ∧ acceleratedOrbit 13 5446 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5446 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5446) = 3 ^ 8 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5446.1, data_13_5446.2]

/-- Complete interval computation for depth 13, residue 5447. -/
theorem bounds_13_5447 : exactInterval 13 5447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5447 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5447) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5447 : oddCount 5447 13 = 10 ∧ acceleratedOrbit 13 5447 = 39275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5447 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5447) = 3 ^ 10 * m + 39275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5447.1, data_13_5447.2]

/-- Complete interval computation for depth 13, residue 5448. -/
theorem bounds_13_5448 : exactInterval 13 5448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5448 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5448) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5448 : oddCount 5448 13 = 9 ∧ acceleratedOrbit 13 5448 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5448 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5448) = 3 ^ 9 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5448.1, data_13_5448.2]

/-- Complete interval computation for depth 13, residue 5449. -/
theorem bounds_13_5449 : exactInterval 13 5449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5449 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5449) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5449 : oddCount 5449 13 = 8 ∧ acceleratedOrbit 13 5449 = 4367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5449 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5449) = 3 ^ 8 * m + 4367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5449.1, data_13_5449.2]

/-- Complete interval computation for depth 13, residue 5450. -/
theorem bounds_13_5450 : exactInterval 13 5450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5450 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5450) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5450 : oddCount 5450 13 = 9 ∧ acceleratedOrbit 13 5450 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5450 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5450) = 3 ^ 9 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5450.1, data_13_5450.2]

/-- Complete interval computation for depth 13, residue 5451. -/
theorem bounds_13_5451 : exactInterval 13 5451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5451 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5451) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5451 : oddCount 5451 13 = 8 ∧ acceleratedOrbit 13 5451 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5451 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5451) = 3 ^ 8 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5451.1, data_13_5451.2]

/-- Complete interval computation for depth 13, residue 5452. -/
theorem bounds_13_5452 : exactInterval 13 5452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5452 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5452) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5452 : oddCount 5452 13 = 9 ∧ acceleratedOrbit 13 5452 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5452 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5452) = 3 ^ 9 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5452.1, data_13_5452.2]

/-- Complete interval computation for depth 13, residue 5453. -/
theorem bounds_13_5453 : exactInterval 13 5453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5453 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5453) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5453 : oddCount 5453 13 = 9 ∧ acceleratedOrbit 13 5453 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5453 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5453) = 3 ^ 9 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5453.1, data_13_5453.2]

/-- Complete interval computation for depth 13, residue 5454. -/
theorem bounds_13_5454 : exactInterval 13 5454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5454 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5454) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5454 : oddCount 5454 13 = 9 ∧ acceleratedOrbit 13 5454 = 13112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5454 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5454) = 3 ^ 9 * m + 13112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5454.1, data_13_5454.2]

/-- Complete interval computation for depth 13, residue 5455. -/
theorem bounds_13_5455 : exactInterval 13 5455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5455 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5455) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5455 : oddCount 5455 13 = 9 ∧ acceleratedOrbit 13 5455 = 13112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5455 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5455) = 3 ^ 9 * m + 13112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5455.1, data_13_5455.2]

/-- Complete interval computation for depth 13, residue 5456. -/
theorem bounds_13_5456 : exactInterval 13 5456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5456 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5456) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5456 : oddCount 5456 13 = 1 ∧ acceleratedOrbit 13 5456 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5456 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5456) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5456.1, data_13_5456.2]

end Collatz.Research.StoppingAtlas.Batch0822
