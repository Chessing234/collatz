import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0359

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2426. -/
theorem bounds_12_2426 : exactInterval 12 2426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2426 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2426) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2426 : oddCount 2426 12 = 6 ∧ acceleratedOrbit 12 2426 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2426 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2426) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2426.1, data_12_2426.2]

/-- Complete interval computation for depth 12, residue 2427. -/
theorem bounds_12_2427 : exactInterval 12 2427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2427 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2427) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2427 : oddCount 2427 12 = 7 ∧ acceleratedOrbit 12 2427 = 1297 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2427 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2427) = 3 ^ 7 * m + 1297 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2427.1, data_12_2427.2]

/-- Complete interval computation for depth 12, residue 2428. -/
theorem bounds_12_2428 : exactInterval 12 2428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2428 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2428) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2428 : oddCount 2428 12 = 6 ∧ acceleratedOrbit 12 2428 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2428 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2428) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2428.1, data_12_2428.2]

/-- Complete interval computation for depth 12, residue 2429. -/
theorem bounds_12_2429 : exactInterval 12 2429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2429 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2429) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2429 : oddCount 2429 12 = 6 ∧ acceleratedOrbit 12 2429 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2429 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2429) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2429.1, data_12_2429.2]

/-- Complete interval computation for depth 12, residue 2430. -/
theorem bounds_12_2430 : exactInterval 12 2430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2430 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2430) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2430 : oddCount 2430 12 = 8 ∧ acceleratedOrbit 12 2430 = 3896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2430 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2430) = 3 ^ 8 * m + 3896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2430.1, data_12_2430.2]

/-- Complete interval computation for depth 12, residue 2431. -/
theorem bounds_12_2431 : exactInterval 12 2431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2431 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2431) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2431 : oddCount 2431 12 = 8 ∧ acceleratedOrbit 12 2431 = 3896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2431 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2431) = 3 ^ 8 * m + 3896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2431.1, data_12_2431.2]

/-- Complete interval computation for depth 12, residue 2432. -/
theorem bounds_12_2432 : exactInterval 12 2432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2432 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2432) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2432 : oddCount 2432 12 = 3 ∧ acceleratedOrbit 12 2432 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2432 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2432) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2432.1, data_12_2432.2]

/-- Complete interval computation for depth 12, residue 2433. -/
theorem bounds_12_2433 : exactInterval 12 2433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2433 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2433) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2433 : oddCount 2433 12 = 6 ∧ acceleratedOrbit 12 2433 = 434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2433 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2433) = 3 ^ 6 * m + 434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2433.1, data_12_2433.2]

/-- Complete interval computation for depth 12, residue 2434. -/
theorem bounds_12_2434 : exactInterval 12 2434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2434 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2434) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2434 : oddCount 2434 12 = 5 ∧ acceleratedOrbit 12 2434 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2434 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2434) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2434.1, data_12_2434.2]

/-- Complete interval computation for depth 12, residue 2435. -/
theorem bounds_12_2435 : exactInterval 12 2435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2435 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2435) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2435 : oddCount 2435 12 = 5 ∧ acceleratedOrbit 12 2435 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2435 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2435) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2435.1, data_12_2435.2]

/-- Complete interval computation for depth 12, residue 2436. -/
theorem bounds_12_2436 : exactInterval 12 2436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2436 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2436) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2436 : oddCount 2436 12 = 5 ∧ acceleratedOrbit 12 2436 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2436 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2436) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2436.1, data_12_2436.2]

/-- Complete interval computation for depth 12, residue 2437. -/
theorem bounds_12_2437 : exactInterval 12 2437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2437 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2437) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2437 : oddCount 2437 12 = 5 ∧ acceleratedOrbit 12 2437 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2437 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2437) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2437.1, data_12_2437.2]

/-- Complete interval computation for depth 12, residue 2438. -/
theorem bounds_12_2438 : exactInterval 12 2438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2438 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2438) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2438 : oddCount 2438 12 = 5 ∧ acceleratedOrbit 12 2438 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2438 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2438) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2438.1, data_12_2438.2]

/-- Complete interval computation for depth 12, residue 2439. -/
theorem bounds_12_2439 : exactInterval 12 2439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2439 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2439) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2439 : oddCount 2439 12 = 5 ∧ acceleratedOrbit 12 2439 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2439 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2439) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2439.1, data_12_2439.2]

/-- Complete interval computation for depth 12, residue 2440. -/
theorem bounds_12_2440 : exactInterval 12 2440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2440 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2440) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2440 : oddCount 2440 12 = 4 ∧ acceleratedOrbit 12 2440 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2440 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2440) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2440.1, data_12_2440.2]

/-- Complete interval computation for depth 12, residue 2441. -/
theorem bounds_12_2441 : exactInterval 12 2441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2441 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2441) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2441 : oddCount 2441 12 = 8 ∧ acceleratedOrbit 12 2441 = 3914 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2441 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2441) = 3 ^ 8 * m + 3914 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2441.1, data_12_2441.2]

end Collatz.Research.StoppingAtlas.Batch0359
