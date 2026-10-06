import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0626

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2432. -/
theorem bounds_13_2432 : exactInterval 13 2432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2432 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2432) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2432 : oddCount 2432 13 = 4 ∧ acceleratedOrbit 13 2432 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2432 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2432) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2432.1, data_13_2432.2]

/-- Complete interval computation for depth 13, residue 2433. -/
theorem bounds_13_2433 : exactInterval 13 2433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2433 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2433) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2433 : oddCount 2433 13 = 6 ∧ acceleratedOrbit 13 2433 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2433 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2433) = 3 ^ 6 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2433.1, data_13_2433.2]

/-- Complete interval computation for depth 13, residue 2434. -/
theorem bounds_13_2434 : exactInterval 13 2434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2434 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2434) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2434 : oddCount 2434 13 = 6 ∧ acceleratedOrbit 13 2434 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2434 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2434) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2434.1, data_13_2434.2]

/-- Complete interval computation for depth 13, residue 2435. -/
theorem bounds_13_2435 : exactInterval 13 2435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2435 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2435) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2435 : oddCount 2435 13 = 6 ∧ acceleratedOrbit 13 2435 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2435 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2435) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2435.1, data_13_2435.2]

/-- Complete interval computation for depth 13, residue 2436. -/
theorem bounds_13_2436 : exactInterval 13 2436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2436 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2436) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2436 : oddCount 2436 13 = 6 ∧ acceleratedOrbit 13 2436 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2436 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2436) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2436.1, data_13_2436.2]

/-- Complete interval computation for depth 13, residue 2437. -/
theorem bounds_13_2437 : exactInterval 13 2437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2437 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2437) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2437 : oddCount 2437 13 = 6 ∧ acceleratedOrbit 13 2437 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2437 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2437) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2437.1, data_13_2437.2]

/-- Complete interval computation for depth 13, residue 2438. -/
theorem bounds_13_2438 : exactInterval 13 2438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2438 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2438) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2438 : oddCount 2438 13 = 6 ∧ acceleratedOrbit 13 2438 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2438 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2438) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2438.1, data_13_2438.2]

/-- Complete interval computation for depth 13, residue 2439. -/
theorem bounds_13_2439 : exactInterval 13 2439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2439 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2439) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2439 : oddCount 2439 13 = 6 ∧ acceleratedOrbit 13 2439 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2439 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2439) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2439.1, data_13_2439.2]

/-- Complete interval computation for depth 13, residue 2440. -/
theorem bounds_13_2440 : exactInterval 13 2440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2440 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2440) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2440 : oddCount 2440 13 = 5 ∧ acceleratedOrbit 13 2440 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2440 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2440) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2440.1, data_13_2440.2]

/-- Complete interval computation for depth 13, residue 2441. -/
theorem bounds_13_2441 : exactInterval 13 2441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2441 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2441) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2441 : oddCount 2441 13 = 8 ∧ acceleratedOrbit 13 2441 = 1957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2441 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2441) = 3 ^ 8 * m + 1957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2441.1, data_13_2441.2]

/-- Complete interval computation for depth 13, residue 2442. -/
theorem bounds_13_2442 : exactInterval 13 2442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2442 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2442) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2442 : oddCount 2442 13 = 5 ∧ acceleratedOrbit 13 2442 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2442 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2442) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2442.1, data_13_2442.2]

/-- Complete interval computation for depth 13, residue 2443. -/
theorem bounds_13_2443 : exactInterval 13 2443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2443 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2443) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2443 : oddCount 2443 13 = 7 ∧ acceleratedOrbit 13 2443 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2443 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2443) = 3 ^ 7 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2443.1, data_13_2443.2]

/-- Complete interval computation for depth 13, residue 2444. -/
theorem bounds_13_2444 : exactInterval 13 2444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2444 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2444) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2444 : oddCount 2444 13 = 5 ∧ acceleratedOrbit 13 2444 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2444 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2444) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2444.1, data_13_2444.2]

/-- Complete interval computation for depth 13, residue 2445. -/
theorem bounds_13_2445 : exactInterval 13 2445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2445 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2445) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2445 : oddCount 2445 13 = 5 ∧ acceleratedOrbit 13 2445 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2445 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2445) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2445.1, data_13_2445.2]

/-- Complete interval computation for depth 13, residue 2446. -/
theorem bounds_13_2446 : exactInterval 13 2446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2446 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2446) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2446 : oddCount 2446 13 = 6 ∧ acceleratedOrbit 13 2446 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2446 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2446) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2446.1, data_13_2446.2]

end Collatz.Research.StoppingAtlas.Batch0626
