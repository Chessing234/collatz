import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0075

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2424. -/
theorem bounds_15_2424 : exactInterval 15 2424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2424 : oddCount 2424 15 = 8 ∧ acceleratedOrbit 15 2424 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2424) = 3 ^ 8 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2424.1, data_15_2424.2]

/-- Complete interval computation for depth 15, residue 2425. -/
theorem bounds_15_2425 : exactInterval 15 2425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2425 : oddCount 2425 15 = 13 ∧ acceleratedOrbit 15 2425 = 118097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2425) = 3 ^ 13 * m + 118097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2425.1, data_15_2425.2]

/-- Complete interval computation for depth 15, residue 2426. -/
theorem bounds_15_2426 : exactInterval 15 2426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2426 : oddCount 2426 15 = 8 ∧ acceleratedOrbit 15 2426 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2426) = 3 ^ 8 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2426.1, data_15_2426.2]

/-- Complete interval computation for depth 15, residue 2427. -/
theorem bounds_15_2427 : exactInterval 15 2427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2427 : oddCount 2427 15 = 9 ∧ acceleratedOrbit 15 2427 = 1460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2427) = 3 ^ 9 * m + 1460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2427.1, data_15_2427.2]

/-- Complete interval computation for depth 15, residue 2428. -/
theorem bounds_15_2428 : exactInterval 15 2428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2428 : oddCount 2428 15 = 8 ∧ acceleratedOrbit 15 2428 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2428) = 3 ^ 8 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2428.1, data_15_2428.2]

/-- Complete interval computation for depth 15, residue 2429. -/
theorem bounds_15_2429 : exactInterval 15 2429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2429 : oddCount 2429 15 = 8 ∧ acceleratedOrbit 15 2429 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2429) = 3 ^ 8 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2429.1, data_15_2429.2]

/-- Complete interval computation for depth 15, residue 2430. -/
theorem bounds_15_2430 : exactInterval 15 2430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2430 : oddCount 2430 15 = 8 ∧ acceleratedOrbit 15 2430 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2430) = 3 ^ 8 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2430.1, data_15_2430.2]

/-- Complete interval computation for depth 15, residue 2431. -/
theorem bounds_15_2431 : exactInterval 15 2431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2431 : oddCount 2431 15 = 8 ∧ acceleratedOrbit 15 2431 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2431) = 3 ^ 8 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2431.1, data_15_2431.2]

/-- Complete interval computation for depth 15, residue 2432. -/
theorem bounds_15_2432 : exactInterval 15 2432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2432 : oddCount 2432 15 = 5 ∧ acceleratedOrbit 15 2432 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2432) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2432.1, data_15_2432.2]

/-- Complete interval computation for depth 15, residue 2433. -/
theorem bounds_15_2433 : exactInterval 15 2433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2433 : oddCount 2433 15 = 7 ∧ acceleratedOrbit 15 2433 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2433) = 3 ^ 7 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2433.1, data_15_2433.2]

/-- Complete interval computation for depth 15, residue 2434. -/
theorem bounds_15_2434 : exactInterval 15 2434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2434 : oddCount 2434 15 = 7 ∧ acceleratedOrbit 15 2434 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2434) = 3 ^ 7 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2434.1, data_15_2434.2]

/-- Complete interval computation for depth 15, residue 2435. -/
theorem bounds_15_2435 : exactInterval 15 2435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2435 : oddCount 2435 15 = 7 ∧ acceleratedOrbit 15 2435 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2435) = 3 ^ 7 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2435.1, data_15_2435.2]

/-- Complete interval computation for depth 15, residue 2436. -/
theorem bounds_15_2436 : exactInterval 15 2436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2436 : oddCount 2436 15 = 7 ∧ acceleratedOrbit 15 2436 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2436) = 3 ^ 7 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2436.1, data_15_2436.2]

/-- Complete interval computation for depth 15, residue 2437. -/
theorem bounds_15_2437 : exactInterval 15 2437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2437 : oddCount 2437 15 = 7 ∧ acceleratedOrbit 15 2437 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2437) = 3 ^ 7 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2437.1, data_15_2437.2]

/-- Complete interval computation for depth 15, residue 2438. -/
theorem bounds_15_2438 : exactInterval 15 2438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2438 : oddCount 2438 15 = 7 ∧ acceleratedOrbit 15 2438 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2438) = 3 ^ 7 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2438.1, data_15_2438.2]

/-- Complete interval computation for depth 15, residue 2439. -/
theorem bounds_15_2439 : exactInterval 15 2439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2439 : oddCount 2439 15 = 7 ∧ acceleratedOrbit 15 2439 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2439) = 3 ^ 7 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2439.1, data_15_2439.2]

/-- Complete interval computation for depth 15, residue 2440. -/
theorem bounds_15_2440 : exactInterval 15 2440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2440 : oddCount 2440 15 = 6 ∧ acceleratedOrbit 15 2440 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2440) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2440.1, data_15_2440.2]

/-- Complete interval computation for depth 15, residue 2441. -/
theorem bounds_15_2441 : exactInterval 15 2441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2441 : oddCount 2441 15 = 9 ∧ acceleratedOrbit 15 2441 = 1468 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2441) = 3 ^ 9 * m + 1468 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2441.1, data_15_2441.2]

/-- Complete interval computation for depth 15, residue 2442. -/
theorem bounds_15_2442 : exactInterval 15 2442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2442 : oddCount 2442 15 = 6 ∧ acceleratedOrbit 15 2442 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2442) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2442.1, data_15_2442.2]

/-- Complete interval computation for depth 15, residue 2443. -/
theorem bounds_15_2443 : exactInterval 15 2443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2443 : oddCount 2443 15 = 8 ∧ acceleratedOrbit 15 2443 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2443) = 3 ^ 8 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2443.1, data_15_2443.2]

/-- Complete interval computation for depth 15, residue 2444. -/
theorem bounds_15_2444 : exactInterval 15 2444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2444 : oddCount 2444 15 = 6 ∧ acceleratedOrbit 15 2444 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2444) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2444.1, data_15_2444.2]

/-- Complete interval computation for depth 15, residue 2445. -/
theorem bounds_15_2445 : exactInterval 15 2445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2445 : oddCount 2445 15 = 6 ∧ acceleratedOrbit 15 2445 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2445) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2445.1, data_15_2445.2]

/-- Complete interval computation for depth 15, residue 2446. -/
theorem bounds_15_2446 : exactInterval 15 2446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2446 : oddCount 2446 15 = 7 ∧ acceleratedOrbit 15 2446 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2446) = 3 ^ 7 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2446.1, data_15_2446.2]

/-- Complete interval computation for depth 15, residue 2447. -/
theorem bounds_15_2447 : exactInterval 15 2447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2447 : oddCount 2447 15 = 7 ∧ acceleratedOrbit 15 2447 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2447) = 3 ^ 7 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2447.1, data_15_2447.2]

/-- Complete interval computation for depth 15, residue 2448. -/
theorem bounds_15_2448 : exactInterval 15 2448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2448 : oddCount 2448 15 = 6 ∧ acceleratedOrbit 15 2448 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2448) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2448.1, data_15_2448.2]

/-- Complete interval computation for depth 15, residue 2449. -/
theorem bounds_15_2449 : exactInterval 15 2449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2449 : oddCount 2449 15 = 6 ∧ acceleratedOrbit 15 2449 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2449) = 3 ^ 6 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2449.1, data_15_2449.2]

/-- Complete interval computation for depth 15, residue 2450. -/
theorem bounds_15_2450 : exactInterval 15 2450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2450 : oddCount 2450 15 = 6 ∧ acceleratedOrbit 15 2450 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2450) = 3 ^ 6 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2450.1, data_15_2450.2]

/-- Complete interval computation for depth 15, residue 2451. -/
theorem bounds_15_2451 : exactInterval 15 2451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2451 : oddCount 2451 15 = 6 ∧ acceleratedOrbit 15 2451 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2451) = 3 ^ 6 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2451.1, data_15_2451.2]

/-- Complete interval computation for depth 15, residue 2452. -/
theorem bounds_15_2452 : exactInterval 15 2452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2452 : oddCount 2452 15 = 6 ∧ acceleratedOrbit 15 2452 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2452) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2452.1, data_15_2452.2]

/-- Complete interval computation for depth 15, residue 2453. -/
theorem bounds_15_2453 : exactInterval 15 2453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2453 : oddCount 2453 15 = 6 ∧ acceleratedOrbit 15 2453 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2453) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2453.1, data_15_2453.2]

/-- Complete interval computation for depth 15, residue 2454. -/
theorem bounds_15_2454 : exactInterval 15 2454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2454 : oddCount 2454 15 = 6 ∧ acceleratedOrbit 15 2454 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2454) = 3 ^ 6 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2454.1, data_15_2454.2]

/-- Complete interval computation for depth 15, residue 2455. -/
theorem bounds_15_2455 : exactInterval 15 2455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2455 : oddCount 2455 15 = 6 ∧ acceleratedOrbit 15 2455 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2455) = 3 ^ 6 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2455.1, data_15_2455.2]

/-- Complete interval computation for depth 15, residue 2456. -/
theorem bounds_15_2456 : exactInterval 15 2456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2456 : oddCount 2456 15 = 6 ∧ acceleratedOrbit 15 2456 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2456) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2456.1, data_15_2456.2]

end Collatz.Research.PassageAtlas.Batch0075
