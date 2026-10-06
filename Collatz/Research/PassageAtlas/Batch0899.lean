import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0899

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29425. -/
theorem bounds_15_29425 : exactInterval 15 29425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29425 : oddCount 29425 15 = 4 ∧ acceleratedOrbit 15 29425 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29425) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29425.1, data_15_29425.2]

/-- Complete interval computation for depth 15, residue 29426. -/
theorem bounds_15_29426 : exactInterval 15 29426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29426 : oddCount 29426 15 = 11 ∧ acceleratedOrbit 15 29426 = 159104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29426) = 3 ^ 11 * m + 159104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29426.1, data_15_29426.2]

/-- Complete interval computation for depth 15, residue 29427. -/
theorem bounds_15_29427 : exactInterval 15 29427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29427 : oddCount 29427 15 = 11 ∧ acceleratedOrbit 15 29427 = 159104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29427) = 3 ^ 11 * m + 159104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29427.1, data_15_29427.2]

/-- Complete interval computation for depth 15, residue 29428. -/
theorem bounds_15_29428 : exactInterval 15 29428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29428 : oddCount 29428 15 = 6 ∧ acceleratedOrbit 15 29428 = 655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29428) = 3 ^ 6 * m + 655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29428.1, data_15_29428.2]

/-- Complete interval computation for depth 15, residue 29429. -/
theorem bounds_15_29429 : exactInterval 15 29429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29429 : oddCount 29429 15 = 6 ∧ acceleratedOrbit 15 29429 = 655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29429) = 3 ^ 6 * m + 655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29429.1, data_15_29429.2]

/-- Complete interval computation for depth 15, residue 29430. -/
theorem bounds_15_29430 : exactInterval 15 29430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29430 : oddCount 29430 15 = 8 ∧ acceleratedOrbit 15 29430 = 5894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29430) = 3 ^ 8 * m + 5894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29430.1, data_15_29430.2]

/-- Complete interval computation for depth 15, residue 29431. -/
theorem bounds_15_29431 : exactInterval 15 29431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29431 : oddCount 29431 15 = 8 ∧ acceleratedOrbit 15 29431 = 5894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29431) = 3 ^ 8 * m + 5894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29431.1, data_15_29431.2]

/-- Complete interval computation for depth 15, residue 29432. -/
theorem bounds_15_29432 : exactInterval 15 29432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29432 : oddCount 29432 15 = 6 ∧ acceleratedOrbit 15 29432 = 655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29432) = 3 ^ 6 * m + 655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29432.1, data_15_29432.2]

/-- Complete interval computation for depth 15, residue 29433. -/
theorem bounds_15_29433 : exactInterval 15 29433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29433 : oddCount 29433 15 = 9 ∧ acceleratedOrbit 15 29433 = 17684 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29433) = 3 ^ 9 * m + 17684 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29433.1, data_15_29433.2]

/-- Complete interval computation for depth 15, residue 29434. -/
theorem bounds_15_29434 : exactInterval 15 29434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29434 : oddCount 29434 15 = 6 ∧ acceleratedOrbit 15 29434 = 655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29434) = 3 ^ 6 * m + 655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29434.1, data_15_29434.2]

/-- Complete interval computation for depth 15, residue 29435. -/
theorem bounds_15_29435 : exactInterval 15 29435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29435 : oddCount 29435 15 = 8 ∧ acceleratedOrbit 15 29435 = 5894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29435) = 3 ^ 8 * m + 5894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29435.1, data_15_29435.2]

/-- Complete interval computation for depth 15, residue 29436. -/
theorem bounds_15_29436 : exactInterval 15 29436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29436 : oddCount 29436 15 = 10 ∧ acceleratedOrbit 15 29436 = 53054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29436) = 3 ^ 10 * m + 53054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29436.1, data_15_29436.2]

/-- Complete interval computation for depth 15, residue 29437. -/
theorem bounds_15_29437 : exactInterval 15 29437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29437 : oddCount 29437 15 = 10 ∧ acceleratedOrbit 15 29437 = 53054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29437) = 3 ^ 10 * m + 53054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29437.1, data_15_29437.2]

/-- Complete interval computation for depth 15, residue 29438. -/
theorem bounds_15_29438 : exactInterval 15 29438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29438 : oddCount 29438 15 = 10 ∧ acceleratedOrbit 15 29438 = 53054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29438) = 3 ^ 10 * m + 53054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29438.1, data_15_29438.2]

/-- Complete interval computation for depth 15, residue 29439. -/
theorem bounds_15_29439 : exactInterval 15 29439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29439 : oddCount 29439 15 = 13 ∧ acceleratedOrbit 15 29439 = 1432403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29439) = 3 ^ 13 * m + 1432403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29439.1, data_15_29439.2]

/-- Complete interval computation for depth 15, residue 29440. -/
theorem bounds_15_29440 : exactInterval 15 29440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29440 : oddCount 29440 15 = 4 ∧ acceleratedOrbit 15 29440 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29440) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29440.1, data_15_29440.2]

/-- Complete interval computation for depth 15, residue 29441. -/
theorem bounds_15_29441 : exactInterval 15 29441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29441 : oddCount 29441 15 = 7 ∧ acceleratedOrbit 15 29441 = 1966 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29441) = 3 ^ 7 * m + 1966 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29441.1, data_15_29441.2]

/-- Complete interval computation for depth 15, residue 29442. -/
theorem bounds_15_29442 : exactInterval 15 29442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29442 : oddCount 29442 15 = 7 ∧ acceleratedOrbit 15 29442 = 1966 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29442) = 3 ^ 7 * m + 1966 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29442.1, data_15_29442.2]

/-- Complete interval computation for depth 15, residue 29443. -/
theorem bounds_15_29443 : exactInterval 15 29443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29443 : oddCount 29443 15 = 7 ∧ acceleratedOrbit 15 29443 = 1966 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29443) = 3 ^ 7 * m + 1966 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29443.1, data_15_29443.2]

/-- Complete interval computation for depth 15, residue 29444. -/
theorem bounds_15_29444 : exactInterval 15 29444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29444 : oddCount 29444 15 = 6 ∧ acceleratedOrbit 15 29444 = 656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29444) = 3 ^ 6 * m + 656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29444.1, data_15_29444.2]

/-- Complete interval computation for depth 15, residue 29445. -/
theorem bounds_15_29445 : exactInterval 15 29445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29445 : oddCount 29445 15 = 6 ∧ acceleratedOrbit 15 29445 = 656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29445) = 3 ^ 6 * m + 656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29445.1, data_15_29445.2]

/-- Complete interval computation for depth 15, residue 29446. -/
theorem bounds_15_29446 : exactInterval 15 29446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29446 : oddCount 29446 15 = 6 ∧ acceleratedOrbit 15 29446 = 656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29446) = 3 ^ 6 * m + 656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29446.1, data_15_29446.2]

/-- Complete interval computation for depth 15, residue 29447. -/
theorem bounds_15_29447 : exactInterval 15 29447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29447 : oddCount 29447 15 = 8 ∧ acceleratedOrbit 15 29447 = 5897 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29447) = 3 ^ 8 * m + 5897 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29447.1, data_15_29447.2]

/-- Complete interval computation for depth 15, residue 29448. -/
theorem bounds_15_29448 : exactInterval 15 29448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29448 : oddCount 29448 15 = 6 ∧ acceleratedOrbit 15 29448 = 656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29448) = 3 ^ 6 * m + 656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29448.1, data_15_29448.2]

/-- Complete interval computation for depth 15, residue 29449. -/
theorem bounds_15_29449 : exactInterval 15 29449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29449 : oddCount 29449 15 = 8 ∧ acceleratedOrbit 15 29449 = 5897 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29449) = 3 ^ 8 * m + 5897 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29449.1, data_15_29449.2]

/-- Complete interval computation for depth 15, residue 29450. -/
theorem bounds_15_29450 : exactInterval 15 29450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29450 : oddCount 29450 15 = 6 ∧ acceleratedOrbit 15 29450 = 656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29450) = 3 ^ 6 * m + 656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29450.1, data_15_29450.2]

/-- Complete interval computation for depth 15, residue 29451. -/
theorem bounds_15_29451 : exactInterval 15 29451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29451 : oddCount 29451 15 = 10 ∧ acceleratedOrbit 15 29451 = 53081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29451) = 3 ^ 10 * m + 53081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29451.1, data_15_29451.2]

/-- Complete interval computation for depth 15, residue 29452. -/
theorem bounds_15_29452 : exactInterval 15 29452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29452 : oddCount 29452 15 = 6 ∧ acceleratedOrbit 15 29452 = 656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29452) = 3 ^ 6 * m + 656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29452.1, data_15_29452.2]

/-- Complete interval computation for depth 15, residue 29453. -/
theorem bounds_15_29453 : exactInterval 15 29453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29453 : oddCount 29453 15 = 6 ∧ acceleratedOrbit 15 29453 = 656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29453) = 3 ^ 6 * m + 656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29453.1, data_15_29453.2]

/-- Complete interval computation for depth 15, residue 29454. -/
theorem bounds_15_29454 : exactInterval 15 29454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29454 : oddCount 29454 15 = 6 ∧ acceleratedOrbit 15 29454 = 656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29454) = 3 ^ 6 * m + 656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29454.1, data_15_29454.2]

/-- Complete interval computation for depth 15, residue 29455. -/
theorem bounds_15_29455 : exactInterval 15 29455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29455 : oddCount 29455 15 = 6 ∧ acceleratedOrbit 15 29455 = 656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29455) = 3 ^ 6 * m + 656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29455.1, data_15_29455.2]

/-- Complete interval computation for depth 15, residue 29456. -/
theorem bounds_15_29456 : exactInterval 15 29456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29456 : oddCount 29456 15 = 4 ∧ acceleratedOrbit 15 29456 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29456) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29456.1, data_15_29456.2]

/-- Complete interval computation for depth 15, residue 29457. -/
theorem bounds_15_29457 : exactInterval 15 29457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29457 : oddCount 29457 15 = 6 ∧ acceleratedOrbit 15 29457 = 656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29457) = 3 ^ 6 * m + 656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29457.1, data_15_29457.2]

end Collatz.Research.PassageAtlas.Batch0899
