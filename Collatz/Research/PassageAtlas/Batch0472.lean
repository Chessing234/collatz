import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0472

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15433. -/
theorem bounds_15_15433 : exactInterval 15 15433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15433 : oddCount 15433 15 = 9 ∧ acceleratedOrbit 15 15433 = 9272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15433) = 3 ^ 9 * m + 9272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15433.1, data_15_15433.2]

/-- Complete interval computation for depth 15, residue 15434. -/
theorem bounds_15_15434 : exactInterval 15 15434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15434 : oddCount 15434 15 = 7 ∧ acceleratedOrbit 15 15434 = 1031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15434) = 3 ^ 7 * m + 1031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15434.1, data_15_15434.2]

/-- Complete interval computation for depth 15, residue 15435. -/
theorem bounds_15_15435 : exactInterval 15 15435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15435 : oddCount 15435 15 = 6 ∧ acceleratedOrbit 15 15435 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15435) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15435.1, data_15_15435.2]

/-- Complete interval computation for depth 15, residue 15436. -/
theorem bounds_15_15436 : exactInterval 15 15436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15436 : oddCount 15436 15 = 7 ∧ acceleratedOrbit 15 15436 = 1031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15436) = 3 ^ 7 * m + 1031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15436.1, data_15_15436.2]

/-- Complete interval computation for depth 15, residue 15437. -/
theorem bounds_15_15437 : exactInterval 15 15437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15437 : oddCount 15437 15 = 7 ∧ acceleratedOrbit 15 15437 = 1031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15437) = 3 ^ 7 * m + 1031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15437.1, data_15_15437.2]

/-- Complete interval computation for depth 15, residue 15438. -/
theorem bounds_15_15438 : exactInterval 15 15438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15438 : oddCount 15438 15 = 6 ∧ acceleratedOrbit 15 15438 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15438) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15438.1, data_15_15438.2]

/-- Complete interval computation for depth 15, residue 15439. -/
theorem bounds_15_15439 : exactInterval 15 15439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15439 : oddCount 15439 15 = 6 ∧ acceleratedOrbit 15 15439 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15439) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15439.1, data_15_15439.2]

/-- Complete interval computation for depth 15, residue 15440. -/
theorem bounds_15_15440 : exactInterval 15 15440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15440 : oddCount 15440 15 = 3 ∧ acceleratedOrbit 15 15440 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15440) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15440.1, data_15_15440.2]

/-- Complete interval computation for depth 15, residue 15441. -/
theorem bounds_15_15441 : exactInterval 15 15441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15441 : oddCount 15441 15 = 7 ∧ acceleratedOrbit 15 15441 = 1031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15441) = 3 ^ 7 * m + 1031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15441.1, data_15_15441.2]

/-- Complete interval computation for depth 15, residue 15442. -/
theorem bounds_15_15442 : exactInterval 15 15442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15442 : oddCount 15442 15 = 11 ∧ acceleratedOrbit 15 15442 = 83501 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15442) = 3 ^ 11 * m + 83501 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15442.1, data_15_15442.2]

/-- Complete interval computation for depth 15, residue 15443. -/
theorem bounds_15_15443 : exactInterval 15 15443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15443 : oddCount 15443 15 = 11 ∧ acceleratedOrbit 15 15443 = 83501 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15443) = 3 ^ 11 * m + 83501 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15443.1, data_15_15443.2]

/-- Complete interval computation for depth 15, residue 15444. -/
theorem bounds_15_15444 : exactInterval 15 15444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15444 : oddCount 15444 15 = 3 ∧ acceleratedOrbit 15 15444 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15444) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15444.1, data_15_15444.2]

/-- Complete interval computation for depth 15, residue 15445. -/
theorem bounds_15_15445 : exactInterval 15 15445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15445 : oddCount 15445 15 = 3 ∧ acceleratedOrbit 15 15445 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15445) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15445.1, data_15_15445.2]

/-- Complete interval computation for depth 15, residue 15446. -/
theorem bounds_15_15446 : exactInterval 15 15446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15446 : oddCount 15446 15 = 6 ∧ acceleratedOrbit 15 15446 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15446) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15446.1, data_15_15446.2]

/-- Complete interval computation for depth 15, residue 15447. -/
theorem bounds_15_15447 : exactInterval 15 15447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15447 : oddCount 15447 15 = 6 ∧ acceleratedOrbit 15 15447 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15447) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15447.1, data_15_15447.2]

/-- Complete interval computation for depth 15, residue 15448. -/
theorem bounds_15_15448 : exactInterval 15 15448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15448 : oddCount 15448 15 = 8 ∧ acceleratedOrbit 15 15448 = 3098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15448) = 3 ^ 8 * m + 3098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15448.1, data_15_15448.2]

/-- Complete interval computation for depth 15, residue 15449. -/
theorem bounds_15_15449 : exactInterval 15 15449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15449 : oddCount 15449 15 = 8 ∧ acceleratedOrbit 15 15449 = 3095 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15449) = 3 ^ 8 * m + 3095 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15449.1, data_15_15449.2]

/-- Complete interval computation for depth 15, residue 15450. -/
theorem bounds_15_15450 : exactInterval 15 15450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15450 : oddCount 15450 15 = 8 ∧ acceleratedOrbit 15 15450 = 3098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15450) = 3 ^ 8 * m + 3098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15450.1, data_15_15450.2]

/-- Complete interval computation for depth 15, residue 15451. -/
theorem bounds_15_15451 : exactInterval 15 15451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15451 : oddCount 15451 15 = 8 ∧ acceleratedOrbit 15 15451 = 3094 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15451) = 3 ^ 8 * m + 3094 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15451.1, data_15_15451.2]

/-- Complete interval computation for depth 15, residue 15452. -/
theorem bounds_15_15452 : exactInterval 15 15452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15452 : oddCount 15452 15 = 8 ∧ acceleratedOrbit 15 15452 = 3098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15452) = 3 ^ 8 * m + 3098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15452.1, data_15_15452.2]

/-- Complete interval computation for depth 15, residue 15453. -/
theorem bounds_15_15453 : exactInterval 15 15453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15453 : oddCount 15453 15 = 8 ∧ acceleratedOrbit 15 15453 = 3098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15453) = 3 ^ 8 * m + 3098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15453.1, data_15_15453.2]

/-- Complete interval computation for depth 15, residue 15454. -/
theorem bounds_15_15454 : exactInterval 15 15454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15454 : oddCount 15454 15 = 10 ∧ acceleratedOrbit 15 15454 = 27854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15454) = 3 ^ 10 * m + 27854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15454.1, data_15_15454.2]

/-- Complete interval computation for depth 15, residue 15455. -/
theorem bounds_15_15455 : exactInterval 15 15455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15455 : oddCount 15455 15 = 10 ∧ acceleratedOrbit 15 15455 = 27854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15455) = 3 ^ 10 * m + 27854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15455.1, data_15_15455.2]

/-- Complete interval computation for depth 15, residue 15456. -/
theorem bounds_15_15456 : exactInterval 15 15456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15456 : oddCount 15456 15 = 3 ∧ acceleratedOrbit 15 15456 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15456) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15456.1, data_15_15456.2]

/-- Complete interval computation for depth 15, residue 15457. -/
theorem bounds_15_15457 : exactInterval 15 15457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15457 : oddCount 15457 15 = 10 ∧ acceleratedOrbit 15 15457 = 27863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15457) = 3 ^ 10 * m + 27863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15457.1, data_15_15457.2]

/-- Complete interval computation for depth 15, residue 15458. -/
theorem bounds_15_15458 : exactInterval 15 15458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15458 : oddCount 15458 15 = 8 ∧ acceleratedOrbit 15 15458 = 3098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15458) = 3 ^ 8 * m + 3098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15458.1, data_15_15458.2]

/-- Complete interval computation for depth 15, residue 15459. -/
theorem bounds_15_15459 : exactInterval 15 15459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15459 : oddCount 15459 15 = 8 ∧ acceleratedOrbit 15 15459 = 3098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15459) = 3 ^ 8 * m + 3098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15459.1, data_15_15459.2]

/-- Complete interval computation for depth 15, residue 15460. -/
theorem bounds_15_15460 : exactInterval 15 15460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15460 : oddCount 15460 15 = 8 ∧ acceleratedOrbit 15 15460 = 3098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15460) = 3 ^ 8 * m + 3098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15460.1, data_15_15460.2]

/-- Complete interval computation for depth 15, residue 15461. -/
theorem bounds_15_15461 : exactInterval 15 15461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15461 : oddCount 15461 15 = 8 ∧ acceleratedOrbit 15 15461 = 3098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15461) = 3 ^ 8 * m + 3098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15461.1, data_15_15461.2]

/-- Complete interval computation for depth 15, residue 15462. -/
theorem bounds_15_15462 : exactInterval 15 15462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15462 : oddCount 15462 15 = 8 ∧ acceleratedOrbit 15 15462 = 3098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15462) = 3 ^ 8 * m + 3098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15462.1, data_15_15462.2]

/-- Complete interval computation for depth 15, residue 15463. -/
theorem bounds_15_15463 : exactInterval 15 15463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15463 : oddCount 15463 15 = 11 ∧ acceleratedOrbit 15 15463 = 83602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15463) = 3 ^ 11 * m + 83602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15463.1, data_15_15463.2]

/-- Complete interval computation for depth 15, residue 15464. -/
theorem bounds_15_15464 : exactInterval 15 15464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15464 : oddCount 15464 15 = 3 ∧ acceleratedOrbit 15 15464 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15464) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15464.1, data_15_15464.2]

/-- Complete interval computation for depth 15, residue 15465. -/
theorem bounds_15_15465 : exactInterval 15 15465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15465 : oddCount 15465 15 = 8 ∧ acceleratedOrbit 15 15465 = 3097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15465) = 3 ^ 8 * m + 3097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15465.1, data_15_15465.2]

end Collatz.Research.PassageAtlas.Batch0472
