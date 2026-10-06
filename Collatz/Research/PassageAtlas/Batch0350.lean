import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0350

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11436. -/
theorem bounds_15_11436 : exactInterval 15 11436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11436 : oddCount 11436 15 = 8 ∧ acceleratedOrbit 15 11436 = 2294 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11436) = 3 ^ 8 * m + 2294 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11436.1, data_15_11436.2]

/-- Complete interval computation for depth 15, residue 11437. -/
theorem bounds_15_11437 : exactInterval 15 11437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11437 : oddCount 11437 15 = 8 ∧ acceleratedOrbit 15 11437 = 2294 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11437) = 3 ^ 8 * m + 2294 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11437.1, data_15_11437.2]

/-- Complete interval computation for depth 15, residue 11438. -/
theorem bounds_15_11438 : exactInterval 15 11438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11438 : oddCount 11438 15 = 8 ∧ acceleratedOrbit 15 11438 = 2294 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11438) = 3 ^ 8 * m + 2294 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11438.1, data_15_11438.2]

/-- Complete interval computation for depth 15, residue 11439. -/
theorem bounds_15_11439 : exactInterval 15 11439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11439 : oddCount 11439 15 = 10 ∧ acceleratedOrbit 15 11439 = 20618 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11439) = 3 ^ 10 * m + 20618 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11439.1, data_15_11439.2]

/-- Complete interval computation for depth 15, residue 11440. -/
theorem bounds_15_11440 : exactInterval 15 11440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11440 : oddCount 11440 15 = 6 ∧ acceleratedOrbit 15 11440 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11440) = 3 ^ 6 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11440.1, data_15_11440.2]

/-- Complete interval computation for depth 15, residue 11441. -/
theorem bounds_15_11441 : exactInterval 15 11441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11441 : oddCount 11441 15 = 8 ∧ acceleratedOrbit 15 11441 = 2294 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11441) = 3 ^ 8 * m + 2294 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11441.1, data_15_11441.2]

/-- Complete interval computation for depth 15, residue 11442. -/
theorem bounds_15_11442 : exactInterval 15 11442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11442 : oddCount 11442 15 = 8 ∧ acceleratedOrbit 15 11442 = 2294 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11442) = 3 ^ 8 * m + 2294 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11442.1, data_15_11442.2]

/-- Complete interval computation for depth 15, residue 11443. -/
theorem bounds_15_11443 : exactInterval 15 11443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11443 : oddCount 11443 15 = 8 ∧ acceleratedOrbit 15 11443 = 2294 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11443) = 3 ^ 8 * m + 2294 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11443.1, data_15_11443.2]

/-- Complete interval computation for depth 15, residue 11444. -/
theorem bounds_15_11444 : exactInterval 15 11444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11444 : oddCount 11444 15 = 6 ∧ acceleratedOrbit 15 11444 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11444) = 3 ^ 6 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11444.1, data_15_11444.2]

/-- Complete interval computation for depth 15, residue 11445. -/
theorem bounds_15_11445 : exactInterval 15 11445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11445 : oddCount 11445 15 = 6 ∧ acceleratedOrbit 15 11445 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11445) = 3 ^ 6 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11445.1, data_15_11445.2]

/-- Complete interval computation for depth 15, residue 11446. -/
theorem bounds_15_11446 : exactInterval 15 11446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11446 : oddCount 11446 15 = 9 ∧ acceleratedOrbit 15 11446 = 6878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11446) = 3 ^ 9 * m + 6878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11446.1, data_15_11446.2]

/-- Complete interval computation for depth 15, residue 11447. -/
theorem bounds_15_11447 : exactInterval 15 11447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11447 : oddCount 11447 15 = 9 ∧ acceleratedOrbit 15 11447 = 6878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11447) = 3 ^ 9 * m + 6878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11447.1, data_15_11447.2]

/-- Complete interval computation for depth 15, residue 11448. -/
theorem bounds_15_11448 : exactInterval 15 11448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11448 : oddCount 11448 15 = 6 ∧ acceleratedOrbit 15 11448 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11448) = 3 ^ 6 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11448.1, data_15_11448.2]

/-- Complete interval computation for depth 15, residue 11449. -/
theorem bounds_15_11449 : exactInterval 15 11449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11449 : oddCount 11449 15 = 9 ∧ acceleratedOrbit 15 11449 = 6880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11449) = 3 ^ 9 * m + 6880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11449.1, data_15_11449.2]

/-- Complete interval computation for depth 15, residue 11450. -/
theorem bounds_15_11450 : exactInterval 15 11450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11450 : oddCount 11450 15 = 6 ∧ acceleratedOrbit 15 11450 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11450) = 3 ^ 6 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11450.1, data_15_11450.2]

/-- Complete interval computation for depth 15, residue 11451. -/
theorem bounds_15_11451 : exactInterval 15 11451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11451 : oddCount 11451 15 = 9 ∧ acceleratedOrbit 15 11451 = 6880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11451) = 3 ^ 9 * m + 6880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11451.1, data_15_11451.2]

/-- Complete interval computation for depth 15, residue 11452. -/
theorem bounds_15_11452 : exactInterval 15 11452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11452 : oddCount 11452 15 = 9 ∧ acceleratedOrbit 15 11452 = 6884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11452) = 3 ^ 9 * m + 6884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11452.1, data_15_11452.2]

/-- Complete interval computation for depth 15, residue 11453. -/
theorem bounds_15_11453 : exactInterval 15 11453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11453 : oddCount 11453 15 = 9 ∧ acceleratedOrbit 15 11453 = 6884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11453) = 3 ^ 9 * m + 6884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11453.1, data_15_11453.2]

/-- Complete interval computation for depth 15, residue 11454. -/
theorem bounds_15_11454 : exactInterval 15 11454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11454 : oddCount 11454 15 = 9 ∧ acceleratedOrbit 15 11454 = 6884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11454) = 3 ^ 9 * m + 6884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11454.1, data_15_11454.2]

/-- Complete interval computation for depth 15, residue 11455. -/
theorem bounds_15_11455 : exactInterval 15 11455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11455 : oddCount 11455 15 = 10 ∧ acceleratedOrbit 15 11455 = 20645 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11455) = 3 ^ 10 * m + 20645 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11455.1, data_15_11455.2]

/-- Complete interval computation for depth 15, residue 11456. -/
theorem bounds_15_11456 : exactInterval 15 11456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11456 : oddCount 11456 15 = 4 ∧ acceleratedOrbit 15 11456 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11456) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11456.1, data_15_11456.2]

/-- Complete interval computation for depth 15, residue 11457. -/
theorem bounds_15_11457 : exactInterval 15 11457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11457 : oddCount 11457 15 = 5 ∧ acceleratedOrbit 15 11457 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11457) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11457.1, data_15_11457.2]

/-- Complete interval computation for depth 15, residue 11458. -/
theorem bounds_15_11458 : exactInterval 15 11458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11458 : oddCount 11458 15 = 5 ∧ acceleratedOrbit 15 11458 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11458) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11458.1, data_15_11458.2]

/-- Complete interval computation for depth 15, residue 11459. -/
theorem bounds_15_11459 : exactInterval 15 11459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11459 : oddCount 11459 15 = 5 ∧ acceleratedOrbit 15 11459 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11459) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11459.1, data_15_11459.2]

/-- Complete interval computation for depth 15, residue 11460. -/
theorem bounds_15_11460 : exactInterval 15 11460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11460 : oddCount 11460 15 = 6 ∧ acceleratedOrbit 15 11460 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11460) = 3 ^ 6 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11460.1, data_15_11460.2]

/-- Complete interval computation for depth 15, residue 11461. -/
theorem bounds_15_11461 : exactInterval 15 11461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11461 : oddCount 11461 15 = 6 ∧ acceleratedOrbit 15 11461 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11461) = 3 ^ 6 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11461.1, data_15_11461.2]

/-- Complete interval computation for depth 15, residue 11462. -/
theorem bounds_15_11462 : exactInterval 15 11462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11462 : oddCount 11462 15 = 6 ∧ acceleratedOrbit 15 11462 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11462) = 3 ^ 6 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11462.1, data_15_11462.2]

/-- Complete interval computation for depth 15, residue 11463. -/
theorem bounds_15_11463 : exactInterval 15 11463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11463 : oddCount 11463 15 = 8 ∧ acceleratedOrbit 15 11463 = 2296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11463) = 3 ^ 8 * m + 2296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11463.1, data_15_11463.2]

/-- Complete interval computation for depth 15, residue 11464. -/
theorem bounds_15_11464 : exactInterval 15 11464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11464 : oddCount 11464 15 = 6 ∧ acceleratedOrbit 15 11464 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11464) = 3 ^ 6 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11464.1, data_15_11464.2]

/-- Complete interval computation for depth 15, residue 11465. -/
theorem bounds_15_11465 : exactInterval 15 11465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11465 : oddCount 11465 15 = 7 ∧ acceleratedOrbit 15 11465 = 766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11465) = 3 ^ 7 * m + 766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11465.1, data_15_11465.2]

/-- Complete interval computation for depth 15, residue 11466. -/
theorem bounds_15_11466 : exactInterval 15 11466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11466 : oddCount 11466 15 = 6 ∧ acceleratedOrbit 15 11466 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11466) = 3 ^ 6 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11466.1, data_15_11466.2]

/-- Complete interval computation for depth 15, residue 11467. -/
theorem bounds_15_11467 : exactInterval 15 11467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11467 : oddCount 11467 15 = 7 ∧ acceleratedOrbit 15 11467 = 766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11467) = 3 ^ 7 * m + 766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11467.1, data_15_11467.2]

end Collatz.Research.PassageAtlas.Batch0350
