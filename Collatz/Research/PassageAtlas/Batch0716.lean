import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0716

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23429. -/
theorem bounds_15_23429 : exactInterval 15 23429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23429 : oddCount 23429 15 = 8 ∧ acceleratedOrbit 15 23429 = 4693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23429) = 3 ^ 8 * m + 4693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23429.1, data_15_23429.2]

/-- Complete interval computation for depth 15, residue 23430. -/
theorem bounds_15_23430 : exactInterval 15 23430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23430 : oddCount 23430 15 = 8 ∧ acceleratedOrbit 15 23430 = 4693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23430) = 3 ^ 8 * m + 4693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23430.1, data_15_23430.2]

/-- Complete interval computation for depth 15, residue 23431. -/
theorem bounds_15_23431 : exactInterval 15 23431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23431 : oddCount 23431 15 = 8 ∧ acceleratedOrbit 15 23431 = 4693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23431) = 3 ^ 8 * m + 4693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23431.1, data_15_23431.2]

/-- Complete interval computation for depth 15, residue 23432. -/
theorem bounds_15_23432 : exactInterval 15 23432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23432 : oddCount 23432 15 = 5 ∧ acceleratedOrbit 15 23432 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23432) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23432.1, data_15_23432.2]

/-- Complete interval computation for depth 15, residue 23433. -/
theorem bounds_15_23433 : exactInterval 15 23433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23433 : oddCount 23433 15 = 9 ∧ acceleratedOrbit 15 23433 = 14077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23433) = 3 ^ 9 * m + 14077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23433.1, data_15_23433.2]

/-- Complete interval computation for depth 15, residue 23434. -/
theorem bounds_15_23434 : exactInterval 15 23434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23434 : oddCount 23434 15 = 5 ∧ acceleratedOrbit 15 23434 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23434) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23434.1, data_15_23434.2]

/-- Complete interval computation for depth 15, residue 23435. -/
theorem bounds_15_23435 : exactInterval 15 23435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23435 : oddCount 23435 15 = 11 ∧ acceleratedOrbit 15 23435 = 126710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23435) = 3 ^ 11 * m + 126710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23435.1, data_15_23435.2]

/-- Complete interval computation for depth 15, residue 23436. -/
theorem bounds_15_23436 : exactInterval 15 23436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23436 : oddCount 23436 15 = 5 ∧ acceleratedOrbit 15 23436 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23436) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23436.1, data_15_23436.2]

/-- Complete interval computation for depth 15, residue 23437. -/
theorem bounds_15_23437 : exactInterval 15 23437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23437 : oddCount 23437 15 = 5 ∧ acceleratedOrbit 15 23437 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23437) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23437.1, data_15_23437.2]

/-- Complete interval computation for depth 15, residue 23438. -/
theorem bounds_15_23438 : exactInterval 15 23438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23438 : oddCount 23438 15 = 7 ∧ acceleratedOrbit 15 23438 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23438) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23438.1, data_15_23438.2]

/-- Complete interval computation for depth 15, residue 23439. -/
theorem bounds_15_23439 : exactInterval 15 23439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23439 : oddCount 23439 15 = 7 ∧ acceleratedOrbit 15 23439 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23439) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23439.1, data_15_23439.2]

/-- Complete interval computation for depth 15, residue 23440. -/
theorem bounds_15_23440 : exactInterval 15 23440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23440 : oddCount 23440 15 = 4 ∧ acceleratedOrbit 15 23440 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23440) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23440.1, data_15_23440.2]

/-- Complete interval computation for depth 15, residue 23441. -/
theorem bounds_15_23441 : exactInterval 15 23441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23441 : oddCount 23441 15 = 8 ∧ acceleratedOrbit 15 23441 = 4697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23441) = 3 ^ 8 * m + 4697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23441.1, data_15_23441.2]

/-- Complete interval computation for depth 15, residue 23442. -/
theorem bounds_15_23442 : exactInterval 15 23442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23442 : oddCount 23442 15 = 8 ∧ acceleratedOrbit 15 23442 = 4697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23442) = 3 ^ 8 * m + 4697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23442.1, data_15_23442.2]

/-- Complete interval computation for depth 15, residue 23443. -/
theorem bounds_15_23443 : exactInterval 15 23443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23443 : oddCount 23443 15 = 8 ∧ acceleratedOrbit 15 23443 = 4697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23443) = 3 ^ 8 * m + 4697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23443.1, data_15_23443.2]

/-- Complete interval computation for depth 15, residue 23444. -/
theorem bounds_15_23444 : exactInterval 15 23444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23444 : oddCount 23444 15 = 4 ∧ acceleratedOrbit 15 23444 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23444) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23444.1, data_15_23444.2]

/-- Complete interval computation for depth 15, residue 23445. -/
theorem bounds_15_23445 : exactInterval 15 23445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23445 : oddCount 23445 15 = 4 ∧ acceleratedOrbit 15 23445 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23445) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23445.1, data_15_23445.2]

/-- Complete interval computation for depth 15, residue 23446. -/
theorem bounds_15_23446 : exactInterval 15 23446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23446 : oddCount 23446 15 = 9 ∧ acceleratedOrbit 15 23446 = 14093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23446) = 3 ^ 9 * m + 14093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23446.1, data_15_23446.2]

/-- Complete interval computation for depth 15, residue 23447. -/
theorem bounds_15_23447 : exactInterval 15 23447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23447 : oddCount 23447 15 = 9 ∧ acceleratedOrbit 15 23447 = 14093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23447) = 3 ^ 9 * m + 14093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23447.1, data_15_23447.2]

/-- Complete interval computation for depth 15, residue 23448. -/
theorem bounds_15_23448 : exactInterval 15 23448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23448 : oddCount 23448 15 = 4 ∧ acceleratedOrbit 15 23448 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23448) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23448.1, data_15_23448.2]

/-- Complete interval computation for depth 15, residue 23449. -/
theorem bounds_15_23449 : exactInterval 15 23449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23449 : oddCount 23449 15 = 9 ∧ acceleratedOrbit 15 23449 = 14093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23449) = 3 ^ 9 * m + 14093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23449.1, data_15_23449.2]

/-- Complete interval computation for depth 15, residue 23450. -/
theorem bounds_15_23450 : exactInterval 15 23450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23450 : oddCount 23450 15 = 4 ∧ acceleratedOrbit 15 23450 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23450) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23450.1, data_15_23450.2]

/-- Complete interval computation for depth 15, residue 23451. -/
theorem bounds_15_23451 : exactInterval 15 23451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23451 : oddCount 23451 15 = 8 ∧ acceleratedOrbit 15 23451 = 4697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23451) = 3 ^ 8 * m + 4697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23451.1, data_15_23451.2]

/-- Complete interval computation for depth 15, residue 23452. -/
theorem bounds_15_23452 : exactInterval 15 23452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23452 : oddCount 23452 15 = 10 ∧ acceleratedOrbit 15 23452 = 42272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23452) = 3 ^ 10 * m + 42272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23452.1, data_15_23452.2]

/-- Complete interval computation for depth 15, residue 23453. -/
theorem bounds_15_23453 : exactInterval 15 23453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23453 : oddCount 23453 15 = 10 ∧ acceleratedOrbit 15 23453 = 42272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23453) = 3 ^ 10 * m + 42272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23453.1, data_15_23453.2]

/-- Complete interval computation for depth 15, residue 23454. -/
theorem bounds_15_23454 : exactInterval 15 23454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23454 : oddCount 23454 15 = 10 ∧ acceleratedOrbit 15 23454 = 42272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23454) = 3 ^ 10 * m + 42272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23454.1, data_15_23454.2]

/-- Complete interval computation for depth 15, residue 23455. -/
theorem bounds_15_23455 : exactInterval 15 23455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23455 : oddCount 23455 15 = 8 ∧ acceleratedOrbit 15 23455 = 4697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23455) = 3 ^ 8 * m + 4697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23455.1, data_15_23455.2]

/-- Complete interval computation for depth 15, residue 23456. -/
theorem bounds_15_23456 : exactInterval 15 23456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23456 : oddCount 23456 15 = 5 ∧ acceleratedOrbit 15 23456 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23456) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23456.1, data_15_23456.2]

/-- Complete interval computation for depth 15, residue 23457. -/
theorem bounds_15_23457 : exactInterval 15 23457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23457 : oddCount 23457 15 = 10 ∧ acceleratedOrbit 15 23457 = 42281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23457) = 3 ^ 10 * m + 42281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23457.1, data_15_23457.2]

/-- Complete interval computation for depth 15, residue 23458. -/
theorem bounds_15_23458 : exactInterval 15 23458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23458 : oddCount 23458 15 = 4 ∧ acceleratedOrbit 15 23458 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23458) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23458.1, data_15_23458.2]

/-- Complete interval computation for depth 15, residue 23459. -/
theorem bounds_15_23459 : exactInterval 15 23459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23459 : oddCount 23459 15 = 4 ∧ acceleratedOrbit 15 23459 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23459) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23459.1, data_15_23459.2]

/-- Complete interval computation for depth 15, residue 23460. -/
theorem bounds_15_23460 : exactInterval 15 23460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23460 : oddCount 23460 15 = 8 ∧ acceleratedOrbit 15 23460 = 4699 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23460) = 3 ^ 8 * m + 4699 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23460.1, data_15_23460.2]

end Collatz.Research.PassageAtlas.Batch0716
