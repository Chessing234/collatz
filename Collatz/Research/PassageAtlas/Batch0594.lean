import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0594

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19431. -/
theorem bounds_15_19431 : exactInterval 15 19431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19431 : oddCount 19431 15 = 7 ∧ acceleratedOrbit 15 19431 = 1297 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19431) = 3 ^ 7 * m + 1297 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19431.1, data_15_19431.2]

/-- Complete interval computation for depth 15, residue 19432. -/
theorem bounds_15_19432 : exactInterval 15 19432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19432 : oddCount 19432 15 = 6 ∧ acceleratedOrbit 15 19432 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19432) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19432.1, data_15_19432.2]

/-- Complete interval computation for depth 15, residue 19433. -/
theorem bounds_15_19433 : exactInterval 15 19433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19433 : oddCount 19433 15 = 11 ∧ acceleratedOrbit 15 19433 = 105067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19433) = 3 ^ 11 * m + 105067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19433.1, data_15_19433.2]

/-- Complete interval computation for depth 15, residue 19434. -/
theorem bounds_15_19434 : exactInterval 15 19434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19434 : oddCount 19434 15 = 6 ∧ acceleratedOrbit 15 19434 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19434) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19434.1, data_15_19434.2]

/-- Complete interval computation for depth 15, residue 19435. -/
theorem bounds_15_19435 : exactInterval 15 19435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19435 : oddCount 19435 15 = 8 ∧ acceleratedOrbit 15 19435 = 3892 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19435) = 3 ^ 8 * m + 3892 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19435.1, data_15_19435.2]

/-- Complete interval computation for depth 15, residue 19436. -/
theorem bounds_15_19436 : exactInterval 15 19436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19436 : oddCount 19436 15 = 8 ∧ acceleratedOrbit 15 19436 = 3893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19436) = 3 ^ 8 * m + 3893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19436.1, data_15_19436.2]

/-- Complete interval computation for depth 15, residue 19437. -/
theorem bounds_15_19437 : exactInterval 15 19437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19437 : oddCount 19437 15 = 8 ∧ acceleratedOrbit 15 19437 = 3893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19437) = 3 ^ 8 * m + 3893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19437.1, data_15_19437.2]

/-- Complete interval computation for depth 15, residue 19438. -/
theorem bounds_15_19438 : exactInterval 15 19438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19438 : oddCount 19438 15 = 8 ∧ acceleratedOrbit 15 19438 = 3893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19438) = 3 ^ 8 * m + 3893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19438.1, data_15_19438.2]

/-- Complete interval computation for depth 15, residue 19439. -/
theorem bounds_15_19439 : exactInterval 15 19439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19439 : oddCount 19439 15 = 11 ∧ acceleratedOrbit 15 19439 = 105097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19439) = 3 ^ 11 * m + 105097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19439.1, data_15_19439.2]

/-- Complete interval computation for depth 15, residue 19440. -/
theorem bounds_15_19440 : exactInterval 15 19440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19440 : oddCount 19440 15 = 8 ∧ acceleratedOrbit 15 19440 = 3896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19440) = 3 ^ 8 * m + 3896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19440.1, data_15_19440.2]

/-- Complete interval computation for depth 15, residue 19441. -/
theorem bounds_15_19441 : exactInterval 15 19441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19441 : oddCount 19441 15 = 6 ∧ acceleratedOrbit 15 19441 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19441) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19441.1, data_15_19441.2]

/-- Complete interval computation for depth 15, residue 19442. -/
theorem bounds_15_19442 : exactInterval 15 19442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19442 : oddCount 19442 15 = 7 ∧ acceleratedOrbit 15 19442 = 1298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19442) = 3 ^ 7 * m + 1298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19442.1, data_15_19442.2]

/-- Complete interval computation for depth 15, residue 19443. -/
theorem bounds_15_19443 : exactInterval 15 19443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19443 : oddCount 19443 15 = 7 ∧ acceleratedOrbit 15 19443 = 1298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19443) = 3 ^ 7 * m + 1298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19443.1, data_15_19443.2]

/-- Complete interval computation for depth 15, residue 19444. -/
theorem bounds_15_19444 : exactInterval 15 19444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19444 : oddCount 19444 15 = 8 ∧ acceleratedOrbit 15 19444 = 3896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19444) = 3 ^ 8 * m + 3896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19444.1, data_15_19444.2]

/-- Complete interval computation for depth 15, residue 19445. -/
theorem bounds_15_19445 : exactInterval 15 19445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19445 : oddCount 19445 15 = 8 ∧ acceleratedOrbit 15 19445 = 3896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19445) = 3 ^ 8 * m + 3896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19445.1, data_15_19445.2]

/-- Complete interval computation for depth 15, residue 19446. -/
theorem bounds_15_19446 : exactInterval 15 19446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19446 : oddCount 19446 15 = 9 ∧ acceleratedOrbit 15 19446 = 11684 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19446) = 3 ^ 9 * m + 11684 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19446.1, data_15_19446.2]

/-- Complete interval computation for depth 15, residue 19447. -/
theorem bounds_15_19447 : exactInterval 15 19447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19447 : oddCount 19447 15 = 9 ∧ acceleratedOrbit 15 19447 = 11684 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19447) = 3 ^ 9 * m + 11684 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19447.1, data_15_19447.2]

/-- Complete interval computation for depth 15, residue 19448. -/
theorem bounds_15_19448 : exactInterval 15 19448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19448 : oddCount 19448 15 = 8 ∧ acceleratedOrbit 15 19448 = 3896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19448) = 3 ^ 8 * m + 3896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19448.1, data_15_19448.2]

/-- Complete interval computation for depth 15, residue 19449. -/
theorem bounds_15_19449 : exactInterval 15 19449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19449 : oddCount 19449 15 = 11 ∧ acceleratedOrbit 15 19449 = 105158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19449) = 3 ^ 11 * m + 105158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19449.1, data_15_19449.2]

/-- Complete interval computation for depth 15, residue 19450. -/
theorem bounds_15_19450 : exactInterval 15 19450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19450 : oddCount 19450 15 = 8 ∧ acceleratedOrbit 15 19450 = 3896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19450) = 3 ^ 8 * m + 3896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19450.1, data_15_19450.2]

/-- Complete interval computation for depth 15, residue 19451. -/
theorem bounds_15_19451 : exactInterval 15 19451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19451 : oddCount 19451 15 = 8 ∧ acceleratedOrbit 15 19451 = 3895 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19451) = 3 ^ 8 * m + 3895 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19451.1, data_15_19451.2]

/-- Complete interval computation for depth 15, residue 19452. -/
theorem bounds_15_19452 : exactInterval 15 19452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19452 : oddCount 19452 15 = 11 ∧ acceleratedOrbit 15 19452 = 105182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19452) = 3 ^ 11 * m + 105182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19452.1, data_15_19452.2]

/-- Complete interval computation for depth 15, residue 19453. -/
theorem bounds_15_19453 : exactInterval 15 19453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19453 : oddCount 19453 15 = 11 ∧ acceleratedOrbit 15 19453 = 105182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19453) = 3 ^ 11 * m + 105182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19453.1, data_15_19453.2]

/-- Complete interval computation for depth 15, residue 19454. -/
theorem bounds_15_19454 : exactInterval 15 19454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19454 : oddCount 19454 15 = 11 ∧ acceleratedOrbit 15 19454 = 105182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19454) = 3 ^ 11 * m + 105182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19454.1, data_15_19454.2]

/-- Complete interval computation for depth 15, residue 19455. -/
theorem bounds_15_19455 : exactInterval 15 19455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19455 : oddCount 19455 15 = 11 ∧ acceleratedOrbit 15 19455 = 105181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19455) = 3 ^ 11 * m + 105181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19455.1, data_15_19455.2]

/-- Complete interval computation for depth 15, residue 19456. -/
theorem bounds_15_19456 : exactInterval 15 19456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19456 : oddCount 19456 15 = 3 ∧ acceleratedOrbit 15 19456 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19456) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19456.1, data_15_19456.2]

/-- Complete interval computation for depth 15, residue 19457. -/
theorem bounds_15_19457 : exactInterval 15 19457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19457 : oddCount 19457 15 = 6 ∧ acceleratedOrbit 15 19457 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19457) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19457.1, data_15_19457.2]

/-- Complete interval computation for depth 15, residue 19458. -/
theorem bounds_15_19458 : exactInterval 15 19458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19458 : oddCount 19458 15 = 8 ∧ acceleratedOrbit 15 19458 = 3898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19458) = 3 ^ 8 * m + 3898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19458.1, data_15_19458.2]

/-- Complete interval computation for depth 15, residue 19459. -/
theorem bounds_15_19459 : exactInterval 15 19459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19459 : oddCount 19459 15 = 8 ∧ acceleratedOrbit 15 19459 = 3898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19459) = 3 ^ 8 * m + 3898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19459.1, data_15_19459.2]

/-- Complete interval computation for depth 15, residue 19460. -/
theorem bounds_15_19460 : exactInterval 15 19460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19460 : oddCount 19460 15 = 6 ∧ acceleratedOrbit 15 19460 = 434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19460) = 3 ^ 6 * m + 434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19460.1, data_15_19460.2]

/-- Complete interval computation for depth 15, residue 19461. -/
theorem bounds_15_19461 : exactInterval 15 19461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19461 : oddCount 19461 15 = 6 ∧ acceleratedOrbit 15 19461 = 434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19461) = 3 ^ 6 * m + 434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19461.1, data_15_19461.2]

/-- Complete interval computation for depth 15, residue 19462. -/
theorem bounds_15_19462 : exactInterval 15 19462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19462 : oddCount 19462 15 = 6 ∧ acceleratedOrbit 15 19462 = 434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19462) = 3 ^ 6 * m + 434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19462.1, data_15_19462.2]

/-- Complete interval computation for depth 15, residue 19463. -/
theorem bounds_15_19463 : exactInterval 15 19463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19463 : oddCount 19463 15 = 8 ∧ acceleratedOrbit 15 19463 = 3898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19463) = 3 ^ 8 * m + 3898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19463.1, data_15_19463.2]

end Collatz.Research.PassageAtlas.Batch0594
