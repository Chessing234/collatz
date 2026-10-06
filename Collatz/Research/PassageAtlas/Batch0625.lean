import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0625

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20447. -/
theorem bounds_15_20447 : exactInterval 15 20447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20447 : oddCount 20447 15 = 9 ∧ acceleratedOrbit 15 20447 = 12284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20447) = 3 ^ 9 * m + 12284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20447.1, data_15_20447.2]

/-- Complete interval computation for depth 15, residue 20448. -/
theorem bounds_15_20448 : exactInterval 15 20448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20448 : oddCount 20448 15 = 9 ∧ acceleratedOrbit 15 20448 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20448) = 3 ^ 9 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20448.1, data_15_20448.2]

/-- Complete interval computation for depth 15, residue 20449. -/
theorem bounds_15_20449 : exactInterval 15 20449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20449 : oddCount 20449 15 = 12 ∧ acceleratedOrbit 15 20449 = 331694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20449) = 3 ^ 12 * m + 331694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20449.1, data_15_20449.2]

/-- Complete interval computation for depth 15, residue 20450. -/
theorem bounds_15_20450 : exactInterval 15 20450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20450 : oddCount 20450 15 = 7 ∧ acceleratedOrbit 15 20450 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20450) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20450.1, data_15_20450.2]

/-- Complete interval computation for depth 15, residue 20451. -/
theorem bounds_15_20451 : exactInterval 15 20451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20451 : oddCount 20451 15 = 7 ∧ acceleratedOrbit 15 20451 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20451) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20451.1, data_15_20451.2]

/-- Complete interval computation for depth 15, residue 20452. -/
theorem bounds_15_20452 : exactInterval 15 20452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20452 : oddCount 20452 15 = 8 ∧ acceleratedOrbit 15 20452 = 4097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20452) = 3 ^ 8 * m + 4097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20452.1, data_15_20452.2]

/-- Complete interval computation for depth 15, residue 20453. -/
theorem bounds_15_20453 : exactInterval 15 20453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20453 : oddCount 20453 15 = 8 ∧ acceleratedOrbit 15 20453 = 4097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20453) = 3 ^ 8 * m + 4097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20453.1, data_15_20453.2]

/-- Complete interval computation for depth 15, residue 20454. -/
theorem bounds_15_20454 : exactInterval 15 20454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20454 : oddCount 20454 15 = 8 ∧ acceleratedOrbit 15 20454 = 4097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20454) = 3 ^ 8 * m + 4097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20454.1, data_15_20454.2]

/-- Complete interval computation for depth 15, residue 20455. -/
theorem bounds_15_20455 : exactInterval 15 20455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20455 : oddCount 20455 15 = 8 ∧ acceleratedOrbit 15 20455 = 4096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20455) = 3 ^ 8 * m + 4096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20455.1, data_15_20455.2]

/-- Complete interval computation for depth 15, residue 20456. -/
theorem bounds_15_20456 : exactInterval 15 20456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20456 : oddCount 20456 15 = 9 ∧ acceleratedOrbit 15 20456 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20456) = 3 ^ 9 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20456.1, data_15_20456.2]

/-- Complete interval computation for depth 15, residue 20457. -/
theorem bounds_15_20457 : exactInterval 15 20457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20457 : oddCount 20457 15 = 10 ∧ acceleratedOrbit 15 20457 = 36868 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20457) = 3 ^ 10 * m + 36868 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20457.1, data_15_20457.2]

/-- Complete interval computation for depth 15, residue 20458. -/
theorem bounds_15_20458 : exactInterval 15 20458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20458 : oddCount 20458 15 = 9 ∧ acceleratedOrbit 15 20458 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20458) = 3 ^ 9 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20458.1, data_15_20458.2]

/-- Complete interval computation for depth 15, residue 20459. -/
theorem bounds_15_20459 : exactInterval 15 20459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20459 : oddCount 20459 15 = 10 ∧ acceleratedOrbit 15 20459 = 36872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20459) = 3 ^ 10 * m + 36872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20459.1, data_15_20459.2]

/-- Complete interval computation for depth 15, residue 20460. -/
theorem bounds_15_20460 : exactInterval 15 20460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20460 : oddCount 20460 15 = 7 ∧ acceleratedOrbit 15 20460 = 1366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20460) = 3 ^ 7 * m + 1366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20460.1, data_15_20460.2]

/-- Complete interval computation for depth 15, residue 20461. -/
theorem bounds_15_20461 : exactInterval 15 20461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20461 : oddCount 20461 15 = 7 ∧ acceleratedOrbit 15 20461 = 1366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20461) = 3 ^ 7 * m + 1366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20461.1, data_15_20461.2]

/-- Complete interval computation for depth 15, residue 20462. -/
theorem bounds_15_20462 : exactInterval 15 20462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20462 : oddCount 20462 15 = 7 ∧ acceleratedOrbit 15 20462 = 1366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20462) = 3 ^ 7 * m + 1366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20462.1, data_15_20462.2]

/-- Complete interval computation for depth 15, residue 20463. -/
theorem bounds_15_20463 : exactInterval 15 20463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20463 : oddCount 20463 15 = 9 ∧ acceleratedOrbit 15 20463 = 12293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20463) = 3 ^ 9 * m + 12293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20463.1, data_15_20463.2]

/-- Complete interval computation for depth 15, residue 20464. -/
theorem bounds_15_20464 : exactInterval 15 20464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20464 : oddCount 20464 15 = 9 ∧ acceleratedOrbit 15 20464 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20464) = 3 ^ 9 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20464.1, data_15_20464.2]

/-- Complete interval computation for depth 15, residue 20465. -/
theorem bounds_15_20465 : exactInterval 15 20465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20465 : oddCount 20465 15 = 9 ∧ acceleratedOrbit 15 20465 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20465) = 3 ^ 9 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20465.1, data_15_20465.2]

/-- Complete interval computation for depth 15, residue 20466. -/
theorem bounds_15_20466 : exactInterval 15 20466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20466 : oddCount 20466 15 = 8 ∧ acceleratedOrbit 15 20466 = 4099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20466) = 3 ^ 8 * m + 4099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20466.1, data_15_20466.2]

/-- Complete interval computation for depth 15, residue 20467. -/
theorem bounds_15_20467 : exactInterval 15 20467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20467 : oddCount 20467 15 = 8 ∧ acceleratedOrbit 15 20467 = 4099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20467) = 3 ^ 8 * m + 4099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20467.1, data_15_20467.2]

/-- Complete interval computation for depth 15, residue 20468. -/
theorem bounds_15_20468 : exactInterval 15 20468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20468 : oddCount 20468 15 = 9 ∧ acceleratedOrbit 15 20468 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20468) = 3 ^ 9 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20468.1, data_15_20468.2]

/-- Complete interval computation for depth 15, residue 20469. -/
theorem bounds_15_20469 : exactInterval 15 20469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20469 : oddCount 20469 15 = 9 ∧ acceleratedOrbit 15 20469 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20469) = 3 ^ 9 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20469.1, data_15_20469.2]

/-- Complete interval computation for depth 15, residue 20470. -/
theorem bounds_15_20470 : exactInterval 15 20470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20470 : oddCount 20470 15 = 10 ∧ acceleratedOrbit 15 20470 = 36895 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20470) = 3 ^ 10 * m + 36895 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20470.1, data_15_20470.2]

/-- Complete interval computation for depth 15, residue 20471. -/
theorem bounds_15_20471 : exactInterval 15 20471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20471 : oddCount 20471 15 = 10 ∧ acceleratedOrbit 15 20471 = 36895 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20471) = 3 ^ 10 * m + 36895 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20471.1, data_15_20471.2]

/-- Complete interval computation for depth 15, residue 20472. -/
theorem bounds_15_20472 : exactInterval 15 20472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20472 : oddCount 20472 15 = 11 ∧ acceleratedOrbit 15 20472 = 110717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20472) = 3 ^ 11 * m + 110717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20472.1, data_15_20472.2]

/-- Complete interval computation for depth 15, residue 20473. -/
theorem bounds_15_20473 : exactInterval 15 20473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20473 : oddCount 20473 15 = 10 ∧ acceleratedOrbit 15 20473 = 36899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20473) = 3 ^ 10 * m + 36899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20473.1, data_15_20473.2]

/-- Complete interval computation for depth 15, residue 20474. -/
theorem bounds_15_20474 : exactInterval 15 20474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20474 : oddCount 20474 15 = 11 ∧ acceleratedOrbit 15 20474 = 110717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20474) = 3 ^ 11 * m + 110717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20474.1, data_15_20474.2]

/-- Complete interval computation for depth 15, residue 20475. -/
theorem bounds_15_20475 : exactInterval 15 20475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20475 : oddCount 20475 15 = 8 ∧ acceleratedOrbit 15 20475 = 4100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20475) = 3 ^ 8 * m + 4100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20475.1, data_15_20475.2]

/-- Complete interval computation for depth 15, residue 20476. -/
theorem bounds_15_20476 : exactInterval 15 20476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20476 : oddCount 20476 15 = 11 ∧ acceleratedOrbit 15 20476 = 110717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20476) = 3 ^ 11 * m + 110717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20476.1, data_15_20476.2]

/-- Complete interval computation for depth 15, residue 20477. -/
theorem bounds_15_20477 : exactInterval 15 20477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20477 : oddCount 20477 15 = 11 ∧ acceleratedOrbit 15 20477 = 110717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20477) = 3 ^ 11 * m + 110717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20477.1, data_15_20477.2]

/-- Complete interval computation for depth 15, residue 20478. -/
theorem bounds_15_20478 : exactInterval 15 20478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20478 : oddCount 20478 15 = 13 ∧ acceleratedOrbit 15 20478 = 996452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20478) = 3 ^ 13 * m + 996452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20478.1, data_15_20478.2]

/-- Complete interval computation for depth 15, residue 20479. -/
theorem bounds_15_20479 : exactInterval 15 20479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20479 : oddCount 20479 15 = 13 ∧ acceleratedOrbit 15 20479 = 996452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20479) = 3 ^ 13 * m + 996452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20479.1, data_15_20479.2]

end Collatz.Research.PassageAtlas.Batch0625
