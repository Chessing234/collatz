import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0961

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31457. -/
theorem bounds_15_31457 : exactInterval 15 31457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31457 : oddCount 31457 15 = 8 ∧ acceleratedOrbit 15 31457 = 6299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31457) = 3 ^ 8 * m + 6299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31457.1, data_15_31457.2]

/-- Complete interval computation for depth 15, residue 31458. -/
theorem bounds_15_31458 : exactInterval 15 31458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31458 : oddCount 31458 15 = 7 ∧ acceleratedOrbit 15 31458 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31458) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31458.1, data_15_31458.2]

/-- Complete interval computation for depth 15, residue 31459. -/
theorem bounds_15_31459 : exactInterval 15 31459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31459 : oddCount 31459 15 = 7 ∧ acceleratedOrbit 15 31459 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31459) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31459.1, data_15_31459.2]

/-- Complete interval computation for depth 15, residue 31460. -/
theorem bounds_15_31460 : exactInterval 15 31460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31460 : oddCount 31460 15 = 7 ∧ acceleratedOrbit 15 31460 = 2101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31460) = 3 ^ 7 * m + 2101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31460.1, data_15_31460.2]

/-- Complete interval computation for depth 15, residue 31461. -/
theorem bounds_15_31461 : exactInterval 15 31461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31461 : oddCount 31461 15 = 7 ∧ acceleratedOrbit 15 31461 = 2101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31461) = 3 ^ 7 * m + 2101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31461.1, data_15_31461.2]

/-- Complete interval computation for depth 15, residue 31462. -/
theorem bounds_15_31462 : exactInterval 15 31462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31462 : oddCount 31462 15 = 7 ∧ acceleratedOrbit 15 31462 = 2101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31462) = 3 ^ 7 * m + 2101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31462.1, data_15_31462.2]

/-- Complete interval computation for depth 15, residue 31463. -/
theorem bounds_15_31463 : exactInterval 15 31463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31463 : oddCount 31463 15 = 13 ∧ acceleratedOrbit 15 31463 = 1530899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31463) = 3 ^ 13 * m + 1530899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31463.1, data_15_31463.2]

/-- Complete interval computation for depth 15, residue 31464. -/
theorem bounds_15_31464 : exactInterval 15 31464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31464 : oddCount 31464 15 = 7 ∧ acceleratedOrbit 15 31464 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31464) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31464.1, data_15_31464.2]

/-- Complete interval computation for depth 15, residue 31465. -/
theorem bounds_15_31465 : exactInterval 15 31465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31465 : oddCount 31465 15 = 9 ∧ acceleratedOrbit 15 31465 = 18902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31465) = 3 ^ 9 * m + 18902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31465.1, data_15_31465.2]

/-- Complete interval computation for depth 15, residue 31466. -/
theorem bounds_15_31466 : exactInterval 15 31466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31466 : oddCount 31466 15 = 7 ∧ acceleratedOrbit 15 31466 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31466) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31466.1, data_15_31466.2]

/-- Complete interval computation for depth 15, residue 31467. -/
theorem bounds_15_31467 : exactInterval 15 31467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31467 : oddCount 31467 15 = 8 ∧ acceleratedOrbit 15 31467 = 6301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31467) = 3 ^ 8 * m + 6301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31467.1, data_15_31467.2]

/-- Complete interval computation for depth 15, residue 31468. -/
theorem bounds_15_31468 : exactInterval 15 31468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31468 : oddCount 31468 15 = 7 ∧ acceleratedOrbit 15 31468 = 2101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31468) = 3 ^ 7 * m + 2101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31468.1, data_15_31468.2]

/-- Complete interval computation for depth 15, residue 31469. -/
theorem bounds_15_31469 : exactInterval 15 31469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31469 : oddCount 31469 15 = 7 ∧ acceleratedOrbit 15 31469 = 2101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31469) = 3 ^ 7 * m + 2101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31469.1, data_15_31469.2]

/-- Complete interval computation for depth 15, residue 31470. -/
theorem bounds_15_31470 : exactInterval 15 31470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31470 : oddCount 31470 15 = 7 ∧ acceleratedOrbit 15 31470 = 2101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31470) = 3 ^ 7 * m + 2101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31470.1, data_15_31470.2]

/-- Complete interval computation for depth 15, residue 31471. -/
theorem bounds_15_31471 : exactInterval 15 31471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31471 : oddCount 31471 15 = 10 ∧ acceleratedOrbit 15 31471 = 56714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31471) = 3 ^ 10 * m + 56714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31471.1, data_15_31471.2]

/-- Complete interval computation for depth 15, residue 31472. -/
theorem bounds_15_31472 : exactInterval 15 31472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31472 : oddCount 31472 15 = 6 ∧ acceleratedOrbit 15 31472 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31472) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31472.1, data_15_31472.2]

/-- Complete interval computation for depth 15, residue 31473. -/
theorem bounds_15_31473 : exactInterval 15 31473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31473 : oddCount 31473 15 = 7 ∧ acceleratedOrbit 15 31473 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31473) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31473.1, data_15_31473.2]

/-- Complete interval computation for depth 15, residue 31474. -/
theorem bounds_15_31474 : exactInterval 15 31474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31474 : oddCount 31474 15 = 10 ∧ acceleratedOrbit 15 31474 = 56726 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31474) = 3 ^ 10 * m + 56726 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31474.1, data_15_31474.2]

/-- Complete interval computation for depth 15, residue 31475. -/
theorem bounds_15_31475 : exactInterval 15 31475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31475 : oddCount 31475 15 = 10 ∧ acceleratedOrbit 15 31475 = 56726 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31475) = 3 ^ 10 * m + 56726 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31475.1, data_15_31475.2]

/-- Complete interval computation for depth 15, residue 31476. -/
theorem bounds_15_31476 : exactInterval 15 31476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31476 : oddCount 31476 15 = 6 ∧ acceleratedOrbit 15 31476 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31476) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31476.1, data_15_31476.2]

/-- Complete interval computation for depth 15, residue 31477. -/
theorem bounds_15_31477 : exactInterval 15 31477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31477 : oddCount 31477 15 = 6 ∧ acceleratedOrbit 15 31477 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31477) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31477.1, data_15_31477.2]

/-- Complete interval computation for depth 15, residue 31478. -/
theorem bounds_15_31478 : exactInterval 15 31478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31478 : oddCount 31478 15 = 8 ∧ acceleratedOrbit 15 31478 = 6304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31478) = 3 ^ 8 * m + 6304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31478.1, data_15_31478.2]

/-- Complete interval computation for depth 15, residue 31479. -/
theorem bounds_15_31479 : exactInterval 15 31479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31479 : oddCount 31479 15 = 8 ∧ acceleratedOrbit 15 31479 = 6304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31479) = 3 ^ 8 * m + 6304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31479.1, data_15_31479.2]

/-- Complete interval computation for depth 15, residue 31480. -/
theorem bounds_15_31480 : exactInterval 15 31480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31480 : oddCount 31480 15 = 6 ∧ acceleratedOrbit 15 31480 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31480) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31480.1, data_15_31480.2]

/-- Complete interval computation for depth 15, residue 31481. -/
theorem bounds_15_31481 : exactInterval 15 31481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31481 : oddCount 31481 15 = 9 ∧ acceleratedOrbit 15 31481 = 18913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31481) = 3 ^ 9 * m + 18913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31481.1, data_15_31481.2]

/-- Complete interval computation for depth 15, residue 31482. -/
theorem bounds_15_31482 : exactInterval 15 31482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31482 : oddCount 31482 15 = 6 ∧ acceleratedOrbit 15 31482 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31482) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31482.1, data_15_31482.2]

/-- Complete interval computation for depth 15, residue 31483. -/
theorem bounds_15_31483 : exactInterval 15 31483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31483 : oddCount 31483 15 = 10 ∧ acceleratedOrbit 15 31483 = 56737 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31483) = 3 ^ 10 * m + 56737 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31483.1, data_15_31483.2]

/-- Complete interval computation for depth 15, residue 31484. -/
theorem bounds_15_31484 : exactInterval 15 31484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31484 : oddCount 31484 15 = 10 ∧ acceleratedOrbit 15 31484 = 56744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31484) = 3 ^ 10 * m + 56744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31484.1, data_15_31484.2]

/-- Complete interval computation for depth 15, residue 31485. -/
theorem bounds_15_31485 : exactInterval 15 31485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31485 : oddCount 31485 15 = 10 ∧ acceleratedOrbit 15 31485 = 56744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31485) = 3 ^ 10 * m + 56744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31485.1, data_15_31485.2]

/-- Complete interval computation for depth 15, residue 31486. -/
theorem bounds_15_31486 : exactInterval 15 31486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31486 : oddCount 31486 15 = 10 ∧ acceleratedOrbit 15 31486 = 56744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31486) = 3 ^ 10 * m + 56744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31486.1, data_15_31486.2]

/-- Complete interval computation for depth 15, residue 31487. -/
theorem bounds_15_31487 : exactInterval 15 31487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31487 : oddCount 31487 15 = 11 ∧ acceleratedOrbit 15 31487 = 170228 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31487) = 3 ^ 11 * m + 170228 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31487.1, data_15_31487.2]

/-- Complete interval computation for depth 15, residue 31488. -/
theorem bounds_15_31488 : exactInterval 15 31488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31488 : oddCount 31488 15 = 5 ∧ acceleratedOrbit 15 31488 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31488) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31488.1, data_15_31488.2]

/-- Complete interval computation for depth 15, residue 31489. -/
theorem bounds_15_31489 : exactInterval 15 31489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31489 : oddCount 31489 15 = 8 ∧ acceleratedOrbit 15 31489 = 6308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31489) = 3 ^ 8 * m + 6308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31489.1, data_15_31489.2]

end Collatz.Research.PassageAtlas.Batch0961
