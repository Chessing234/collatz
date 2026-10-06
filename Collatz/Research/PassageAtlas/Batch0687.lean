import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0687

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22478. -/
theorem bounds_15_22478 : exactInterval 15 22478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22478 : oddCount 22478 15 = 8 ∧ acceleratedOrbit 15 22478 = 4502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22478) = 3 ^ 8 * m + 4502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22478.1, data_15_22478.2]

/-- Complete interval computation for depth 15, residue 22479. -/
theorem bounds_15_22479 : exactInterval 15 22479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22479 : oddCount 22479 15 = 8 ∧ acceleratedOrbit 15 22479 = 4502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22479) = 3 ^ 8 * m + 4502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22479.1, data_15_22479.2]

/-- Complete interval computation for depth 15, residue 22480. -/
theorem bounds_15_22480 : exactInterval 15 22480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22480 : oddCount 22480 15 = 5 ∧ acceleratedOrbit 15 22480 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22480) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22480.1, data_15_22480.2]

/-- Complete interval computation for depth 15, residue 22481. -/
theorem bounds_15_22481 : exactInterval 15 22481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22481 : oddCount 22481 15 = 7 ∧ acceleratedOrbit 15 22481 = 1502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22481) = 3 ^ 7 * m + 1502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22481.1, data_15_22481.2]

/-- Complete interval computation for depth 15, residue 22482. -/
theorem bounds_15_22482 : exactInterval 15 22482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22482 : oddCount 22482 15 = 10 ∧ acceleratedOrbit 15 22482 = 40520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22482) = 3 ^ 10 * m + 40520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22482.1, data_15_22482.2]

/-- Complete interval computation for depth 15, residue 22483. -/
theorem bounds_15_22483 : exactInterval 15 22483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22483 : oddCount 22483 15 = 10 ∧ acceleratedOrbit 15 22483 = 40520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22483) = 3 ^ 10 * m + 40520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22483.1, data_15_22483.2]

/-- Complete interval computation for depth 15, residue 22484. -/
theorem bounds_15_22484 : exactInterval 15 22484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22484 : oddCount 22484 15 = 5 ∧ acceleratedOrbit 15 22484 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22484) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22484.1, data_15_22484.2]

/-- Complete interval computation for depth 15, residue 22485. -/
theorem bounds_15_22485 : exactInterval 15 22485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22485 : oddCount 22485 15 = 5 ∧ acceleratedOrbit 15 22485 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22485) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22485.1, data_15_22485.2]

/-- Complete interval computation for depth 15, residue 22486. -/
theorem bounds_15_22486 : exactInterval 15 22486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22486 : oddCount 22486 15 = 7 ∧ acceleratedOrbit 15 22486 = 1501 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22486) = 3 ^ 7 * m + 1501 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22486.1, data_15_22486.2]

/-- Complete interval computation for depth 15, residue 22487. -/
theorem bounds_15_22487 : exactInterval 15 22487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22487 : oddCount 22487 15 = 7 ∧ acceleratedOrbit 15 22487 = 1501 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22487) = 3 ^ 7 * m + 1501 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22487.1, data_15_22487.2]

/-- Complete interval computation for depth 15, residue 22488. -/
theorem bounds_15_22488 : exactInterval 15 22488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22488 : oddCount 22488 15 = 9 ∧ acceleratedOrbit 15 22488 = 13517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22488) = 3 ^ 9 * m + 13517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22488.1, data_15_22488.2]

/-- Complete interval computation for depth 15, residue 22489. -/
theorem bounds_15_22489 : exactInterval 15 22489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22489 : oddCount 22489 15 = 5 ∧ acceleratedOrbit 15 22489 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22489) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22489.1, data_15_22489.2]

/-- Complete interval computation for depth 15, residue 22490. -/
theorem bounds_15_22490 : exactInterval 15 22490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22490 : oddCount 22490 15 = 9 ∧ acceleratedOrbit 15 22490 = 13517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22490) = 3 ^ 9 * m + 13517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22490.1, data_15_22490.2]

/-- Complete interval computation for depth 15, residue 22491. -/
theorem bounds_15_22491 : exactInterval 15 22491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22491 : oddCount 22491 15 = 8 ∧ acceleratedOrbit 15 22491 = 4504 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22491) = 3 ^ 8 * m + 4504 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22491.1, data_15_22491.2]

/-- Complete interval computation for depth 15, residue 22492. -/
theorem bounds_15_22492 : exactInterval 15 22492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22492 : oddCount 22492 15 = 9 ∧ acceleratedOrbit 15 22492 = 13517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22492) = 3 ^ 9 * m + 13517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22492.1, data_15_22492.2]

/-- Complete interval computation for depth 15, residue 22493. -/
theorem bounds_15_22493 : exactInterval 15 22493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22493 : oddCount 22493 15 = 9 ∧ acceleratedOrbit 15 22493 = 13517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22493) = 3 ^ 9 * m + 13517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22493.1, data_15_22493.2]

/-- Complete interval computation for depth 15, residue 22494. -/
theorem bounds_15_22494 : exactInterval 15 22494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22494 : oddCount 22494 15 = 10 ∧ acceleratedOrbit 15 22494 = 40540 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22494) = 3 ^ 10 * m + 40540 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22494.1, data_15_22494.2]

/-- Complete interval computation for depth 15, residue 22495. -/
theorem bounds_15_22495 : exactInterval 15 22495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22495 : oddCount 22495 15 = 10 ∧ acceleratedOrbit 15 22495 = 40540 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22495) = 3 ^ 10 * m + 40540 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22495.1, data_15_22495.2]

/-- Complete interval computation for depth 15, residue 22496. -/
theorem bounds_15_22496 : exactInterval 15 22496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22496 : oddCount 22496 15 = 8 ∧ acceleratedOrbit 15 22496 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22496) = 3 ^ 8 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22496.1, data_15_22496.2]

/-- Complete interval computation for depth 15, residue 22497. -/
theorem bounds_15_22497 : exactInterval 15 22497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22497 : oddCount 22497 15 = 8 ∧ acceleratedOrbit 15 22497 = 4505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22497) = 3 ^ 8 * m + 4505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22497.1, data_15_22497.2]

/-- Complete interval computation for depth 15, residue 22498. -/
theorem bounds_15_22498 : exactInterval 15 22498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22498 : oddCount 22498 15 = 5 ∧ acceleratedOrbit 15 22498 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22498) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22498.1, data_15_22498.2]

/-- Complete interval computation for depth 15, residue 22499. -/
theorem bounds_15_22499 : exactInterval 15 22499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22499 : oddCount 22499 15 = 5 ∧ acceleratedOrbit 15 22499 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22499) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22499.1, data_15_22499.2]

/-- Complete interval computation for depth 15, residue 22500. -/
theorem bounds_15_22500 : exactInterval 15 22500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22500 : oddCount 22500 15 = 8 ∧ acceleratedOrbit 15 22500 = 4508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22500) = 3 ^ 8 * m + 4508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22500.1, data_15_22500.2]

/-- Complete interval computation for depth 15, residue 22501. -/
theorem bounds_15_22501 : exactInterval 15 22501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22501 : oddCount 22501 15 = 8 ∧ acceleratedOrbit 15 22501 = 4508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22501) = 3 ^ 8 * m + 4508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22501.1, data_15_22501.2]

/-- Complete interval computation for depth 15, residue 22502. -/
theorem bounds_15_22502 : exactInterval 15 22502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22502 : oddCount 22502 15 = 8 ∧ acceleratedOrbit 15 22502 = 4508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22502) = 3 ^ 8 * m + 4508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22502.1, data_15_22502.2]

/-- Complete interval computation for depth 15, residue 22503. -/
theorem bounds_15_22503 : exactInterval 15 22503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22503 : oddCount 22503 15 = 7 ∧ acceleratedOrbit 15 22503 = 1502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22503) = 3 ^ 7 * m + 1502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22503.1, data_15_22503.2]

/-- Complete interval computation for depth 15, residue 22504. -/
theorem bounds_15_22504 : exactInterval 15 22504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22504 : oddCount 22504 15 = 8 ∧ acceleratedOrbit 15 22504 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22504) = 3 ^ 8 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22504.1, data_15_22504.2]

/-- Complete interval computation for depth 15, residue 22505. -/
theorem bounds_15_22505 : exactInterval 15 22505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22505 : oddCount 22505 15 = 11 ∧ acceleratedOrbit 15 22505 = 121675 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22505) = 3 ^ 11 * m + 121675 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22505.1, data_15_22505.2]

/-- Complete interval computation for depth 15, residue 22506. -/
theorem bounds_15_22506 : exactInterval 15 22506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22506 : oddCount 22506 15 = 8 ∧ acceleratedOrbit 15 22506 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22506) = 3 ^ 8 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22506.1, data_15_22506.2]

/-- Complete interval computation for depth 15, residue 22507. -/
theorem bounds_15_22507 : exactInterval 15 22507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22507 : oddCount 22507 15 = 11 ∧ acceleratedOrbit 15 22507 = 121688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22507) = 3 ^ 11 * m + 121688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22507.1, data_15_22507.2]

/-- Complete interval computation for depth 15, residue 22508. -/
theorem bounds_15_22508 : exactInterval 15 22508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22508 : oddCount 22508 15 = 9 ∧ acceleratedOrbit 15 22508 = 13526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22508) = 3 ^ 9 * m + 13526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22508.1, data_15_22508.2]

/-- Complete interval computation for depth 15, residue 22509. -/
theorem bounds_15_22509 : exactInterval 15 22509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22509 : oddCount 22509 15 = 9 ∧ acceleratedOrbit 15 22509 = 13526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22509) = 3 ^ 9 * m + 13526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22509.1, data_15_22509.2]

/-- Complete interval computation for depth 15, residue 22510. -/
theorem bounds_15_22510 : exactInterval 15 22510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22510 : oddCount 22510 15 = 9 ∧ acceleratedOrbit 15 22510 = 13526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22510) = 3 ^ 9 * m + 13526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22510.1, data_15_22510.2]

end Collatz.Research.PassageAtlas.Batch0687
