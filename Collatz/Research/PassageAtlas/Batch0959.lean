import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0959

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31391. -/
theorem bounds_15_31391 : exactInterval 15 31391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31391 : oddCount 31391 15 = 9 ∧ acceleratedOrbit 15 31391 = 18857 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31391) = 3 ^ 9 * m + 18857 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31391.1, data_15_31391.2]

/-- Complete interval computation for depth 15, residue 31392. -/
theorem bounds_15_31392 : exactInterval 15 31392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31392 : oddCount 31392 15 = 4 ∧ acceleratedOrbit 15 31392 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31392) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31392.1, data_15_31392.2]

/-- Complete interval computation for depth 15, residue 31393. -/
theorem bounds_15_31393 : exactInterval 15 31393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31393 : oddCount 31393 15 = 10 ∧ acceleratedOrbit 15 31393 = 56578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31393) = 3 ^ 10 * m + 56578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31393.1, data_15_31393.2]

/-- Complete interval computation for depth 15, residue 31394. -/
theorem bounds_15_31394 : exactInterval 15 31394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31394 : oddCount 31394 15 = 9 ∧ acceleratedOrbit 15 31394 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31394) = 3 ^ 9 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31394.1, data_15_31394.2]

/-- Complete interval computation for depth 15, residue 31395. -/
theorem bounds_15_31395 : exactInterval 15 31395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31395 : oddCount 31395 15 = 9 ∧ acceleratedOrbit 15 31395 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31395) = 3 ^ 9 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31395.1, data_15_31395.2]

/-- Complete interval computation for depth 15, residue 31396. -/
theorem bounds_15_31396 : exactInterval 15 31396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31396 : oddCount 31396 15 = 11 ∧ acceleratedOrbit 15 31396 = 169766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31396) = 3 ^ 11 * m + 169766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31396.1, data_15_31396.2]

/-- Complete interval computation for depth 15, residue 31397. -/
theorem bounds_15_31397 : exactInterval 15 31397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31397 : oddCount 31397 15 = 11 ∧ acceleratedOrbit 15 31397 = 169766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31397) = 3 ^ 11 * m + 169766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31397.1, data_15_31397.2]

/-- Complete interval computation for depth 15, residue 31398. -/
theorem bounds_15_31398 : exactInterval 15 31398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31398 : oddCount 31398 15 = 11 ∧ acceleratedOrbit 15 31398 = 169766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31398) = 3 ^ 11 * m + 169766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31398.1, data_15_31398.2]

/-- Complete interval computation for depth 15, residue 31399. -/
theorem bounds_15_31399 : exactInterval 15 31399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31399 : oddCount 31399 15 = 10 ∧ acceleratedOrbit 15 31399 = 56585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31399) = 3 ^ 10 * m + 56585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31399.1, data_15_31399.2]

/-- Complete interval computation for depth 15, residue 31400. -/
theorem bounds_15_31400 : exactInterval 15 31400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31400 : oddCount 31400 15 = 4 ∧ acceleratedOrbit 15 31400 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31400) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31400.1, data_15_31400.2]

/-- Complete interval computation for depth 15, residue 31401. -/
theorem bounds_15_31401 : exactInterval 15 31401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31401 : oddCount 31401 15 = 13 ∧ acceleratedOrbit 15 31401 = 1527893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31401) = 3 ^ 13 * m + 1527893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31401.1, data_15_31401.2]

/-- Complete interval computation for depth 15, residue 31402. -/
theorem bounds_15_31402 : exactInterval 15 31402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31402 : oddCount 31402 15 = 4 ∧ acceleratedOrbit 15 31402 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31402) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31402.1, data_15_31402.2]

/-- Complete interval computation for depth 15, residue 31403. -/
theorem bounds_15_31403 : exactInterval 15 31403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31403 : oddCount 31403 15 = 9 ∧ acceleratedOrbit 15 31403 = 18866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31403) = 3 ^ 9 * m + 18866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31403.1, data_15_31403.2]

/-- Complete interval computation for depth 15, residue 31404. -/
theorem bounds_15_31404 : exactInterval 15 31404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31404 : oddCount 31404 15 = 9 ∧ acceleratedOrbit 15 31404 = 18872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31404) = 3 ^ 9 * m + 18872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31404.1, data_15_31404.2]

/-- Complete interval computation for depth 15, residue 31405. -/
theorem bounds_15_31405 : exactInterval 15 31405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31405 : oddCount 31405 15 = 9 ∧ acceleratedOrbit 15 31405 = 18872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31405) = 3 ^ 9 * m + 18872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31405.1, data_15_31405.2]

/-- Complete interval computation for depth 15, residue 31406. -/
theorem bounds_15_31406 : exactInterval 15 31406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31406 : oddCount 31406 15 = 9 ∧ acceleratedOrbit 15 31406 = 18872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31406) = 3 ^ 9 * m + 18872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31406.1, data_15_31406.2]

/-- Complete interval computation for depth 15, residue 31407. -/
theorem bounds_15_31407 : exactInterval 15 31407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31407 : oddCount 31407 15 = 8 ∧ acceleratedOrbit 15 31407 = 6290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31407) = 3 ^ 8 * m + 6290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31407.1, data_15_31407.2]

/-- Complete interval computation for depth 15, residue 31408. -/
theorem bounds_15_31408 : exactInterval 15 31408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31408 : oddCount 31408 15 = 7 ∧ acceleratedOrbit 15 31408 = 2099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31408) = 3 ^ 7 * m + 2099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31408.1, data_15_31408.2]

/-- Complete interval computation for depth 15, residue 31409. -/
theorem bounds_15_31409 : exactInterval 15 31409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31409 : oddCount 31409 15 = 5 ∧ acceleratedOrbit 15 31409 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31409) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31409.1, data_15_31409.2]

/-- Complete interval computation for depth 15, residue 31410. -/
theorem bounds_15_31410 : exactInterval 15 31410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31410 : oddCount 31410 15 = 5 ∧ acceleratedOrbit 15 31410 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31410) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31410.1, data_15_31410.2]

/-- Complete interval computation for depth 15, residue 31411. -/
theorem bounds_15_31411 : exactInterval 15 31411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31411 : oddCount 31411 15 = 5 ∧ acceleratedOrbit 15 31411 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31411) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31411.1, data_15_31411.2]

/-- Complete interval computation for depth 15, residue 31412. -/
theorem bounds_15_31412 : exactInterval 15 31412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31412 : oddCount 31412 15 = 7 ∧ acceleratedOrbit 15 31412 = 2099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31412) = 3 ^ 7 * m + 2099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31412.1, data_15_31412.2]

/-- Complete interval computation for depth 15, residue 31413. -/
theorem bounds_15_31413 : exactInterval 15 31413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31413 : oddCount 31413 15 = 7 ∧ acceleratedOrbit 15 31413 = 2099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31413) = 3 ^ 7 * m + 2099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31413.1, data_15_31413.2]

/-- Complete interval computation for depth 15, residue 31414. -/
theorem bounds_15_31414 : exactInterval 15 31414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31414 : oddCount 31414 15 = 10 ∧ acceleratedOrbit 15 31414 = 56618 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31414) = 3 ^ 10 * m + 56618 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31414.1, data_15_31414.2]

/-- Complete interval computation for depth 15, residue 31415. -/
theorem bounds_15_31415 : exactInterval 15 31415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31415 : oddCount 31415 15 = 10 ∧ acceleratedOrbit 15 31415 = 56618 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31415) = 3 ^ 10 * m + 56618 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31415.1, data_15_31415.2]

/-- Complete interval computation for depth 15, residue 31416. -/
theorem bounds_15_31416 : exactInterval 15 31416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31416 : oddCount 31416 15 = 7 ∧ acceleratedOrbit 15 31416 = 2099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31416) = 3 ^ 7 * m + 2099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31416.1, data_15_31416.2]

/-- Complete interval computation for depth 15, residue 31417. -/
theorem bounds_15_31417 : exactInterval 15 31417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31417 : oddCount 31417 15 = 5 ∧ acceleratedOrbit 15 31417 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31417) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31417.1, data_15_31417.2]

/-- Complete interval computation for depth 15, residue 31418. -/
theorem bounds_15_31418 : exactInterval 15 31418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31418 : oddCount 31418 15 = 7 ∧ acceleratedOrbit 15 31418 = 2099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31418) = 3 ^ 7 * m + 2099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31418.1, data_15_31418.2]

/-- Complete interval computation for depth 15, residue 31419. -/
theorem bounds_15_31419 : exactInterval 15 31419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31419 : oddCount 31419 15 = 9 ∧ acceleratedOrbit 15 31419 = 18875 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31419) = 3 ^ 9 * m + 18875 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31419.1, data_15_31419.2]

/-- Complete interval computation for depth 15, residue 31420. -/
theorem bounds_15_31420 : exactInterval 15 31420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31420 : oddCount 31420 15 = 8 ∧ acceleratedOrbit 15 31420 = 6293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31420) = 3 ^ 8 * m + 6293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31420.1, data_15_31420.2]

/-- Complete interval computation for depth 15, residue 31421. -/
theorem bounds_15_31421 : exactInterval 15 31421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31421 : oddCount 31421 15 = 8 ∧ acceleratedOrbit 15 31421 = 6293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31421) = 3 ^ 8 * m + 6293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31421.1, data_15_31421.2]

/-- Complete interval computation for depth 15, residue 31422. -/
theorem bounds_15_31422 : exactInterval 15 31422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31422 : oddCount 31422 15 = 8 ∧ acceleratedOrbit 15 31422 = 6293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31422) = 3 ^ 8 * m + 6293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31422.1, data_15_31422.2]

/-- Complete interval computation for depth 15, residue 31423. -/
theorem bounds_15_31423 : exactInterval 15 31423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31423 : oddCount 31423 15 = 11 ∧ acceleratedOrbit 15 31423 = 169883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31423) = 3 ^ 11 * m + 169883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31423.1, data_15_31423.2]

end Collatz.Research.PassageAtlas.Batch0959
