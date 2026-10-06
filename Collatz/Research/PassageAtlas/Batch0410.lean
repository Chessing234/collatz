import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0410

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13402. -/
theorem bounds_15_13402 : exactInterval 15 13402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13402 : oddCount 13402 15 = 6 ∧ acceleratedOrbit 15 13402 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13402) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13402.1, data_15_13402.2]

/-- Complete interval computation for depth 15, residue 13403. -/
theorem bounds_15_13403 : exactInterval 15 13403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13403 : oddCount 13403 15 = 12 ∧ acceleratedOrbit 15 13403 = 217403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13403) = 3 ^ 12 * m + 217403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13403.1, data_15_13403.2]

/-- Complete interval computation for depth 15, residue 13404. -/
theorem bounds_15_13404 : exactInterval 15 13404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13404 : oddCount 13404 15 = 6 ∧ acceleratedOrbit 15 13404 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13404) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13404.1, data_15_13404.2]

/-- Complete interval computation for depth 15, residue 13405. -/
theorem bounds_15_13405 : exactInterval 15 13405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13405 : oddCount 13405 15 = 6 ∧ acceleratedOrbit 15 13405 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13405) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13405.1, data_15_13405.2]

/-- Complete interval computation for depth 15, residue 13406. -/
theorem bounds_15_13406 : exactInterval 15 13406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13406 : oddCount 13406 15 = 10 ∧ acceleratedOrbit 15 13406 = 24164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13406) = 3 ^ 10 * m + 24164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13406.1, data_15_13406.2]

/-- Complete interval computation for depth 15, residue 13407. -/
theorem bounds_15_13407 : exactInterval 15 13407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13407 : oddCount 13407 15 = 10 ∧ acceleratedOrbit 15 13407 = 24164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13407) = 3 ^ 10 * m + 24164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13407.1, data_15_13407.2]

/-- Complete interval computation for depth 15, residue 13408. -/
theorem bounds_15_13408 : exactInterval 15 13408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13408 : oddCount 13408 15 = 5 ∧ acceleratedOrbit 15 13408 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13408) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13408.1, data_15_13408.2]

/-- Complete interval computation for depth 15, residue 13409. -/
theorem bounds_15_13409 : exactInterval 15 13409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13409 : oddCount 13409 15 = 8 ∧ acceleratedOrbit 15 13409 = 2686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13409) = 3 ^ 8 * m + 2686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13409.1, data_15_13409.2]

/-- Complete interval computation for depth 15, residue 13410. -/
theorem bounds_15_13410 : exactInterval 15 13410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13410 : oddCount 13410 15 = 7 ∧ acceleratedOrbit 15 13410 = 896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13410) = 3 ^ 7 * m + 896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13410.1, data_15_13410.2]

/-- Complete interval computation for depth 15, residue 13411. -/
theorem bounds_15_13411 : exactInterval 15 13411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13411 : oddCount 13411 15 = 7 ∧ acceleratedOrbit 15 13411 = 896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13411) = 3 ^ 7 * m + 896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13411.1, data_15_13411.2]

/-- Complete interval computation for depth 15, residue 13412. -/
theorem bounds_15_13412 : exactInterval 15 13412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13412 : oddCount 13412 15 = 7 ∧ acceleratedOrbit 15 13412 = 896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13412) = 3 ^ 7 * m + 896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13412.1, data_15_13412.2]

/-- Complete interval computation for depth 15, residue 13413. -/
theorem bounds_15_13413 : exactInterval 15 13413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13413 : oddCount 13413 15 = 7 ∧ acceleratedOrbit 15 13413 = 896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13413) = 3 ^ 7 * m + 896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13413.1, data_15_13413.2]

/-- Complete interval computation for depth 15, residue 13414. -/
theorem bounds_15_13414 : exactInterval 15 13414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13414 : oddCount 13414 15 = 7 ∧ acceleratedOrbit 15 13414 = 896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13414) = 3 ^ 7 * m + 896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13414.1, data_15_13414.2]

/-- Complete interval computation for depth 15, residue 13415. -/
theorem bounds_15_13415 : exactInterval 15 13415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13415 : oddCount 13415 15 = 12 ∧ acceleratedOrbit 15 13415 = 217592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13415) = 3 ^ 12 * m + 217592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13415.1, data_15_13415.2]

/-- Complete interval computation for depth 15, residue 13416. -/
theorem bounds_15_13416 : exactInterval 15 13416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13416 : oddCount 13416 15 = 5 ∧ acceleratedOrbit 15 13416 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13416) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13416.1, data_15_13416.2]

/-- Complete interval computation for depth 15, residue 13417. -/
theorem bounds_15_13417 : exactInterval 15 13417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13417 : oddCount 13417 15 = 8 ∧ acceleratedOrbit 15 13417 = 2687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13417) = 3 ^ 8 * m + 2687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13417.1, data_15_13417.2]

/-- Complete interval computation for depth 15, residue 13418. -/
theorem bounds_15_13418 : exactInterval 15 13418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13418 : oddCount 13418 15 = 5 ∧ acceleratedOrbit 15 13418 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13418) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13418.1, data_15_13418.2]

/-- Complete interval computation for depth 15, residue 13419. -/
theorem bounds_15_13419 : exactInterval 15 13419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13419 : oddCount 13419 15 = 9 ∧ acceleratedOrbit 15 13419 = 8063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13419) = 3 ^ 9 * m + 8063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13419.1, data_15_13419.2]

/-- Complete interval computation for depth 15, residue 13420. -/
theorem bounds_15_13420 : exactInterval 15 13420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13420 : oddCount 13420 15 = 10 ∧ acceleratedOrbit 15 13420 = 24194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13420) = 3 ^ 10 * m + 24194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13420.1, data_15_13420.2]

/-- Complete interval computation for depth 15, residue 13421. -/
theorem bounds_15_13421 : exactInterval 15 13421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13421 : oddCount 13421 15 = 10 ∧ acceleratedOrbit 15 13421 = 24194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13421) = 3 ^ 10 * m + 24194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13421.1, data_15_13421.2]

/-- Complete interval computation for depth 15, residue 13422. -/
theorem bounds_15_13422 : exactInterval 15 13422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13422 : oddCount 13422 15 = 10 ∧ acceleratedOrbit 15 13422 = 24194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13422) = 3 ^ 10 * m + 24194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13422.1, data_15_13422.2]

/-- Complete interval computation for depth 15, residue 13423. -/
theorem bounds_15_13423 : exactInterval 15 13423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13423 : oddCount 13423 15 = 11 ∧ acceleratedOrbit 15 13423 = 72575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13423) = 3 ^ 11 * m + 72575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13423.1, data_15_13423.2]

/-- Complete interval computation for depth 15, residue 13424. -/
theorem bounds_15_13424 : exactInterval 15 13424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13424 : oddCount 13424 15 = 8 ∧ acceleratedOrbit 15 13424 = 2693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13424) = 3 ^ 8 * m + 2693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13424.1, data_15_13424.2]

/-- Complete interval computation for depth 15, residue 13425. -/
theorem bounds_15_13425 : exactInterval 15 13425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13425 : oddCount 13425 15 = 5 ∧ acceleratedOrbit 15 13425 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13425) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13425.1, data_15_13425.2]

/-- Complete interval computation for depth 15, residue 13426. -/
theorem bounds_15_13426 : exactInterval 15 13426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13426 : oddCount 13426 15 = 8 ∧ acceleratedOrbit 15 13426 = 2690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13426) = 3 ^ 8 * m + 2690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13426.1, data_15_13426.2]

/-- Complete interval computation for depth 15, residue 13427. -/
theorem bounds_15_13427 : exactInterval 15 13427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13427 : oddCount 13427 15 = 8 ∧ acceleratedOrbit 15 13427 = 2690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13427) = 3 ^ 8 * m + 2690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13427.1, data_15_13427.2]

/-- Complete interval computation for depth 15, residue 13428. -/
theorem bounds_15_13428 : exactInterval 15 13428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13428 : oddCount 13428 15 = 8 ∧ acceleratedOrbit 15 13428 = 2693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13428) = 3 ^ 8 * m + 2693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13428.1, data_15_13428.2]

/-- Complete interval computation for depth 15, residue 13429. -/
theorem bounds_15_13429 : exactInterval 15 13429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13429 : oddCount 13429 15 = 8 ∧ acceleratedOrbit 15 13429 = 2693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13429) = 3 ^ 8 * m + 2693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13429.1, data_15_13429.2]

/-- Complete interval computation for depth 15, residue 13430. -/
theorem bounds_15_13430 : exactInterval 15 13430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13430 : oddCount 13430 15 = 6 ∧ acceleratedOrbit 15 13430 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13430) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13430.1, data_15_13430.2]

/-- Complete interval computation for depth 15, residue 13431. -/
theorem bounds_15_13431 : exactInterval 15 13431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13431 : oddCount 13431 15 = 6 ∧ acceleratedOrbit 15 13431 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13431) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13431.1, data_15_13431.2]

/-- Complete interval computation for depth 15, residue 13432. -/
theorem bounds_15_13432 : exactInterval 15 13432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13432 : oddCount 13432 15 = 8 ∧ acceleratedOrbit 15 13432 = 2693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13432) = 3 ^ 8 * m + 2693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13432.1, data_15_13432.2]

/-- Complete interval computation for depth 15, residue 13433. -/
theorem bounds_15_13433 : exactInterval 15 13433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13433 : oddCount 13433 15 = 10 ∧ acceleratedOrbit 15 13433 = 24212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13433) = 3 ^ 10 * m + 24212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13433.1, data_15_13433.2]

end Collatz.Research.PassageAtlas.Batch0410
