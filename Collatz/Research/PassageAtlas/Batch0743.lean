import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0743

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24313. -/
theorem bounds_15_24313 : exactInterval 15 24313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24313 : oddCount 24313 15 = 6 ∧ acceleratedOrbit 15 24313 = 541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24313) = 3 ^ 6 * m + 541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24313.1, data_15_24313.2]

/-- Complete interval computation for depth 15, residue 24314. -/
theorem bounds_15_24314 : exactInterval 15 24314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24314 : oddCount 24314 15 = 8 ∧ acceleratedOrbit 15 24314 = 4870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24314) = 3 ^ 8 * m + 4870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24314.1, data_15_24314.2]

/-- Complete interval computation for depth 15, residue 24315. -/
theorem bounds_15_24315 : exactInterval 15 24315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24315 : oddCount 24315 15 = 11 ∧ acceleratedOrbit 15 24315 = 131462 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24315) = 3 ^ 11 * m + 131462 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24315.1, data_15_24315.2]

/-- Complete interval computation for depth 15, residue 24316. -/
theorem bounds_15_24316 : exactInterval 15 24316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24316 : oddCount 24316 15 = 9 ∧ acceleratedOrbit 15 24316 = 14609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24316) = 3 ^ 9 * m + 14609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24316.1, data_15_24316.2]

/-- Complete interval computation for depth 15, residue 24317. -/
theorem bounds_15_24317 : exactInterval 15 24317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24317 : oddCount 24317 15 = 9 ∧ acceleratedOrbit 15 24317 = 14609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24317) = 3 ^ 9 * m + 14609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24317.1, data_15_24317.2]

/-- Complete interval computation for depth 15, residue 24318. -/
theorem bounds_15_24318 : exactInterval 15 24318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24318 : oddCount 24318 15 = 9 ∧ acceleratedOrbit 15 24318 = 14609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24318) = 3 ^ 9 * m + 14609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24318.1, data_15_24318.2]

/-- Complete interval computation for depth 15, residue 24319. -/
theorem bounds_15_24319 : exactInterval 15 24319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24319 : oddCount 24319 15 = 13 ∧ acceleratedOrbit 15 24319 = 1183288 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24319) = 3 ^ 13 * m + 1183288 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24319.1, data_15_24319.2]

/-- Complete interval computation for depth 15, residue 24320. -/
theorem bounds_15_24320 : exactInterval 15 24320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24320 : oddCount 24320 15 = 5 ∧ acceleratedOrbit 15 24320 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24320) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24320.1, data_15_24320.2]

/-- Complete interval computation for depth 15, residue 24321. -/
theorem bounds_15_24321 : exactInterval 15 24321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24321 : oddCount 24321 15 = 6 ∧ acceleratedOrbit 15 24321 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24321) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24321.1, data_15_24321.2]

/-- Complete interval computation for depth 15, residue 24322. -/
theorem bounds_15_24322 : exactInterval 15 24322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24322 : oddCount 24322 15 = 7 ∧ acceleratedOrbit 15 24322 = 1624 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24322) = 3 ^ 7 * m + 1624 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24322.1, data_15_24322.2]

/-- Complete interval computation for depth 15, residue 24323. -/
theorem bounds_15_24323 : exactInterval 15 24323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24323 : oddCount 24323 15 = 7 ∧ acceleratedOrbit 15 24323 = 1624 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24323) = 3 ^ 7 * m + 1624 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24323.1, data_15_24323.2]

/-- Complete interval computation for depth 15, residue 24324. -/
theorem bounds_15_24324 : exactInterval 15 24324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24324 : oddCount 24324 15 = 6 ∧ acceleratedOrbit 15 24324 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24324) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24324.1, data_15_24324.2]

/-- Complete interval computation for depth 15, residue 24325. -/
theorem bounds_15_24325 : exactInterval 15 24325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24325 : oddCount 24325 15 = 6 ∧ acceleratedOrbit 15 24325 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24325) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24325.1, data_15_24325.2]

/-- Complete interval computation for depth 15, residue 24326. -/
theorem bounds_15_24326 : exactInterval 15 24326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24326 : oddCount 24326 15 = 6 ∧ acceleratedOrbit 15 24326 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24326) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24326.1, data_15_24326.2]

/-- Complete interval computation for depth 15, residue 24327. -/
theorem bounds_15_24327 : exactInterval 15 24327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24327 : oddCount 24327 15 = 7 ∧ acceleratedOrbit 15 24327 = 1624 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24327) = 3 ^ 7 * m + 1624 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24327.1, data_15_24327.2]

/-- Complete interval computation for depth 15, residue 24328. -/
theorem bounds_15_24328 : exactInterval 15 24328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24328 : oddCount 24328 15 = 7 ∧ acceleratedOrbit 15 24328 = 1625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24328) = 3 ^ 7 * m + 1625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24328.1, data_15_24328.2]

/-- Complete interval computation for depth 15, residue 24329. -/
theorem bounds_15_24329 : exactInterval 15 24329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24329 : oddCount 24329 15 = 10 ∧ acceleratedOrbit 15 24329 = 43847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24329) = 3 ^ 10 * m + 43847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24329.1, data_15_24329.2]

/-- Complete interval computation for depth 15, residue 24330. -/
theorem bounds_15_24330 : exactInterval 15 24330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24330 : oddCount 24330 15 = 7 ∧ acceleratedOrbit 15 24330 = 1625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24330) = 3 ^ 7 * m + 1625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24330.1, data_15_24330.2]

/-- Complete interval computation for depth 15, residue 24331. -/
theorem bounds_15_24331 : exactInterval 15 24331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24331 : oddCount 24331 15 = 8 ∧ acceleratedOrbit 15 24331 = 4873 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24331) = 3 ^ 8 * m + 4873 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24331.1, data_15_24331.2]

/-- Complete interval computation for depth 15, residue 24332. -/
theorem bounds_15_24332 : exactInterval 15 24332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24332 : oddCount 24332 15 = 7 ∧ acceleratedOrbit 15 24332 = 1625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24332) = 3 ^ 7 * m + 1625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24332.1, data_15_24332.2]

/-- Complete interval computation for depth 15, residue 24333. -/
theorem bounds_15_24333 : exactInterval 15 24333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24333 : oddCount 24333 15 = 7 ∧ acceleratedOrbit 15 24333 = 1625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24333) = 3 ^ 7 * m + 1625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24333.1, data_15_24333.2]

/-- Complete interval computation for depth 15, residue 24334. -/
theorem bounds_15_24334 : exactInterval 15 24334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24334 : oddCount 24334 15 = 6 ∧ acceleratedOrbit 15 24334 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24334) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24334.1, data_15_24334.2]

/-- Complete interval computation for depth 15, residue 24335. -/
theorem bounds_15_24335 : exactInterval 15 24335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24335 : oddCount 24335 15 = 6 ∧ acceleratedOrbit 15 24335 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24335) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24335.1, data_15_24335.2]

/-- Complete interval computation for depth 15, residue 24336. -/
theorem bounds_15_24336 : exactInterval 15 24336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24336 : oddCount 24336 15 = 5 ∧ acceleratedOrbit 15 24336 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24336) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24336.1, data_15_24336.2]

/-- Complete interval computation for depth 15, residue 24337. -/
theorem bounds_15_24337 : exactInterval 15 24337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24337 : oddCount 24337 15 = 7 ∧ acceleratedOrbit 15 24337 = 1625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24337) = 3 ^ 7 * m + 1625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24337.1, data_15_24337.2]

/-- Complete interval computation for depth 15, residue 24338. -/
theorem bounds_15_24338 : exactInterval 15 24338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24338 : oddCount 24338 15 = 8 ∧ acceleratedOrbit 15 24338 = 4874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24338) = 3 ^ 8 * m + 4874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24338.1, data_15_24338.2]

/-- Complete interval computation for depth 15, residue 24339. -/
theorem bounds_15_24339 : exactInterval 15 24339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24339 : oddCount 24339 15 = 8 ∧ acceleratedOrbit 15 24339 = 4874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24339) = 3 ^ 8 * m + 4874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24339.1, data_15_24339.2]

/-- Complete interval computation for depth 15, residue 24340. -/
theorem bounds_15_24340 : exactInterval 15 24340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24340 : oddCount 24340 15 = 5 ∧ acceleratedOrbit 15 24340 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24340) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24340.1, data_15_24340.2]

/-- Complete interval computation for depth 15, residue 24341. -/
theorem bounds_15_24341 : exactInterval 15 24341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24341 : oddCount 24341 15 = 5 ∧ acceleratedOrbit 15 24341 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24341) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24341.1, data_15_24341.2]

/-- Complete interval computation for depth 15, residue 24342. -/
theorem bounds_15_24342 : exactInterval 15 24342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24342 : oddCount 24342 15 = 7 ∧ acceleratedOrbit 15 24342 = 1625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24342) = 3 ^ 7 * m + 1625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24342.1, data_15_24342.2]

/-- Complete interval computation for depth 15, residue 24343. -/
theorem bounds_15_24343 : exactInterval 15 24343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24343 : oddCount 24343 15 = 7 ∧ acceleratedOrbit 15 24343 = 1625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24343) = 3 ^ 7 * m + 1625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24343.1, data_15_24343.2]

/-- Complete interval computation for depth 15, residue 24344. -/
theorem bounds_15_24344 : exactInterval 15 24344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24344 : oddCount 24344 15 = 5 ∧ acceleratedOrbit 15 24344 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24344) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24344.1, data_15_24344.2]

/-- Complete interval computation for depth 15, residue 24345. -/
theorem bounds_15_24345 : exactInterval 15 24345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24345 : oddCount 24345 15 = 10 ∧ acceleratedOrbit 15 24345 = 43877 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24345) = 3 ^ 10 * m + 43877 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24345.1, data_15_24345.2]

end Collatz.Research.PassageAtlas.Batch0743
