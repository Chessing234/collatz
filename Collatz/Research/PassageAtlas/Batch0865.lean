import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0865

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28311. -/
theorem bounds_15_28311 : exactInterval 15 28311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28311 : oddCount 28311 15 = 4 ∧ acceleratedOrbit 15 28311 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28311) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28311.1, data_15_28311.2]

/-- Complete interval computation for depth 15, residue 28312. -/
theorem bounds_15_28312 : exactInterval 15 28312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28312 : oddCount 28312 15 = 7 ∧ acceleratedOrbit 15 28312 = 1891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28312) = 3 ^ 7 * m + 1891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28312.1, data_15_28312.2]

/-- Complete interval computation for depth 15, residue 28313. -/
theorem bounds_15_28313 : exactInterval 15 28313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28313 : oddCount 28313 15 = 11 ∧ acceleratedOrbit 15 28313 = 153089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28313) = 3 ^ 11 * m + 153089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28313.1, data_15_28313.2]

/-- Complete interval computation for depth 15, residue 28314. -/
theorem bounds_15_28314 : exactInterval 15 28314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28314 : oddCount 28314 15 = 7 ∧ acceleratedOrbit 15 28314 = 1891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28314) = 3 ^ 7 * m + 1891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28314.1, data_15_28314.2]

/-- Complete interval computation for depth 15, residue 28315. -/
theorem bounds_15_28315 : exactInterval 15 28315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28315 : oddCount 28315 15 = 11 ∧ acceleratedOrbit 15 28315 = 153083 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28315) = 3 ^ 11 * m + 153083 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28315.1, data_15_28315.2]

/-- Complete interval computation for depth 15, residue 28316. -/
theorem bounds_15_28316 : exactInterval 15 28316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28316 : oddCount 28316 15 = 8 ∧ acceleratedOrbit 15 28316 = 5671 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28316) = 3 ^ 8 * m + 5671 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28316.1, data_15_28316.2]

/-- Complete interval computation for depth 15, residue 28317. -/
theorem bounds_15_28317 : exactInterval 15 28317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28317 : oddCount 28317 15 = 8 ∧ acceleratedOrbit 15 28317 = 5671 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28317) = 3 ^ 8 * m + 5671 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28317.1, data_15_28317.2]

/-- Complete interval computation for depth 15, residue 28318. -/
theorem bounds_15_28318 : exactInterval 15 28318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28318 : oddCount 28318 15 = 8 ∧ acceleratedOrbit 15 28318 = 5671 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28318) = 3 ^ 8 * m + 5671 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28318.1, data_15_28318.2]

/-- Complete interval computation for depth 15, residue 28319. -/
theorem bounds_15_28319 : exactInterval 15 28319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28319 : oddCount 28319 15 = 10 ∧ acceleratedOrbit 15 28319 = 51034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28319) = 3 ^ 10 * m + 51034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28319.1, data_15_28319.2]

/-- Complete interval computation for depth 15, residue 28320. -/
theorem bounds_15_28320 : exactInterval 15 28320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28320 : oddCount 28320 15 = 4 ∧ acceleratedOrbit 15 28320 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28320) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28320.1, data_15_28320.2]

/-- Complete interval computation for depth 15, residue 28321. -/
theorem bounds_15_28321 : exactInterval 15 28321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28321 : oddCount 28321 15 = 8 ∧ acceleratedOrbit 15 28321 = 5672 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28321) = 3 ^ 8 * m + 5672 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28321.1, data_15_28321.2]

/-- Complete interval computation for depth 15, residue 28322. -/
theorem bounds_15_28322 : exactInterval 15 28322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28322 : oddCount 28322 15 = 7 ∧ acceleratedOrbit 15 28322 = 1891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28322) = 3 ^ 7 * m + 1891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28322.1, data_15_28322.2]

/-- Complete interval computation for depth 15, residue 28323. -/
theorem bounds_15_28323 : exactInterval 15 28323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28323 : oddCount 28323 15 = 7 ∧ acceleratedOrbit 15 28323 = 1891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28323) = 3 ^ 7 * m + 1891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28323.1, data_15_28323.2]

/-- Complete interval computation for depth 15, residue 28324. -/
theorem bounds_15_28324 : exactInterval 15 28324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28324 : oddCount 28324 15 = 9 ∧ acceleratedOrbit 15 28324 = 17018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28324) = 3 ^ 9 * m + 17018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28324.1, data_15_28324.2]

/-- Complete interval computation for depth 15, residue 28325. -/
theorem bounds_15_28325 : exactInterval 15 28325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28325 : oddCount 28325 15 = 9 ∧ acceleratedOrbit 15 28325 = 17018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28325) = 3 ^ 9 * m + 17018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28325.1, data_15_28325.2]

/-- Complete interval computation for depth 15, residue 28326. -/
theorem bounds_15_28326 : exactInterval 15 28326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28326 : oddCount 28326 15 = 9 ∧ acceleratedOrbit 15 28326 = 17018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28326) = 3 ^ 9 * m + 17018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28326.1, data_15_28326.2]

/-- Complete interval computation for depth 15, residue 28327. -/
theorem bounds_15_28327 : exactInterval 15 28327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28327 : oddCount 28327 15 = 10 ∧ acceleratedOrbit 15 28327 = 51050 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28327) = 3 ^ 10 * m + 51050 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28327.1, data_15_28327.2]

/-- Complete interval computation for depth 15, residue 28328. -/
theorem bounds_15_28328 : exactInterval 15 28328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28328 : oddCount 28328 15 = 4 ∧ acceleratedOrbit 15 28328 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28328) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28328.1, data_15_28328.2]

/-- Complete interval computation for depth 15, residue 28329. -/
theorem bounds_15_28329 : exactInterval 15 28329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28329 : oddCount 28329 15 = 12 ∧ acceleratedOrbit 15 28329 = 459476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28329) = 3 ^ 12 * m + 459476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28329.1, data_15_28329.2]

/-- Complete interval computation for depth 15, residue 28330. -/
theorem bounds_15_28330 : exactInterval 15 28330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28330 : oddCount 28330 15 = 4 ∧ acceleratedOrbit 15 28330 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28330) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28330.1, data_15_28330.2]

/-- Complete interval computation for depth 15, residue 28331. -/
theorem bounds_15_28331 : exactInterval 15 28331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28331 : oddCount 28331 15 = 9 ∧ acceleratedOrbit 15 28331 = 17020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28331) = 3 ^ 9 * m + 17020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28331.1, data_15_28331.2]

/-- Complete interval computation for depth 15, residue 28332. -/
theorem bounds_15_28332 : exactInterval 15 28332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28332 : oddCount 28332 15 = 7 ∧ acceleratedOrbit 15 28332 = 1892 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28332) = 3 ^ 7 * m + 1892 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28332.1, data_15_28332.2]

/-- Complete interval computation for depth 15, residue 28333. -/
theorem bounds_15_28333 : exactInterval 15 28333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28333 : oddCount 28333 15 = 7 ∧ acceleratedOrbit 15 28333 = 1892 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28333) = 3 ^ 7 * m + 1892 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28333.1, data_15_28333.2]

/-- Complete interval computation for depth 15, residue 28334. -/
theorem bounds_15_28334 : exactInterval 15 28334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28334 : oddCount 28334 15 = 7 ∧ acceleratedOrbit 15 28334 = 1892 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28334) = 3 ^ 7 * m + 1892 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28334.1, data_15_28334.2]

/-- Complete interval computation for depth 15, residue 28335. -/
theorem bounds_15_28335 : exactInterval 15 28335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28335 : oddCount 28335 15 = 8 ∧ acceleratedOrbit 15 28335 = 5674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28335) = 3 ^ 8 * m + 5674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28335.1, data_15_28335.2]

/-- Complete interval computation for depth 15, residue 28336. -/
theorem bounds_15_28336 : exactInterval 15 28336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28336 : oddCount 28336 15 = 6 ∧ acceleratedOrbit 15 28336 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28336) = 3 ^ 6 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28336.1, data_15_28336.2]

/-- Complete interval computation for depth 15, residue 28337. -/
theorem bounds_15_28337 : exactInterval 15 28337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28337 : oddCount 28337 15 = 6 ∧ acceleratedOrbit 15 28337 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28337) = 3 ^ 6 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28337.1, data_15_28337.2]

/-- Complete interval computation for depth 15, residue 28338. -/
theorem bounds_15_28338 : exactInterval 15 28338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28338 : oddCount 28338 15 = 6 ∧ acceleratedOrbit 15 28338 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28338) = 3 ^ 6 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28338.1, data_15_28338.2]

/-- Complete interval computation for depth 15, residue 28339. -/
theorem bounds_15_28339 : exactInterval 15 28339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28339 : oddCount 28339 15 = 6 ∧ acceleratedOrbit 15 28339 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28339) = 3 ^ 6 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28339.1, data_15_28339.2]

/-- Complete interval computation for depth 15, residue 28340. -/
theorem bounds_15_28340 : exactInterval 15 28340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28340 : oddCount 28340 15 = 6 ∧ acceleratedOrbit 15 28340 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28340) = 3 ^ 6 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28340.1, data_15_28340.2]

/-- Complete interval computation for depth 15, residue 28341. -/
theorem bounds_15_28341 : exactInterval 15 28341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28341 : oddCount 28341 15 = 6 ∧ acceleratedOrbit 15 28341 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28341) = 3 ^ 6 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28341.1, data_15_28341.2]

/-- Complete interval computation for depth 15, residue 28342. -/
theorem bounds_15_28342 : exactInterval 15 28342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28342 : oddCount 28342 15 = 9 ∧ acceleratedOrbit 15 28342 = 17027 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28342) = 3 ^ 9 * m + 17027 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28342.1, data_15_28342.2]

/-- Complete interval computation for depth 15, residue 28343. -/
theorem bounds_15_28343 : exactInterval 15 28343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28343 : oddCount 28343 15 = 9 ∧ acceleratedOrbit 15 28343 = 17027 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28343) = 3 ^ 9 * m + 17027 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28343.1, data_15_28343.2]

end Collatz.Research.PassageAtlas.Batch0865
