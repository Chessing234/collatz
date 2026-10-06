import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0884

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6394. -/
theorem bounds_13_6394 : exactInterval 13 6394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6394 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6394) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6394 : oddCount 6394 13 = 7 ∧ acceleratedOrbit 13 6394 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6394 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6394) = 3 ^ 7 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6394.1, data_13_6394.2]

/-- Complete interval computation for depth 13, residue 6395. -/
theorem bounds_13_6395 : exactInterval 13 6395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6395 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6395) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6395 : oddCount 6395 13 = 10 ∧ acceleratedOrbit 13 6395 = 46109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6395 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6395) = 3 ^ 10 * m + 46109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6395.1, data_13_6395.2]

/-- Complete interval computation for depth 13, residue 6396. -/
theorem bounds_13_6396 : exactInterval 13 6396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6396 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6396) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6396 : oddCount 6396 13 = 7 ∧ acceleratedOrbit 13 6396 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6396 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6396) = 3 ^ 7 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6396.1, data_13_6396.2]

/-- Complete interval computation for depth 13, residue 6397. -/
theorem bounds_13_6397 : exactInterval 13 6397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6397 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6397) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6397 : oddCount 6397 13 = 7 ∧ acceleratedOrbit 13 6397 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6397 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6397) = 3 ^ 7 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6397.1, data_13_6397.2]

/-- Complete interval computation for depth 13, residue 6398. -/
theorem bounds_13_6398 : exactInterval 13 6398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6398 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6398) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6398 : oddCount 6398 13 = 10 ∧ acceleratedOrbit 13 6398 = 46133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6398 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6398) = 3 ^ 10 * m + 46133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6398.1, data_13_6398.2]

/-- Complete interval computation for depth 13, residue 6399. -/
theorem bounds_13_6399 : exactInterval 13 6399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6399 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6399) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6399 : oddCount 6399 13 = 10 ∧ acceleratedOrbit 13 6399 = 46133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6399 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6399) = 3 ^ 10 * m + 46133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6399.1, data_13_6399.2]

/-- Complete interval computation for depth 13, residue 6400. -/
theorem bounds_13_6400 : exactInterval 13 6400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6400 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6400) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6400 : oddCount 6400 13 = 3 ∧ acceleratedOrbit 13 6400 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6400 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6400) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6400.1, data_13_6400.2]

/-- Complete interval computation for depth 13, residue 6401. -/
theorem bounds_13_6401 : exactInterval 13 6401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6401 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6401) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6401 : oddCount 6401 13 = 5 ∧ acceleratedOrbit 13 6401 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6401 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6401) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6401.1, data_13_6401.2]

/-- Complete interval computation for depth 13, residue 6402. -/
theorem bounds_13_6402 : exactInterval 13 6402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6402 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6402) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6402 : oddCount 6402 13 = 7 ∧ acceleratedOrbit 13 6402 = 1711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6402 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6402) = 3 ^ 7 * m + 1711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6402.1, data_13_6402.2]

/-- Complete interval computation for depth 13, residue 6403. -/
theorem bounds_13_6403 : exactInterval 13 6403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6403 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6403) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6403 : oddCount 6403 13 = 7 ∧ acceleratedOrbit 13 6403 = 1711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6403 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6403) = 3 ^ 7 * m + 1711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6403.1, data_13_6403.2]

/-- Complete interval computation for depth 13, residue 6404. -/
theorem bounds_13_6404 : exactInterval 13 6404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6404 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6404) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6404 : oddCount 6404 13 = 5 ∧ acceleratedOrbit 13 6404 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6404 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6404) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6404.1, data_13_6404.2]

/-- Complete interval computation for depth 13, residue 6405. -/
theorem bounds_13_6405 : exactInterval 13 6405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6405 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6405) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6405 : oddCount 6405 13 = 5 ∧ acceleratedOrbit 13 6405 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6405 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6405) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6405.1, data_13_6405.2]

/-- Complete interval computation for depth 13, residue 6406. -/
theorem bounds_13_6406 : exactInterval 13 6406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6406 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6406) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6406 : oddCount 6406 13 = 5 ∧ acceleratedOrbit 13 6406 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6406 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6406) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6406.1, data_13_6406.2]

/-- Complete interval computation for depth 13, residue 6407. -/
theorem bounds_13_6407 : exactInterval 13 6407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6407 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6407) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6407 : oddCount 6407 13 = 7 ∧ acceleratedOrbit 13 6407 = 1711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6407 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6407) = 3 ^ 7 * m + 1711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6407.1, data_13_6407.2]

/-- Complete interval computation for depth 13, residue 6408. -/
theorem bounds_13_6408 : exactInterval 13 6408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6408 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6408) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6408 : oddCount 6408 13 = 5 ∧ acceleratedOrbit 13 6408 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6408 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6408) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6408.1, data_13_6408.2]

/-- Complete interval computation for depth 13, residue 6409. -/
theorem bounds_13_6409 : exactInterval 13 6409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6409 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6409) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6409 : oddCount 6409 13 = 7 ∧ acceleratedOrbit 13 6409 = 1712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6409 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6409) = 3 ^ 7 * m + 1712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6409.1, data_13_6409.2]

end Collatz.Research.StoppingAtlas.Batch0884
