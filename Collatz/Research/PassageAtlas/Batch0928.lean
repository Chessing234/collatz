import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0928

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30375. -/
theorem bounds_15_30375 : exactInterval 15 30375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30375 : oddCount 30375 15 = 9 ∧ acceleratedOrbit 15 30375 = 18247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30375) = 3 ^ 9 * m + 18247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30375.1, data_15_30375.2]

/-- Complete interval computation for depth 15, residue 30376. -/
theorem bounds_15_30376 : exactInterval 15 30376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30376 : oddCount 30376 15 = 4 ∧ acceleratedOrbit 15 30376 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30376) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30376.1, data_15_30376.2]

/-- Complete interval computation for depth 15, residue 30377. -/
theorem bounds_15_30377 : exactInterval 15 30377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30377 : oddCount 30377 15 = 11 ∧ acceleratedOrbit 15 30377 = 164231 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30377) = 3 ^ 11 * m + 164231 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30377.1, data_15_30377.2]

/-- Complete interval computation for depth 15, residue 30378. -/
theorem bounds_15_30378 : exactInterval 15 30378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30378 : oddCount 30378 15 = 4 ∧ acceleratedOrbit 15 30378 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30378) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30378.1, data_15_30378.2]

/-- Complete interval computation for depth 15, residue 30379. -/
theorem bounds_15_30379 : exactInterval 15 30379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30379 : oddCount 30379 15 = 9 ∧ acceleratedOrbit 15 30379 = 18251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30379) = 3 ^ 9 * m + 18251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30379.1, data_15_30379.2]

/-- Complete interval computation for depth 15, residue 30380. -/
theorem bounds_15_30380 : exactInterval 15 30380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30380 : oddCount 30380 15 = 8 ∧ acceleratedOrbit 15 30380 = 6085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30380) = 3 ^ 8 * m + 6085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30380.1, data_15_30380.2]

/-- Complete interval computation for depth 15, residue 30381. -/
theorem bounds_15_30381 : exactInterval 15 30381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30381 : oddCount 30381 15 = 8 ∧ acceleratedOrbit 15 30381 = 6085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30381) = 3 ^ 8 * m + 6085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30381.1, data_15_30381.2]

/-- Complete interval computation for depth 15, residue 30382. -/
theorem bounds_15_30382 : exactInterval 15 30382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30382 : oddCount 30382 15 = 8 ∧ acceleratedOrbit 15 30382 = 6085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30382) = 3 ^ 8 * m + 6085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30382.1, data_15_30382.2]

/-- Complete interval computation for depth 15, residue 30383. -/
theorem bounds_15_30383 : exactInterval 15 30383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30383 : oddCount 30383 15 = 11 ∧ acceleratedOrbit 15 30383 = 164267 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30383) = 3 ^ 11 * m + 164267 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30383.1, data_15_30383.2]

/-- Complete interval computation for depth 15, residue 30384. -/
theorem bounds_15_30384 : exactInterval 15 30384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30384 : oddCount 30384 15 = 6 ∧ acceleratedOrbit 15 30384 = 677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30384) = 3 ^ 6 * m + 677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30384.1, data_15_30384.2]

/-- Complete interval computation for depth 15, residue 30385. -/
theorem bounds_15_30385 : exactInterval 15 30385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30385 : oddCount 30385 15 = 6 ∧ acceleratedOrbit 15 30385 = 677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30385) = 3 ^ 6 * m + 677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30385.1, data_15_30385.2]

/-- Complete interval computation for depth 15, residue 30386. -/
theorem bounds_15_30386 : exactInterval 15 30386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30386 : oddCount 30386 15 = 6 ∧ acceleratedOrbit 15 30386 = 677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30386) = 3 ^ 6 * m + 677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30386.1, data_15_30386.2]

/-- Complete interval computation for depth 15, residue 30387. -/
theorem bounds_15_30387 : exactInterval 15 30387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30387 : oddCount 30387 15 = 6 ∧ acceleratedOrbit 15 30387 = 677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30387) = 3 ^ 6 * m + 677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30387.1, data_15_30387.2]

/-- Complete interval computation for depth 15, residue 30388. -/
theorem bounds_15_30388 : exactInterval 15 30388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30388 : oddCount 30388 15 = 6 ∧ acceleratedOrbit 15 30388 = 677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30388) = 3 ^ 6 * m + 677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30388.1, data_15_30388.2]

/-- Complete interval computation for depth 15, residue 30389. -/
theorem bounds_15_30389 : exactInterval 15 30389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30389 : oddCount 30389 15 = 6 ∧ acceleratedOrbit 15 30389 = 677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30389) = 3 ^ 6 * m + 677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30389.1, data_15_30389.2]

/-- Complete interval computation for depth 15, residue 30390. -/
theorem bounds_15_30390 : exactInterval 15 30390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30390 : oddCount 30390 15 = 8 ∧ acceleratedOrbit 15 30390 = 6086 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30390) = 3 ^ 8 * m + 6086 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30390.1, data_15_30390.2]

/-- Complete interval computation for depth 15, residue 30391. -/
theorem bounds_15_30391 : exactInterval 15 30391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30391 : oddCount 30391 15 = 8 ∧ acceleratedOrbit 15 30391 = 6086 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30391) = 3 ^ 8 * m + 6086 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30391.1, data_15_30391.2]

/-- Complete interval computation for depth 15, residue 30392. -/
theorem bounds_15_30392 : exactInterval 15 30392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30392 : oddCount 30392 15 = 6 ∧ acceleratedOrbit 15 30392 = 677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30392) = 3 ^ 6 * m + 677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30392.1, data_15_30392.2]

/-- Complete interval computation for depth 15, residue 30393. -/
theorem bounds_15_30393 : exactInterval 15 30393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30393 : oddCount 30393 15 = 7 ∧ acceleratedOrbit 15 30393 = 2029 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30393) = 3 ^ 7 * m + 2029 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30393.1, data_15_30393.2]

/-- Complete interval computation for depth 15, residue 30394. -/
theorem bounds_15_30394 : exactInterval 15 30394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30394 : oddCount 30394 15 = 6 ∧ acceleratedOrbit 15 30394 = 677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30394) = 3 ^ 6 * m + 677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30394.1, data_15_30394.2]

/-- Complete interval computation for depth 15, residue 30395. -/
theorem bounds_15_30395 : exactInterval 15 30395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30395 : oddCount 30395 15 = 7 ∧ acceleratedOrbit 15 30395 = 2029 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30395) = 3 ^ 7 * m + 2029 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30395.1, data_15_30395.2]

/-- Complete interval computation for depth 15, residue 30396. -/
theorem bounds_15_30396 : exactInterval 15 30396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30396 : oddCount 30396 15 = 8 ∧ acceleratedOrbit 15 30396 = 6088 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30396) = 3 ^ 8 * m + 6088 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30396.1, data_15_30396.2]

/-- Complete interval computation for depth 15, residue 30397. -/
theorem bounds_15_30397 : exactInterval 15 30397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30397 : oddCount 30397 15 = 8 ∧ acceleratedOrbit 15 30397 = 6088 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30397) = 3 ^ 8 * m + 6088 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30397.1, data_15_30397.2]

/-- Complete interval computation for depth 15, residue 30398. -/
theorem bounds_15_30398 : exactInterval 15 30398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30398 : oddCount 30398 15 = 8 ∧ acceleratedOrbit 15 30398 = 6088 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30398) = 3 ^ 8 * m + 6088 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30398.1, data_15_30398.2]

/-- Complete interval computation for depth 15, residue 30399. -/
theorem bounds_15_30399 : exactInterval 15 30399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30399 : oddCount 30399 15 = 11 ∧ acceleratedOrbit 15 30399 = 164348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30399) = 3 ^ 11 * m + 164348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30399.1, data_15_30399.2]

/-- Complete interval computation for depth 15, residue 30400. -/
theorem bounds_15_30400 : exactInterval 15 30400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30400 : oddCount 30400 15 = 5 ∧ acceleratedOrbit 15 30400 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30400) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30400.1, data_15_30400.2]

/-- Complete interval computation for depth 15, residue 30401. -/
theorem bounds_15_30401 : exactInterval 15 30401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30401 : oddCount 30401 15 = 6 ∧ acceleratedOrbit 15 30401 = 677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30401) = 3 ^ 6 * m + 677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30401.1, data_15_30401.2]

/-- Complete interval computation for depth 15, residue 30402. -/
theorem bounds_15_30402 : exactInterval 15 30402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30402 : oddCount 30402 15 = 10 ∧ acceleratedOrbit 15 30402 = 54796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30402) = 3 ^ 10 * m + 54796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30402.1, data_15_30402.2]

/-- Complete interval computation for depth 15, residue 30403. -/
theorem bounds_15_30403 : exactInterval 15 30403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30403 : oddCount 30403 15 = 10 ∧ acceleratedOrbit 15 30403 = 54796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30403) = 3 ^ 10 * m + 54796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30403.1, data_15_30403.2]

/-- Complete interval computation for depth 15, residue 30404. -/
theorem bounds_15_30404 : exactInterval 15 30404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30404 : oddCount 30404 15 = 5 ∧ acceleratedOrbit 15 30404 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30404) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30404.1, data_15_30404.2]

/-- Complete interval computation for depth 15, residue 30405. -/
theorem bounds_15_30405 : exactInterval 15 30405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30405 : oddCount 30405 15 = 5 ∧ acceleratedOrbit 15 30405 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30405) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30405.1, data_15_30405.2]

/-- Complete interval computation for depth 15, residue 30406. -/
theorem bounds_15_30406 : exactInterval 15 30406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30406 : oddCount 30406 15 = 5 ∧ acceleratedOrbit 15 30406 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30406) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30406.1, data_15_30406.2]

/-- Complete interval computation for depth 15, residue 30407. -/
theorem bounds_15_30407 : exactInterval 15 30407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30407 : oddCount 30407 15 = 6 ∧ acceleratedOrbit 15 30407 = 677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30407) = 3 ^ 6 * m + 677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30407.1, data_15_30407.2]

end Collatz.Research.PassageAtlas.Batch0928
