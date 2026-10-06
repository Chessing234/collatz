import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0820

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5411. -/
theorem bounds_13_5411 : exactInterval 13 5411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5411 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5411) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5411 : oddCount 5411 13 = 7 ∧ acceleratedOrbit 13 5411 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5411 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5411) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5411.1, data_13_5411.2]

/-- Complete interval computation for depth 13, residue 5412. -/
theorem bounds_13_5412 : exactInterval 13 5412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5412 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5412) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5412 : oddCount 5412 13 = 7 ∧ acceleratedOrbit 13 5412 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5412 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5412) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5412.1, data_13_5412.2]

/-- Complete interval computation for depth 13, residue 5413. -/
theorem bounds_13_5413 : exactInterval 13 5413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5413 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5413) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5413 : oddCount 5413 13 = 7 ∧ acceleratedOrbit 13 5413 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5413 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5413) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5413.1, data_13_5413.2]

/-- Complete interval computation for depth 13, residue 5414. -/
theorem bounds_13_5414 : exactInterval 13 5414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5414 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5414) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5414 : oddCount 5414 13 = 7 ∧ acceleratedOrbit 13 5414 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5414 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5414) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5414.1, data_13_5414.2]

/-- Complete interval computation for depth 13, residue 5415. -/
theorem bounds_13_5415 : exactInterval 13 5415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5415 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5415) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5415 : oddCount 5415 13 = 6 ∧ acceleratedOrbit 13 5415 = 482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5415 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5415) = 3 ^ 6 * m + 482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5415.1, data_13_5415.2]

/-- Complete interval computation for depth 13, residue 5416. -/
theorem bounds_13_5416 : exactInterval 13 5416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5416 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5416) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5416 : oddCount 5416 13 = 7 ∧ acceleratedOrbit 13 5416 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5416 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5416) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5416.1, data_13_5416.2]

/-- Complete interval computation for depth 13, residue 5417. -/
theorem bounds_13_5417 : exactInterval 13 5417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5417 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5417) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5417 : oddCount 5417 13 = 8 ∧ acceleratedOrbit 13 5417 = 4340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5417 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5417) = 3 ^ 8 * m + 4340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5417.1, data_13_5417.2]

/-- Complete interval computation for depth 13, residue 5418. -/
theorem bounds_13_5418 : exactInterval 13 5418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5418 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5418) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5418 : oddCount 5418 13 = 7 ∧ acceleratedOrbit 13 5418 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5418 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5418) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5418.1, data_13_5418.2]

/-- Complete interval computation for depth 13, residue 5419. -/
theorem bounds_13_5419 : exactInterval 13 5419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5419 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5419) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5419 : oddCount 5419 13 = 7 ∧ acceleratedOrbit 13 5419 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5419 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5419) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5419.1, data_13_5419.2]

/-- Complete interval computation for depth 13, residue 5420. -/
theorem bounds_13_5420 : exactInterval 13 5420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5420 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5420) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5420 : oddCount 5420 13 = 6 ∧ acceleratedOrbit 13 5420 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5420 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5420) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5420.1, data_13_5420.2]

/-- Complete interval computation for depth 13, residue 5421. -/
theorem bounds_13_5421 : exactInterval 13 5421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5421 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5421) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5421 : oddCount 5421 13 = 6 ∧ acceleratedOrbit 13 5421 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5421 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5421) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5421.1, data_13_5421.2]

/-- Complete interval computation for depth 13, residue 5422. -/
theorem bounds_13_5422 : exactInterval 13 5422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5422 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5422) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5422 : oddCount 5422 13 = 6 ∧ acceleratedOrbit 13 5422 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5422 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5422) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5422.1, data_13_5422.2]

/-- Complete interval computation for depth 13, residue 5423. -/
theorem bounds_13_5423 : exactInterval 13 5423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5423 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5423) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5423 : oddCount 5423 13 = 9 ∧ acceleratedOrbit 13 5423 = 13034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5423 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5423) = 3 ^ 9 * m + 13034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5423.1, data_13_5423.2]

/-- Complete interval computation for depth 13, residue 5424. -/
theorem bounds_13_5424 : exactInterval 13 5424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5424 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5424) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5424 : oddCount 5424 13 = 7 ∧ acceleratedOrbit 13 5424 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5424 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5424) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5424.1, data_13_5424.2]

/-- Complete interval computation for depth 13, residue 5425. -/
theorem bounds_13_5425 : exactInterval 13 5425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5425 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5425) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5425 : oddCount 5425 13 = 7 ∧ acceleratedOrbit 13 5425 = 1451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5425 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5425) = 3 ^ 7 * m + 1451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5425.1, data_13_5425.2]

/-- Complete interval computation for depth 13, residue 5426. -/
theorem bounds_13_5426 : exactInterval 13 5426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5426 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5426) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5426 : oddCount 5426 13 = 7 ∧ acceleratedOrbit 13 5426 = 1451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5426 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5426) = 3 ^ 7 * m + 1451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5426.1, data_13_5426.2]

end Collatz.Research.StoppingAtlas.Batch0820
