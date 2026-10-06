import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0166

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5406. -/
theorem bounds_15_5406 : exactInterval 15 5406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5406 : oddCount 5406 15 = 9 ∧ acceleratedOrbit 15 5406 = 3250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5406) = 3 ^ 9 * m + 3250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5406.1, data_15_5406.2]

/-- Complete interval computation for depth 15, residue 5407. -/
theorem bounds_15_5407 : exactInterval 15 5407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5407 : oddCount 5407 15 = 7 ∧ acceleratedOrbit 15 5407 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5407) = 3 ^ 7 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5407.1, data_15_5407.2]

/-- Complete interval computation for depth 15, residue 5408. -/
theorem bounds_15_5408 : exactInterval 15 5408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5408 : oddCount 5408 15 = 8 ∧ acceleratedOrbit 15 5408 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5408) = 3 ^ 8 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5408.1, data_15_5408.2]

/-- Complete interval computation for depth 15, residue 5409. -/
theorem bounds_15_5409 : exactInterval 15 5409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5409 : oddCount 5409 15 = 6 ∧ acceleratedOrbit 15 5409 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5409) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5409.1, data_15_5409.2]

/-- Complete interval computation for depth 15, residue 5410. -/
theorem bounds_15_5410 : exactInterval 15 5410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5410 : oddCount 5410 15 = 7 ∧ acceleratedOrbit 15 5410 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5410) = 3 ^ 7 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5410.1, data_15_5410.2]

/-- Complete interval computation for depth 15, residue 5411. -/
theorem bounds_15_5411 : exactInterval 15 5411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5411 : oddCount 5411 15 = 7 ∧ acceleratedOrbit 15 5411 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5411) = 3 ^ 7 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5411.1, data_15_5411.2]

/-- Complete interval computation for depth 15, residue 5412. -/
theorem bounds_15_5412 : exactInterval 15 5412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5412 : oddCount 5412 15 = 7 ∧ acceleratedOrbit 15 5412 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5412) = 3 ^ 7 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5412.1, data_15_5412.2]

/-- Complete interval computation for depth 15, residue 5413. -/
theorem bounds_15_5413 : exactInterval 15 5413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5413 : oddCount 5413 15 = 7 ∧ acceleratedOrbit 15 5413 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5413) = 3 ^ 7 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5413.1, data_15_5413.2]

/-- Complete interval computation for depth 15, residue 5414. -/
theorem bounds_15_5414 : exactInterval 15 5414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5414 : oddCount 5414 15 = 7 ∧ acceleratedOrbit 15 5414 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5414) = 3 ^ 7 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5414.1, data_15_5414.2]

/-- Complete interval computation for depth 15, residue 5415. -/
theorem bounds_15_5415 : exactInterval 15 5415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5415 : oddCount 5415 15 = 7 ∧ acceleratedOrbit 15 5415 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5415) = 3 ^ 7 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5415.1, data_15_5415.2]

/-- Complete interval computation for depth 15, residue 5416. -/
theorem bounds_15_5416 : exactInterval 15 5416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5416 : oddCount 5416 15 = 8 ∧ acceleratedOrbit 15 5416 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5416) = 3 ^ 8 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5416.1, data_15_5416.2]

/-- Complete interval computation for depth 15, residue 5417. -/
theorem bounds_15_5417 : exactInterval 15 5417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5417 : oddCount 5417 15 = 8 ∧ acceleratedOrbit 15 5417 = 1085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5417) = 3 ^ 8 * m + 1085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5417.1, data_15_5417.2]

/-- Complete interval computation for depth 15, residue 5418. -/
theorem bounds_15_5418 : exactInterval 15 5418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5418 : oddCount 5418 15 = 8 ∧ acceleratedOrbit 15 5418 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5418) = 3 ^ 8 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5418.1, data_15_5418.2]

/-- Complete interval computation for depth 15, residue 5419. -/
theorem bounds_15_5419 : exactInterval 15 5419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5419 : oddCount 5419 15 = 7 ∧ acceleratedOrbit 15 5419 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5419) = 3 ^ 7 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5419.1, data_15_5419.2]

/-- Complete interval computation for depth 15, residue 5420. -/
theorem bounds_15_5420 : exactInterval 15 5420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5420 : oddCount 5420 15 = 7 ∧ acceleratedOrbit 15 5420 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5420) = 3 ^ 7 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5420.1, data_15_5420.2]

/-- Complete interval computation for depth 15, residue 5421. -/
theorem bounds_15_5421 : exactInterval 15 5421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5421 : oddCount 5421 15 = 7 ∧ acceleratedOrbit 15 5421 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5421) = 3 ^ 7 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5421.1, data_15_5421.2]

/-- Complete interval computation for depth 15, residue 5422. -/
theorem bounds_15_5422 : exactInterval 15 5422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5422 : oddCount 5422 15 = 7 ∧ acceleratedOrbit 15 5422 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5422) = 3 ^ 7 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5422.1, data_15_5422.2]

/-- Complete interval computation for depth 15, residue 5423. -/
theorem bounds_15_5423 : exactInterval 15 5423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5423 : oddCount 5423 15 = 10 ∧ acceleratedOrbit 15 5423 = 9776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5423) = 3 ^ 10 * m + 9776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5423.1, data_15_5423.2]

/-- Complete interval computation for depth 15, residue 5424. -/
theorem bounds_15_5424 : exactInterval 15 5424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5424 : oddCount 5424 15 = 8 ∧ acceleratedOrbit 15 5424 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5424) = 3 ^ 8 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5424.1, data_15_5424.2]

/-- Complete interval computation for depth 15, residue 5425. -/
theorem bounds_15_5425 : exactInterval 15 5425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5425 : oddCount 5425 15 = 9 ∧ acceleratedOrbit 15 5425 = 3266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5425) = 3 ^ 9 * m + 3266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5425.1, data_15_5425.2]

/-- Complete interval computation for depth 15, residue 5426. -/
theorem bounds_15_5426 : exactInterval 15 5426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5426 : oddCount 5426 15 = 9 ∧ acceleratedOrbit 15 5426 = 3266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5426) = 3 ^ 9 * m + 3266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5426.1, data_15_5426.2]

/-- Complete interval computation for depth 15, residue 5427. -/
theorem bounds_15_5427 : exactInterval 15 5427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5427 : oddCount 5427 15 = 9 ∧ acceleratedOrbit 15 5427 = 3266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5427) = 3 ^ 9 * m + 3266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5427.1, data_15_5427.2]

/-- Complete interval computation for depth 15, residue 5428. -/
theorem bounds_15_5428 : exactInterval 15 5428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5428 : oddCount 5428 15 = 8 ∧ acceleratedOrbit 15 5428 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5428) = 3 ^ 8 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5428.1, data_15_5428.2]

/-- Complete interval computation for depth 15, residue 5429. -/
theorem bounds_15_5429 : exactInterval 15 5429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5429 : oddCount 5429 15 = 8 ∧ acceleratedOrbit 15 5429 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5429) = 3 ^ 8 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5429.1, data_15_5429.2]

/-- Complete interval computation for depth 15, residue 5430. -/
theorem bounds_15_5430 : exactInterval 15 5430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5430 : oddCount 5430 15 = 10 ∧ acceleratedOrbit 15 5430 = 9791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5430) = 3 ^ 10 * m + 9791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5430.1, data_15_5430.2]

/-- Complete interval computation for depth 15, residue 5431. -/
theorem bounds_15_5431 : exactInterval 15 5431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5431 : oddCount 5431 15 = 10 ∧ acceleratedOrbit 15 5431 = 9791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5431) = 3 ^ 10 * m + 9791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5431.1, data_15_5431.2]

/-- Complete interval computation for depth 15, residue 5432. -/
theorem bounds_15_5432 : exactInterval 15 5432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5432 : oddCount 5432 15 = 8 ∧ acceleratedOrbit 15 5432 = 1090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5432) = 3 ^ 8 * m + 1090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5432.1, data_15_5432.2]

/-- Complete interval computation for depth 15, residue 5433. -/
theorem bounds_15_5433 : exactInterval 15 5433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5433 : oddCount 5433 15 = 10 ∧ acceleratedOrbit 15 5433 = 9796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5433) = 3 ^ 10 * m + 9796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5433.1, data_15_5433.2]

/-- Complete interval computation for depth 15, residue 5434. -/
theorem bounds_15_5434 : exactInterval 15 5434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5434 : oddCount 5434 15 = 8 ∧ acceleratedOrbit 15 5434 = 1090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5434) = 3 ^ 8 * m + 1090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5434.1, data_15_5434.2]

/-- Complete interval computation for depth 15, residue 5435. -/
theorem bounds_15_5435 : exactInterval 15 5435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5435 : oddCount 5435 15 = 7 ∧ acceleratedOrbit 15 5435 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5435) = 3 ^ 7 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5435.1, data_15_5435.2]

/-- Complete interval computation for depth 15, residue 5436. -/
theorem bounds_15_5436 : exactInterval 15 5436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5436 : oddCount 5436 15 = 8 ∧ acceleratedOrbit 15 5436 = 1090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5436) = 3 ^ 8 * m + 1090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5436.1, data_15_5436.2]

/-- Complete interval computation for depth 15, residue 5437. -/
theorem bounds_15_5437 : exactInterval 15 5437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5437 : oddCount 5437 15 = 8 ∧ acceleratedOrbit 15 5437 = 1090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5437) = 3 ^ 8 * m + 1090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5437.1, data_15_5437.2]

/-- Complete interval computation for depth 15, residue 5438. -/
theorem bounds_15_5438 : exactInterval 15 5438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5438 : oddCount 5438 15 = 9 ∧ acceleratedOrbit 15 5438 = 3268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5438) = 3 ^ 9 * m + 3268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5438.1, data_15_5438.2]

end Collatz.Research.PassageAtlas.Batch0166
