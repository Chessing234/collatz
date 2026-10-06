import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0136

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4423. -/
theorem bounds_15_4423 : exactInterval 15 4423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4423 : oddCount 4423 15 = 11 ∧ acceleratedOrbit 15 4423 = 23921 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4423) = 3 ^ 11 * m + 23921 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4423.1, data_15_4423.2]

/-- Complete interval computation for depth 15, residue 4424. -/
theorem bounds_15_4424 : exactInterval 15 4424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4424 : oddCount 4424 15 = 9 ∧ acceleratedOrbit 15 4424 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4424) = 3 ^ 9 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4424.1, data_15_4424.2]

/-- Complete interval computation for depth 15, residue 4425. -/
theorem bounds_15_4425 : exactInterval 15 4425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4425 : oddCount 4425 15 = 7 ∧ acceleratedOrbit 15 4425 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4425) = 3 ^ 7 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4425.1, data_15_4425.2]

/-- Complete interval computation for depth 15, residue 4426. -/
theorem bounds_15_4426 : exactInterval 15 4426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4426 : oddCount 4426 15 = 9 ∧ acceleratedOrbit 15 4426 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4426) = 3 ^ 9 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4426.1, data_15_4426.2]

/-- Complete interval computation for depth 15, residue 4427. -/
theorem bounds_15_4427 : exactInterval 15 4427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4427 : oddCount 4427 15 = 8 ∧ acceleratedOrbit 15 4427 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4427) = 3 ^ 8 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4427.1, data_15_4427.2]

/-- Complete interval computation for depth 15, residue 4428. -/
theorem bounds_15_4428 : exactInterval 15 4428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4428 : oddCount 4428 15 = 9 ∧ acceleratedOrbit 15 4428 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4428) = 3 ^ 9 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4428.1, data_15_4428.2]

/-- Complete interval computation for depth 15, residue 4429. -/
theorem bounds_15_4429 : exactInterval 15 4429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4429 : oddCount 4429 15 = 9 ∧ acceleratedOrbit 15 4429 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4429) = 3 ^ 9 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4429.1, data_15_4429.2]

/-- Complete interval computation for depth 15, residue 4430. -/
theorem bounds_15_4430 : exactInterval 15 4430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4430 : oddCount 4430 15 = 11 ∧ acceleratedOrbit 15 4430 = 23966 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4430) = 3 ^ 11 * m + 23966 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4430.1, data_15_4430.2]

/-- Complete interval computation for depth 15, residue 4431. -/
theorem bounds_15_4431 : exactInterval 15 4431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4431 : oddCount 4431 15 = 11 ∧ acceleratedOrbit 15 4431 = 23966 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4431) = 3 ^ 11 * m + 23966 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4431.1, data_15_4431.2]

/-- Complete interval computation for depth 15, residue 4432. -/
theorem bounds_15_4432 : exactInterval 15 4432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4432 : oddCount 4432 15 = 3 ∧ acceleratedOrbit 15 4432 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4432) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4432.1, data_15_4432.2]

/-- Complete interval computation for depth 15, residue 4433. -/
theorem bounds_15_4433 : exactInterval 15 4433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4433 : oddCount 4433 15 = 9 ∧ acceleratedOrbit 15 4433 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4433) = 3 ^ 9 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4433.1, data_15_4433.2]

/-- Complete interval computation for depth 15, residue 4434. -/
theorem bounds_15_4434 : exactInterval 15 4434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4434 : oddCount 4434 15 = 11 ∧ acceleratedOrbit 15 4434 = 23989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4434) = 3 ^ 11 * m + 23989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4434.1, data_15_4434.2]

/-- Complete interval computation for depth 15, residue 4435. -/
theorem bounds_15_4435 : exactInterval 15 4435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4435 : oddCount 4435 15 = 11 ∧ acceleratedOrbit 15 4435 = 23989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4435) = 3 ^ 11 * m + 23989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4435.1, data_15_4435.2]

/-- Complete interval computation for depth 15, residue 4436. -/
theorem bounds_15_4436 : exactInterval 15 4436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4436 : oddCount 4436 15 = 3 ∧ acceleratedOrbit 15 4436 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4436) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4436.1, data_15_4436.2]

/-- Complete interval computation for depth 15, residue 4437. -/
theorem bounds_15_4437 : exactInterval 15 4437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4437 : oddCount 4437 15 = 3 ∧ acceleratedOrbit 15 4437 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4437) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4437.1, data_15_4437.2]

/-- Complete interval computation for depth 15, residue 4438. -/
theorem bounds_15_4438 : exactInterval 15 4438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4438 : oddCount 4438 15 = 9 ∧ acceleratedOrbit 15 4438 = 2672 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4438) = 3 ^ 9 * m + 2672 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4438.1, data_15_4438.2]

/-- Complete interval computation for depth 15, residue 4439. -/
theorem bounds_15_4439 : exactInterval 15 4439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4439 : oddCount 4439 15 = 9 ∧ acceleratedOrbit 15 4439 = 2672 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4439) = 3 ^ 9 * m + 2672 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4439.1, data_15_4439.2]

/-- Complete interval computation for depth 15, residue 4440. -/
theorem bounds_15_4440 : exactInterval 15 4440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4440 : oddCount 4440 15 = 4 ∧ acceleratedOrbit 15 4440 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4440) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4440.1, data_15_4440.2]

/-- Complete interval computation for depth 15, residue 4441. -/
theorem bounds_15_4441 : exactInterval 15 4441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4441 : oddCount 4441 15 = 10 ∧ acceleratedOrbit 15 4441 = 8018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4441) = 3 ^ 10 * m + 8018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4441.1, data_15_4441.2]

/-- Complete interval computation for depth 15, residue 4442. -/
theorem bounds_15_4442 : exactInterval 15 4442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4442 : oddCount 4442 15 = 4 ∧ acceleratedOrbit 15 4442 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4442) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4442.1, data_15_4442.2]

/-- Complete interval computation for depth 15, residue 4443. -/
theorem bounds_15_4443 : exactInterval 15 4443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4443 : oddCount 4443 15 = 9 ∧ acceleratedOrbit 15 4443 = 2672 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4443) = 3 ^ 9 * m + 2672 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4443.1, data_15_4443.2]

/-- Complete interval computation for depth 15, residue 4444. -/
theorem bounds_15_4444 : exactInterval 15 4444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4444 : oddCount 4444 15 = 4 ∧ acceleratedOrbit 15 4444 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4444) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4444.1, data_15_4444.2]

/-- Complete interval computation for depth 15, residue 4445. -/
theorem bounds_15_4445 : exactInterval 15 4445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4445 : oddCount 4445 15 = 4 ∧ acceleratedOrbit 15 4445 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4445) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4445.1, data_15_4445.2]

/-- Complete interval computation for depth 15, residue 4446. -/
theorem bounds_15_4446 : exactInterval 15 4446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4446 : oddCount 4446 15 = 11 ∧ acceleratedOrbit 15 4446 = 24056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4446) = 3 ^ 11 * m + 24056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4446.1, data_15_4446.2]

/-- Complete interval computation for depth 15, residue 4447. -/
theorem bounds_15_4447 : exactInterval 15 4447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4447 : oddCount 4447 15 = 11 ∧ acceleratedOrbit 15 4447 = 24056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4447) = 3 ^ 11 * m + 24056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4447.1, data_15_4447.2]

/-- Complete interval computation for depth 15, residue 4448. -/
theorem bounds_15_4448 : exactInterval 15 4448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4448 : oddCount 4448 15 = 6 ∧ acceleratedOrbit 15 4448 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4448) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4448.1, data_15_4448.2]

/-- Complete interval computation for depth 15, residue 4449. -/
theorem bounds_15_4449 : exactInterval 15 4449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4449 : oddCount 4449 15 = 9 ∧ acceleratedOrbit 15 4449 = 2675 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4449) = 3 ^ 9 * m + 2675 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4449.1, data_15_4449.2]

/-- Complete interval computation for depth 15, residue 4450. -/
theorem bounds_15_4450 : exactInterval 15 4450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4450 : oddCount 4450 15 = 7 ∧ acceleratedOrbit 15 4450 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4450) = 3 ^ 7 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4450.1, data_15_4450.2]

/-- Complete interval computation for depth 15, residue 4451. -/
theorem bounds_15_4451 : exactInterval 15 4451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4451 : oddCount 4451 15 = 7 ∧ acceleratedOrbit 15 4451 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4451) = 3 ^ 7 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4451.1, data_15_4451.2]

/-- Complete interval computation for depth 15, residue 4452. -/
theorem bounds_15_4452 : exactInterval 15 4452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4452 : oddCount 4452 15 = 7 ∧ acceleratedOrbit 15 4452 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4452) = 3 ^ 7 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4452.1, data_15_4452.2]

/-- Complete interval computation for depth 15, residue 4453. -/
theorem bounds_15_4453 : exactInterval 15 4453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4453 : oddCount 4453 15 = 7 ∧ acceleratedOrbit 15 4453 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4453) = 3 ^ 7 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4453.1, data_15_4453.2]

/-- Complete interval computation for depth 15, residue 4454. -/
theorem bounds_15_4454 : exactInterval 15 4454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4454 : oddCount 4454 15 = 7 ∧ acceleratedOrbit 15 4454 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4454) = 3 ^ 7 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4454.1, data_15_4454.2]

/-- Complete interval computation for depth 15, residue 4455. -/
theorem bounds_15_4455 : exactInterval 15 4455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4455 : oddCount 4455 15 = 9 ∧ acceleratedOrbit 15 4455 = 2677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4455) = 3 ^ 9 * m + 2677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4455.1, data_15_4455.2]

end Collatz.Research.PassageAtlas.Batch0136
