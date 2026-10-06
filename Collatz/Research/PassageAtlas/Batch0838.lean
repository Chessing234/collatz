import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0838

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27426. -/
theorem bounds_15_27426 : exactInterval 15 27426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27426 : oddCount 27426 15 = 6 ∧ acceleratedOrbit 15 27426 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27426) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27426.1, data_15_27426.2]

/-- Complete interval computation for depth 15, residue 27427. -/
theorem bounds_15_27427 : exactInterval 15 27427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27427 : oddCount 27427 15 = 6 ∧ acceleratedOrbit 15 27427 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27427) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27427.1, data_15_27427.2]

/-- Complete interval computation for depth 15, residue 27428. -/
theorem bounds_15_27428 : exactInterval 15 27428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27428 : oddCount 27428 15 = 6 ∧ acceleratedOrbit 15 27428 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27428) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27428.1, data_15_27428.2]

/-- Complete interval computation for depth 15, residue 27429. -/
theorem bounds_15_27429 : exactInterval 15 27429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27429 : oddCount 27429 15 = 6 ∧ acceleratedOrbit 15 27429 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27429) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27429.1, data_15_27429.2]

/-- Complete interval computation for depth 15, residue 27430. -/
theorem bounds_15_27430 : exactInterval 15 27430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27430 : oddCount 27430 15 = 6 ∧ acceleratedOrbit 15 27430 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27430) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27430.1, data_15_27430.2]

/-- Complete interval computation for depth 15, residue 27431. -/
theorem bounds_15_27431 : exactInterval 15 27431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27431 : oddCount 27431 15 = 10 ∧ acceleratedOrbit 15 27431 = 49436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27431) = 3 ^ 10 * m + 49436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27431.1, data_15_27431.2]

/-- Complete interval computation for depth 15, residue 27432. -/
theorem bounds_15_27432 : exactInterval 15 27432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27432 : oddCount 27432 15 = 4 ∧ acceleratedOrbit 15 27432 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27432) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27432.1, data_15_27432.2]

/-- Complete interval computation for depth 15, residue 27433. -/
theorem bounds_15_27433 : exactInterval 15 27433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27433 : oddCount 27433 15 = 9 ∧ acceleratedOrbit 15 27433 = 16480 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27433) = 3 ^ 9 * m + 16480 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27433.1, data_15_27433.2]

/-- Complete interval computation for depth 15, residue 27434. -/
theorem bounds_15_27434 : exactInterval 15 27434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27434 : oddCount 27434 15 = 4 ∧ acceleratedOrbit 15 27434 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27434) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27434.1, data_15_27434.2]

/-- Complete interval computation for depth 15, residue 27435. -/
theorem bounds_15_27435 : exactInterval 15 27435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27435 : oddCount 27435 15 = 9 ∧ acceleratedOrbit 15 27435 = 16483 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27435) = 3 ^ 9 * m + 16483 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27435.1, data_15_27435.2]

/-- Complete interval computation for depth 15, residue 27436. -/
theorem bounds_15_27436 : exactInterval 15 27436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27436 : oddCount 27436 15 = 8 ∧ acceleratedOrbit 15 27436 = 5498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27436) = 3 ^ 8 * m + 5498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27436.1, data_15_27436.2]

/-- Complete interval computation for depth 15, residue 27437. -/
theorem bounds_15_27437 : exactInterval 15 27437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27437 : oddCount 27437 15 = 8 ∧ acceleratedOrbit 15 27437 = 5498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27437) = 3 ^ 8 * m + 5498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27437.1, data_15_27437.2]

/-- Complete interval computation for depth 15, residue 27438. -/
theorem bounds_15_27438 : exactInterval 15 27438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27438 : oddCount 27438 15 = 8 ∧ acceleratedOrbit 15 27438 = 5498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27438) = 3 ^ 8 * m + 5498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27438.1, data_15_27438.2]

/-- Complete interval computation for depth 15, residue 27439. -/
theorem bounds_15_27439 : exactInterval 15 27439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27439 : oddCount 27439 15 = 10 ∧ acceleratedOrbit 15 27439 = 49450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27439) = 3 ^ 10 * m + 49450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27439.1, data_15_27439.2]

/-- Complete interval computation for depth 15, residue 27440. -/
theorem bounds_15_27440 : exactInterval 15 27440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27440 : oddCount 27440 15 = 4 ∧ acceleratedOrbit 15 27440 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27440) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27440.1, data_15_27440.2]

/-- Complete interval computation for depth 15, residue 27441. -/
theorem bounds_15_27441 : exactInterval 15 27441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27441 : oddCount 27441 15 = 8 ∧ acceleratedOrbit 15 27441 = 5498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27441) = 3 ^ 8 * m + 5498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27441.1, data_15_27441.2]

/-- Complete interval computation for depth 15, residue 27442. -/
theorem bounds_15_27442 : exactInterval 15 27442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27442 : oddCount 27442 15 = 8 ∧ acceleratedOrbit 15 27442 = 5498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27442) = 3 ^ 8 * m + 5498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27442.1, data_15_27442.2]

/-- Complete interval computation for depth 15, residue 27443. -/
theorem bounds_15_27443 : exactInterval 15 27443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27443 : oddCount 27443 15 = 8 ∧ acceleratedOrbit 15 27443 = 5498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27443) = 3 ^ 8 * m + 5498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27443.1, data_15_27443.2]

/-- Complete interval computation for depth 15, residue 27444. -/
theorem bounds_15_27444 : exactInterval 15 27444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27444 : oddCount 27444 15 = 4 ∧ acceleratedOrbit 15 27444 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27444) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27444.1, data_15_27444.2]

/-- Complete interval computation for depth 15, residue 27445. -/
theorem bounds_15_27445 : exactInterval 15 27445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27445 : oddCount 27445 15 = 4 ∧ acceleratedOrbit 15 27445 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27445) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27445.1, data_15_27445.2]

/-- Complete interval computation for depth 15, residue 27446. -/
theorem bounds_15_27446 : exactInterval 15 27446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27446 : oddCount 27446 15 = 7 ∧ acceleratedOrbit 15 27446 = 1832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27446) = 3 ^ 7 * m + 1832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27446.1, data_15_27446.2]

/-- Complete interval computation for depth 15, residue 27447. -/
theorem bounds_15_27447 : exactInterval 15 27447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27447 : oddCount 27447 15 = 7 ∧ acceleratedOrbit 15 27447 = 1832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27447) = 3 ^ 7 * m + 1832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27447.1, data_15_27447.2]

/-- Complete interval computation for depth 15, residue 27448. -/
theorem bounds_15_27448 : exactInterval 15 27448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27448 : oddCount 27448 15 = 10 ∧ acceleratedOrbit 15 27448 = 49481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27448) = 3 ^ 10 * m + 49481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27448.1, data_15_27448.2]

/-- Complete interval computation for depth 15, residue 27449. -/
theorem bounds_15_27449 : exactInterval 15 27449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27449 : oddCount 27449 15 = 9 ∧ acceleratedOrbit 15 27449 = 16490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27449) = 3 ^ 9 * m + 16490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27449.1, data_15_27449.2]

/-- Complete interval computation for depth 15, residue 27450. -/
theorem bounds_15_27450 : exactInterval 15 27450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27450 : oddCount 27450 15 = 10 ∧ acceleratedOrbit 15 27450 = 49481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27450) = 3 ^ 10 * m + 49481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27450.1, data_15_27450.2]

/-- Complete interval computation for depth 15, residue 27451. -/
theorem bounds_15_27451 : exactInterval 15 27451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27451 : oddCount 27451 15 = 8 ∧ acceleratedOrbit 15 27451 = 5498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27451) = 3 ^ 8 * m + 5498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27451.1, data_15_27451.2]

/-- Complete interval computation for depth 15, residue 27452. -/
theorem bounds_15_27452 : exactInterval 15 27452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27452 : oddCount 27452 15 = 10 ∧ acceleratedOrbit 15 27452 = 49481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27452) = 3 ^ 10 * m + 49481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27452.1, data_15_27452.2]

/-- Complete interval computation for depth 15, residue 27453. -/
theorem bounds_15_27453 : exactInterval 15 27453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27453 : oddCount 27453 15 = 10 ∧ acceleratedOrbit 15 27453 = 49481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27453) = 3 ^ 10 * m + 49481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27453.1, data_15_27453.2]

/-- Complete interval computation for depth 15, residue 27454. -/
theorem bounds_15_27454 : exactInterval 15 27454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27454 : oddCount 27454 15 = 11 ∧ acceleratedOrbit 15 27454 = 148432 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27454) = 3 ^ 11 * m + 148432 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27454.1, data_15_27454.2]

/-- Complete interval computation for depth 15, residue 27455. -/
theorem bounds_15_27455 : exactInterval 15 27455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27455 : oddCount 27455 15 = 11 ∧ acceleratedOrbit 15 27455 = 148432 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27455) = 3 ^ 11 * m + 148432 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27455.1, data_15_27455.2]

/-- Complete interval computation for depth 15, residue 27456. -/
theorem bounds_15_27456 : exactInterval 15 27456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27456 : oddCount 27456 15 = 5 ∧ acceleratedOrbit 15 27456 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27456) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27456.1, data_15_27456.2]

/-- Complete interval computation for depth 15, residue 27457. -/
theorem bounds_15_27457 : exactInterval 15 27457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27457 : oddCount 27457 15 = 4 ∧ acceleratedOrbit 15 27457 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27457) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27457.1, data_15_27457.2]

/-- Complete interval computation for depth 15, residue 27458. -/
theorem bounds_15_27458 : exactInterval 15 27458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27458 : oddCount 27458 15 = 6 ∧ acceleratedOrbit 15 27458 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27458) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27458.1, data_15_27458.2]

end Collatz.Research.PassageAtlas.Batch0838
