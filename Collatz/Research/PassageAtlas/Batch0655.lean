import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0655

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21430. -/
theorem bounds_15_21430 : exactInterval 15 21430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21430 : oddCount 21430 15 = 9 ∧ acceleratedOrbit 15 21430 = 12878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21430) = 3 ^ 9 * m + 12878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21430.1, data_15_21430.2]

/-- Complete interval computation for depth 15, residue 21431. -/
theorem bounds_15_21431 : exactInterval 15 21431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21431 : oddCount 21431 15 = 9 ∧ acceleratedOrbit 15 21431 = 12878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21431) = 3 ^ 9 * m + 12878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21431.1, data_15_21431.2]

/-- Complete interval computation for depth 15, residue 21432. -/
theorem bounds_15_21432 : exactInterval 15 21432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21432 : oddCount 21432 15 = 4 ∧ acceleratedOrbit 15 21432 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21432) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21432.1, data_15_21432.2]

/-- Complete interval computation for depth 15, residue 21433. -/
theorem bounds_15_21433 : exactInterval 15 21433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21433 : oddCount 21433 15 = 10 ∧ acceleratedOrbit 15 21433 = 38636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21433) = 3 ^ 10 * m + 38636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21433.1, data_15_21433.2]

/-- Complete interval computation for depth 15, residue 21434. -/
theorem bounds_15_21434 : exactInterval 15 21434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21434 : oddCount 21434 15 = 4 ∧ acceleratedOrbit 15 21434 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21434) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21434.1, data_15_21434.2]

/-- Complete interval computation for depth 15, residue 21435. -/
theorem bounds_15_21435 : exactInterval 15 21435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21435 : oddCount 21435 15 = 10 ∧ acceleratedOrbit 15 21435 = 38636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21435) = 3 ^ 10 * m + 38636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21435.1, data_15_21435.2]

/-- Complete interval computation for depth 15, residue 21436. -/
theorem bounds_15_21436 : exactInterval 15 21436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21436 : oddCount 21436 15 = 12 ∧ acceleratedOrbit 15 21436 = 347732 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21436) = 3 ^ 12 * m + 347732 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21436.1, data_15_21436.2]

/-- Complete interval computation for depth 15, residue 21437. -/
theorem bounds_15_21437 : exactInterval 15 21437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21437 : oddCount 21437 15 = 12 ∧ acceleratedOrbit 15 21437 = 347732 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21437) = 3 ^ 12 * m + 347732 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21437.1, data_15_21437.2]

/-- Complete interval computation for depth 15, residue 21438. -/
theorem bounds_15_21438 : exactInterval 15 21438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21438 : oddCount 21438 15 = 12 ∧ acceleratedOrbit 15 21438 = 347732 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21438) = 3 ^ 12 * m + 347732 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21438.1, data_15_21438.2]

/-- Complete interval computation for depth 15, residue 21439. -/
theorem bounds_15_21439 : exactInterval 15 21439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21439 : oddCount 21439 15 = 12 ∧ acceleratedOrbit 15 21439 = 347723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21439) = 3 ^ 12 * m + 347723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21439.1, data_15_21439.2]

/-- Complete interval computation for depth 15, residue 21440. -/
theorem bounds_15_21440 : exactInterval 15 21440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21440 : oddCount 21440 15 = 6 ∧ acceleratedOrbit 15 21440 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21440) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21440.1, data_15_21440.2]

/-- Complete interval computation for depth 15, residue 21441. -/
theorem bounds_15_21441 : exactInterval 15 21441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21441 : oddCount 21441 15 = 8 ∧ acceleratedOrbit 15 21441 = 4295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21441) = 3 ^ 8 * m + 4295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21441.1, data_15_21441.2]

/-- Complete interval computation for depth 15, residue 21442. -/
theorem bounds_15_21442 : exactInterval 15 21442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21442 : oddCount 21442 15 = 8 ∧ acceleratedOrbit 15 21442 = 4295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21442) = 3 ^ 8 * m + 4295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21442.1, data_15_21442.2]

/-- Complete interval computation for depth 15, residue 21443. -/
theorem bounds_15_21443 : exactInterval 15 21443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21443 : oddCount 21443 15 = 8 ∧ acceleratedOrbit 15 21443 = 4295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21443) = 3 ^ 8 * m + 4295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21443.1, data_15_21443.2]

/-- Complete interval computation for depth 15, residue 21444. -/
theorem bounds_15_21444 : exactInterval 15 21444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21444 : oddCount 21444 15 = 6 ∧ acceleratedOrbit 15 21444 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21444) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21444.1, data_15_21444.2]

/-- Complete interval computation for depth 15, residue 21445. -/
theorem bounds_15_21445 : exactInterval 15 21445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21445 : oddCount 21445 15 = 6 ∧ acceleratedOrbit 15 21445 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21445) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21445.1, data_15_21445.2]

/-- Complete interval computation for depth 15, residue 21446. -/
theorem bounds_15_21446 : exactInterval 15 21446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21446 : oddCount 21446 15 = 6 ∧ acceleratedOrbit 15 21446 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21446) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21446.1, data_15_21446.2]

/-- Complete interval computation for depth 15, residue 21447. -/
theorem bounds_15_21447 : exactInterval 15 21447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21447 : oddCount 21447 15 = 9 ∧ acceleratedOrbit 15 21447 = 12884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21447) = 3 ^ 9 * m + 12884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21447.1, data_15_21447.2]

/-- Complete interval computation for depth 15, residue 21448. -/
theorem bounds_15_21448 : exactInterval 15 21448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21448 : oddCount 21448 15 = 7 ∧ acceleratedOrbit 15 21448 = 1433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21448) = 3 ^ 7 * m + 1433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21448.1, data_15_21448.2]

/-- Complete interval computation for depth 15, residue 21449. -/
theorem bounds_15_21449 : exactInterval 15 21449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21449 : oddCount 21449 15 = 7 ∧ acceleratedOrbit 15 21449 = 1432 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21449) = 3 ^ 7 * m + 1432 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21449.1, data_15_21449.2]

/-- Complete interval computation for depth 15, residue 21450. -/
theorem bounds_15_21450 : exactInterval 15 21450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21450 : oddCount 21450 15 = 7 ∧ acceleratedOrbit 15 21450 = 1433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21450) = 3 ^ 7 * m + 1433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21450.1, data_15_21450.2]

/-- Complete interval computation for depth 15, residue 21451. -/
theorem bounds_15_21451 : exactInterval 15 21451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21451 : oddCount 21451 15 = 7 ∧ acceleratedOrbit 15 21451 = 1433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21451) = 3 ^ 7 * m + 1433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21451.1, data_15_21451.2]

/-- Complete interval computation for depth 15, residue 21452. -/
theorem bounds_15_21452 : exactInterval 15 21452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21452 : oddCount 21452 15 = 7 ∧ acceleratedOrbit 15 21452 = 1433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21452) = 3 ^ 7 * m + 1433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21452.1, data_15_21452.2]

/-- Complete interval computation for depth 15, residue 21453. -/
theorem bounds_15_21453 : exactInterval 15 21453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21453 : oddCount 21453 15 = 7 ∧ acceleratedOrbit 15 21453 = 1433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21453) = 3 ^ 7 * m + 1433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21453.1, data_15_21453.2]

/-- Complete interval computation for depth 15, residue 21454. -/
theorem bounds_15_21454 : exactInterval 15 21454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21454 : oddCount 21454 15 = 9 ∧ acceleratedOrbit 15 21454 = 12889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21454) = 3 ^ 9 * m + 12889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21454.1, data_15_21454.2]

/-- Complete interval computation for depth 15, residue 21455. -/
theorem bounds_15_21455 : exactInterval 15 21455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21455 : oddCount 21455 15 = 9 ∧ acceleratedOrbit 15 21455 = 12889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21455) = 3 ^ 9 * m + 12889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21455.1, data_15_21455.2]

/-- Complete interval computation for depth 15, residue 21456. -/
theorem bounds_15_21456 : exactInterval 15 21456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21456 : oddCount 21456 15 = 6 ∧ acceleratedOrbit 15 21456 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21456) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21456.1, data_15_21456.2]

/-- Complete interval computation for depth 15, residue 21457. -/
theorem bounds_15_21457 : exactInterval 15 21457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21457 : oddCount 21457 15 = 7 ∧ acceleratedOrbit 15 21457 = 1433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21457) = 3 ^ 7 * m + 1433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21457.1, data_15_21457.2]

/-- Complete interval computation for depth 15, residue 21458. -/
theorem bounds_15_21458 : exactInterval 15 21458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21458 : oddCount 21458 15 = 9 ∧ acceleratedOrbit 15 21458 = 12892 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21458) = 3 ^ 9 * m + 12892 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21458.1, data_15_21458.2]

/-- Complete interval computation for depth 15, residue 21459. -/
theorem bounds_15_21459 : exactInterval 15 21459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21459 : oddCount 21459 15 = 9 ∧ acceleratedOrbit 15 21459 = 12892 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21459) = 3 ^ 9 * m + 12892 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21459.1, data_15_21459.2]

/-- Complete interval computation for depth 15, residue 21460. -/
theorem bounds_15_21460 : exactInterval 15 21460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21460 : oddCount 21460 15 = 6 ∧ acceleratedOrbit 15 21460 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21460) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21460.1, data_15_21460.2]

/-- Complete interval computation for depth 15, residue 21461. -/
theorem bounds_15_21461 : exactInterval 15 21461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21461 : oddCount 21461 15 = 6 ∧ acceleratedOrbit 15 21461 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21461) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21461.1, data_15_21461.2]

/-- Complete interval computation for depth 15, residue 21462. -/
theorem bounds_15_21462 : exactInterval 15 21462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21462 : oddCount 21462 15 = 8 ∧ acceleratedOrbit 15 21462 = 4298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21462) = 3 ^ 8 * m + 4298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21462.1, data_15_21462.2]

end Collatz.Research.PassageAtlas.Batch0655
