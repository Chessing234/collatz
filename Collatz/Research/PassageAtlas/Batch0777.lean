import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0777

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25427. -/
theorem bounds_15_25427 : exactInterval 15 25427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25427 : oddCount 25427 15 = 9 ∧ acceleratedOrbit 15 25427 = 15275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25427) = 3 ^ 9 * m + 15275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25427.1, data_15_25427.2]

/-- Complete interval computation for depth 15, residue 25428. -/
theorem bounds_15_25428 : exactInterval 15 25428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25428 : oddCount 25428 15 = 2 ∧ acceleratedOrbit 15 25428 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25428) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25428.1, data_15_25428.2]

/-- Complete interval computation for depth 15, residue 25429. -/
theorem bounds_15_25429 : exactInterval 15 25429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25429 : oddCount 25429 15 = 2 ∧ acceleratedOrbit 15 25429 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25429) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25429.1, data_15_25429.2]

/-- Complete interval computation for depth 15, residue 25430. -/
theorem bounds_15_25430 : exactInterval 15 25430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25430 : oddCount 25430 15 = 10 ∧ acceleratedOrbit 15 25430 = 45836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25430) = 3 ^ 10 * m + 45836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25430.1, data_15_25430.2]

/-- Complete interval computation for depth 15, residue 25431. -/
theorem bounds_15_25431 : exactInterval 15 25431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25431 : oddCount 25431 15 = 10 ∧ acceleratedOrbit 15 25431 = 45836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25431) = 3 ^ 10 * m + 45836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25431.1, data_15_25431.2]

/-- Complete interval computation for depth 15, residue 25432. -/
theorem bounds_15_25432 : exactInterval 15 25432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25432 : oddCount 25432 15 = 8 ∧ acceleratedOrbit 15 25432 = 5096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25432) = 3 ^ 8 * m + 5096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25432.1, data_15_25432.2]

/-- Complete interval computation for depth 15, residue 25433. -/
theorem bounds_15_25433 : exactInterval 15 25433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25433 : oddCount 25433 15 = 7 ∧ acceleratedOrbit 15 25433 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25433) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25433.1, data_15_25433.2]

/-- Complete interval computation for depth 15, residue 25434. -/
theorem bounds_15_25434 : exactInterval 15 25434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25434 : oddCount 25434 15 = 8 ∧ acceleratedOrbit 15 25434 = 5096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25434) = 3 ^ 8 * m + 5096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25434.1, data_15_25434.2]

/-- Complete interval computation for depth 15, residue 25435. -/
theorem bounds_15_25435 : exactInterval 15 25435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25435 : oddCount 25435 15 = 10 ∧ acceleratedOrbit 15 25435 = 45839 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25435) = 3 ^ 10 * m + 45839 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25435.1, data_15_25435.2]

/-- Complete interval computation for depth 15, residue 25436. -/
theorem bounds_15_25436 : exactInterval 15 25436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25436 : oddCount 25436 15 = 8 ∧ acceleratedOrbit 15 25436 = 5096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25436) = 3 ^ 8 * m + 5096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25436.1, data_15_25436.2]

/-- Complete interval computation for depth 15, residue 25437. -/
theorem bounds_15_25437 : exactInterval 15 25437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25437 : oddCount 25437 15 = 8 ∧ acceleratedOrbit 15 25437 = 5096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25437) = 3 ^ 8 * m + 5096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25437.1, data_15_25437.2]

/-- Complete interval computation for depth 15, residue 25438. -/
theorem bounds_15_25438 : exactInterval 15 25438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25438 : oddCount 25438 15 = 6 ∧ acceleratedOrbit 15 25438 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25438) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25438.1, data_15_25438.2]

/-- Complete interval computation for depth 15, residue 25439. -/
theorem bounds_15_25439 : exactInterval 15 25439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25439 : oddCount 25439 15 = 6 ∧ acceleratedOrbit 15 25439 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25439) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25439.1, data_15_25439.2]

/-- Complete interval computation for depth 15, residue 25440. -/
theorem bounds_15_25440 : exactInterval 15 25440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25440 : oddCount 25440 15 = 9 ∧ acceleratedOrbit 15 25440 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25440) = 3 ^ 9 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25440.1, data_15_25440.2]

/-- Complete interval computation for depth 15, residue 25441. -/
theorem bounds_15_25441 : exactInterval 15 25441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25441 : oddCount 25441 15 = 9 ∧ acceleratedOrbit 15 25441 = 15284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25441) = 3 ^ 9 * m + 15284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25441.1, data_15_25441.2]

/-- Complete interval computation for depth 15, residue 25442. -/
theorem bounds_15_25442 : exactInterval 15 25442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25442 : oddCount 25442 15 = 8 ∧ acceleratedOrbit 15 25442 = 5102 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25442) = 3 ^ 8 * m + 5102 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25442.1, data_15_25442.2]

/-- Complete interval computation for depth 15, residue 25443. -/
theorem bounds_15_25443 : exactInterval 15 25443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25443 : oddCount 25443 15 = 8 ∧ acceleratedOrbit 15 25443 = 5102 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25443) = 3 ^ 8 * m + 5102 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25443.1, data_15_25443.2]

/-- Complete interval computation for depth 15, residue 25444. -/
theorem bounds_15_25444 : exactInterval 15 25444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25444 : oddCount 25444 15 = 8 ∧ acceleratedOrbit 15 25444 = 5102 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25444) = 3 ^ 8 * m + 5102 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25444.1, data_15_25444.2]

/-- Complete interval computation for depth 15, residue 25445. -/
theorem bounds_15_25445 : exactInterval 15 25445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25445 : oddCount 25445 15 = 8 ∧ acceleratedOrbit 15 25445 = 5102 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25445) = 3 ^ 8 * m + 5102 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25445.1, data_15_25445.2]

/-- Complete interval computation for depth 15, residue 25446. -/
theorem bounds_15_25446 : exactInterval 15 25446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25446 : oddCount 25446 15 = 8 ∧ acceleratedOrbit 15 25446 = 5102 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25446) = 3 ^ 8 * m + 5102 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25446.1, data_15_25446.2]

/-- Complete interval computation for depth 15, residue 25447. -/
theorem bounds_15_25447 : exactInterval 15 25447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25447 : oddCount 25447 15 = 11 ∧ acceleratedOrbit 15 25447 = 137576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25447) = 3 ^ 11 * m + 137576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25447.1, data_15_25447.2]

/-- Complete interval computation for depth 15, residue 25448. -/
theorem bounds_15_25448 : exactInterval 15 25448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25448 : oddCount 25448 15 = 9 ∧ acceleratedOrbit 15 25448 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25448) = 3 ^ 9 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25448.1, data_15_25448.2]

/-- Complete interval computation for depth 15, residue 25449. -/
theorem bounds_15_25449 : exactInterval 15 25449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25449 : oddCount 25449 15 = 10 ∧ acceleratedOrbit 15 25449 = 45866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25449) = 3 ^ 10 * m + 45866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25449.1, data_15_25449.2]

/-- Complete interval computation for depth 15, residue 25450. -/
theorem bounds_15_25450 : exactInterval 15 25450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25450 : oddCount 25450 15 = 9 ∧ acceleratedOrbit 15 25450 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25450) = 3 ^ 9 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25450.1, data_15_25450.2]

/-- Complete interval computation for depth 15, residue 25451. -/
theorem bounds_15_25451 : exactInterval 15 25451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25451 : oddCount 25451 15 = 7 ∧ acceleratedOrbit 15 25451 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25451) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25451.1, data_15_25451.2]

/-- Complete interval computation for depth 15, residue 25452. -/
theorem bounds_15_25452 : exactInterval 15 25452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25452 : oddCount 25452 15 = 8 ∧ acceleratedOrbit 15 25452 = 5098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25452) = 3 ^ 8 * m + 5098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25452.1, data_15_25452.2]

/-- Complete interval computation for depth 15, residue 25453. -/
theorem bounds_15_25453 : exactInterval 15 25453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25453 : oddCount 25453 15 = 8 ∧ acceleratedOrbit 15 25453 = 5098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25453) = 3 ^ 8 * m + 5098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25453.1, data_15_25453.2]

/-- Complete interval computation for depth 15, residue 25454. -/
theorem bounds_15_25454 : exactInterval 15 25454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25454 : oddCount 25454 15 = 8 ∧ acceleratedOrbit 15 25454 = 5098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25454) = 3 ^ 8 * m + 5098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25454.1, data_15_25454.2]

/-- Complete interval computation for depth 15, residue 25455. -/
theorem bounds_15_25455 : exactInterval 15 25455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25455 : oddCount 25455 15 = 7 ∧ acceleratedOrbit 15 25455 = 1699 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25455) = 3 ^ 7 * m + 1699 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25455.1, data_15_25455.2]

/-- Complete interval computation for depth 15, residue 25456. -/
theorem bounds_15_25456 : exactInterval 15 25456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25456 : oddCount 25456 15 = 9 ∧ acceleratedOrbit 15 25456 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25456) = 3 ^ 9 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25456.1, data_15_25456.2]

/-- Complete interval computation for depth 15, residue 25457. -/
theorem bounds_15_25457 : exactInterval 15 25457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25457 : oddCount 25457 15 = 9 ∧ acceleratedOrbit 15 25457 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25457) = 3 ^ 9 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25457.1, data_15_25457.2]

/-- Complete interval computation for depth 15, residue 25458. -/
theorem bounds_15_25458 : exactInterval 15 25458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25458 : oddCount 25458 15 = 8 ∧ acceleratedOrbit 15 25458 = 5102 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25458) = 3 ^ 8 * m + 5102 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25458.1, data_15_25458.2]

/-- Complete interval computation for depth 15, residue 25459. -/
theorem bounds_15_25459 : exactInterval 15 25459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25459 : oddCount 25459 15 = 8 ∧ acceleratedOrbit 15 25459 = 5102 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25459) = 3 ^ 8 * m + 5102 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25459.1, data_15_25459.2]

end Collatz.Research.PassageAtlas.Batch0777
