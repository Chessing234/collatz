import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch094

/-- Complete interval computation for depth 9, residue 440. -/
theorem bounds_9_440 : exactInterval 9 440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_440 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 440) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_440 : oddCount 440 9 = 4 ∧ acceleratedOrbit 9 440 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_440 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 440) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_440.1, data_9_440.2]

/-- Complete interval computation for depth 9, residue 441. -/
theorem bounds_9_441 : exactInterval 9 441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_441 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 441) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_441 : oddCount 441 9 = 4 ∧ acceleratedOrbit 9 441 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_441 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 441) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_441.1, data_9_441.2]

/-- Complete interval computation for depth 9, residue 442. -/
theorem bounds_9_442 : exactInterval 9 442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_442 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 442) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_442 : oddCount 442 9 = 4 ∧ acceleratedOrbit 9 442 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_442 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 442) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_442.1, data_9_442.2]

/-- Complete interval computation for depth 9, residue 443. -/
theorem bounds_9_443 : exactInterval 9 443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_443 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 443) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_443 : oddCount 443 9 = 5 ∧ acceleratedOrbit 9 443 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_443 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 443) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_443.1, data_9_443.2]

/-- Complete interval computation for depth 9, residue 444. -/
theorem bounds_9_444 : exactInterval 9 444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_444 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 444) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_444 : oddCount 444 9 = 6 ∧ acceleratedOrbit 9 444 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_444 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 444) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_444.1, data_9_444.2]

/-- Complete interval computation for depth 9, residue 445. -/
theorem bounds_9_445 : exactInterval 9 445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_445 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 445) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_445 : oddCount 445 9 = 6 ∧ acceleratedOrbit 9 445 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_445 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 445) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_445.1, data_9_445.2]

/-- Complete interval computation for depth 9, residue 446. -/
theorem bounds_9_446 : exactInterval 9 446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_446 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 446) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_446 : oddCount 446 9 = 6 ∧ acceleratedOrbit 9 446 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_446 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 446) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_446.1, data_9_446.2]

/-- Complete interval computation for depth 9, residue 447. -/
theorem bounds_9_447 : exactInterval 9 447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_447 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 447) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_447 : oddCount 447 9 = 8 ∧ acceleratedOrbit 9 447 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_447 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 447) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_447.1, data_9_447.2]

/-- Complete interval computation for depth 9, residue 448. -/
theorem bounds_9_448 : exactInterval 9 448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_448 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 448) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_448 : oddCount 448 9 = 3 ∧ acceleratedOrbit 9 448 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_448 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 448) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_448.1, data_9_448.2]

/-- Complete interval computation for depth 9, residue 449. -/
theorem bounds_9_449 : exactInterval 9 449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_449 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 449) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_449 : oddCount 449 9 = 5 ∧ acceleratedOrbit 9 449 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_449 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 449) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_449.1, data_9_449.2]

end Collatz.Research.DescentIntervals.Batch094
