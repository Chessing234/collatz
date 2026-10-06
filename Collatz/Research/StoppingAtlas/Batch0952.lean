import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0952

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7439. -/
theorem bounds_13_7439 : exactInterval 13 7439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7439 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7439) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7439 : oddCount 7439 13 = 7 ∧ acceleratedOrbit 13 7439 = 1988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7439 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7439) = 3 ^ 7 * m + 1988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7439.1, data_13_7439.2]

/-- Complete interval computation for depth 13, residue 7440. -/
theorem bounds_13_7440 : exactInterval 13 7440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7440 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7440) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7440 : oddCount 7440 13 = 4 ∧ acceleratedOrbit 13 7440 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7440 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7440) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7440.1, data_13_7440.2]

/-- Complete interval computation for depth 13, residue 7441. -/
theorem bounds_13_7441 : exactInterval 13 7441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7441 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7441) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7441 : oddCount 7441 13 = 5 ∧ acceleratedOrbit 13 7441 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7441 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7441) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7441.1, data_13_7441.2]

/-- Complete interval computation for depth 13, residue 7442. -/
theorem bounds_13_7442 : exactInterval 13 7442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7442 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7442) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7442 : oddCount 7442 13 = 9 ∧ acceleratedOrbit 13 7442 = 17891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7442 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7442) = 3 ^ 9 * m + 17891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7442.1, data_13_7442.2]

/-- Complete interval computation for depth 13, residue 7443. -/
theorem bounds_13_7443 : exactInterval 13 7443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7443 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7443) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7443 : oddCount 7443 13 = 9 ∧ acceleratedOrbit 13 7443 = 17891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7443 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7443) = 3 ^ 9 * m + 17891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7443.1, data_13_7443.2]

/-- Complete interval computation for depth 13, residue 7444. -/
theorem bounds_13_7444 : exactInterval 13 7444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7444 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7444) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7444 : oddCount 7444 13 = 4 ∧ acceleratedOrbit 13 7444 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7444 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7444) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7444.1, data_13_7444.2]

/-- Complete interval computation for depth 13, residue 7445. -/
theorem bounds_13_7445 : exactInterval 13 7445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7445 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7445) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7445 : oddCount 7445 13 = 4 ∧ acceleratedOrbit 13 7445 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7445 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7445) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7445.1, data_13_7445.2]

/-- Complete interval computation for depth 13, residue 7446. -/
theorem bounds_13_7446 : exactInterval 13 7446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7446 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7446) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7446 : oddCount 7446 13 = 5 ∧ acceleratedOrbit 13 7446 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7446 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7446) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7446.1, data_13_7446.2]

/-- Complete interval computation for depth 13, residue 7447. -/
theorem bounds_13_7447 : exactInterval 13 7447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7447 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7447) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7447 : oddCount 7447 13 = 5 ∧ acceleratedOrbit 13 7447 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7447 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7447) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7447.1, data_13_7447.2]

/-- Complete interval computation for depth 13, residue 7448. -/
theorem bounds_13_7448 : exactInterval 13 7448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7448 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7448) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7448 : oddCount 7448 13 = 4 ∧ acceleratedOrbit 13 7448 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7448 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7448) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7448.1, data_13_7448.2]

/-- Complete interval computation for depth 13, residue 7449. -/
theorem bounds_13_7449 : exactInterval 13 7449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7449 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7449) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7449 : oddCount 7449 13 = 8 ∧ acceleratedOrbit 13 7449 = 5969 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7449 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7449) = 3 ^ 8 * m + 5969 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7449.1, data_13_7449.2]

/-- Complete interval computation for depth 13, residue 7450. -/
theorem bounds_13_7450 : exactInterval 13 7450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7450 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7450) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7450 : oddCount 7450 13 = 4 ∧ acceleratedOrbit 13 7450 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7450 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7450) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7450.1, data_13_7450.2]

/-- Complete interval computation for depth 13, residue 7451. -/
theorem bounds_13_7451 : exactInterval 13 7451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7451 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7451) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7451 : oddCount 7451 13 = 9 ∧ acceleratedOrbit 13 7451 = 17906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7451 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7451) = 3 ^ 9 * m + 17906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7451.1, data_13_7451.2]

/-- Complete interval computation for depth 13, residue 7452. -/
theorem bounds_13_7452 : exactInterval 13 7452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7452 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7452) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7452 : oddCount 7452 13 = 7 ∧ acceleratedOrbit 13 7452 = 1991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7452 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7452) = 3 ^ 7 * m + 1991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7452.1, data_13_7452.2]

/-- Complete interval computation for depth 13, residue 7453. -/
theorem bounds_13_7453 : exactInterval 13 7453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7453 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7453) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7453 : oddCount 7453 13 = 7 ∧ acceleratedOrbit 13 7453 = 1991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7453 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7453) = 3 ^ 7 * m + 1991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7453.1, data_13_7453.2]

end Collatz.Research.StoppingAtlas.Batch0952
