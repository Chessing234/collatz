import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0951

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7424. -/
theorem bounds_13_7424 : exactInterval 13 7424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7424 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7424) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7424 : oddCount 7424 13 = 3 ∧ acceleratedOrbit 13 7424 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7424 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7424) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7424.1, data_13_7424.2]

/-- Complete interval computation for depth 13, residue 7425. -/
theorem bounds_13_7425 : exactInterval 13 7425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7425 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7425) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7425 : oddCount 7425 13 = 7 ∧ acceleratedOrbit 13 7425 = 1984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7425 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7425) = 3 ^ 7 * m + 1984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7425.1, data_13_7425.2]

/-- Complete interval computation for depth 13, residue 7426. -/
theorem bounds_13_7426 : exactInterval 13 7426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7426 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7426) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7426 : oddCount 7426 13 = 8 ∧ acceleratedOrbit 13 7426 = 5953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7426 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7426) = 3 ^ 8 * m + 5953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7426.1, data_13_7426.2]

/-- Complete interval computation for depth 13, residue 7427. -/
theorem bounds_13_7427 : exactInterval 13 7427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7427 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7427) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7427 : oddCount 7427 13 = 8 ∧ acceleratedOrbit 13 7427 = 5953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7427 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7427) = 3 ^ 8 * m + 5953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7427.1, data_13_7427.2]

/-- Complete interval computation for depth 13, residue 7428. -/
theorem bounds_13_7428 : exactInterval 13 7428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7428 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7428) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7428 : oddCount 7428 13 = 4 ∧ acceleratedOrbit 13 7428 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7428 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7428) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7428.1, data_13_7428.2]

/-- Complete interval computation for depth 13, residue 7429. -/
theorem bounds_13_7429 : exactInterval 13 7429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7429 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7429) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7429 : oddCount 7429 13 = 4 ∧ acceleratedOrbit 13 7429 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7429 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7429) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7429.1, data_13_7429.2]

/-- Complete interval computation for depth 13, residue 7430. -/
theorem bounds_13_7430 : exactInterval 13 7430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7430 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7430) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7430 : oddCount 7430 13 = 4 ∧ acceleratedOrbit 13 7430 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7430 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7430) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7430.1, data_13_7430.2]

/-- Complete interval computation for depth 13, residue 7431. -/
theorem bounds_13_7431 : exactInterval 13 7431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7431 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7431) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7431 : oddCount 7431 13 = 9 ∧ acceleratedOrbit 13 7431 = 17860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7431 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7431) = 3 ^ 9 * m + 17860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7431.1, data_13_7431.2]

/-- Complete interval computation for depth 13, residue 7432. -/
theorem bounds_13_7432 : exactInterval 13 7432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7432 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7432) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7432 : oddCount 7432 13 = 5 ∧ acceleratedOrbit 13 7432 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7432 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7432) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7432.1, data_13_7432.2]

/-- Complete interval computation for depth 13, residue 7433. -/
theorem bounds_13_7433 : exactInterval 13 7433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7433 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7433) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7433 : oddCount 7433 13 = 7 ∧ acceleratedOrbit 13 7433 = 1985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7433 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7433) = 3 ^ 7 * m + 1985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7433.1, data_13_7433.2]

/-- Complete interval computation for depth 13, residue 7434. -/
theorem bounds_13_7434 : exactInterval 13 7434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7434 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7434) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7434 : oddCount 7434 13 = 5 ∧ acceleratedOrbit 13 7434 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7434 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7434) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7434.1, data_13_7434.2]

/-- Complete interval computation for depth 13, residue 7435. -/
theorem bounds_13_7435 : exactInterval 13 7435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7435 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7435) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7435 : oddCount 7435 13 = 6 ∧ acceleratedOrbit 13 7435 = 662 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7435 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7435) = 3 ^ 6 * m + 662 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7435.1, data_13_7435.2]

/-- Complete interval computation for depth 13, residue 7436. -/
theorem bounds_13_7436 : exactInterval 13 7436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7436 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7436) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7436 : oddCount 7436 13 = 5 ∧ acceleratedOrbit 13 7436 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7436 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7436) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7436.1, data_13_7436.2]

/-- Complete interval computation for depth 13, residue 7437. -/
theorem bounds_13_7437 : exactInterval 13 7437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7437 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7437) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7437 : oddCount 7437 13 = 5 ∧ acceleratedOrbit 13 7437 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7437 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7437) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7437.1, data_13_7437.2]

/-- Complete interval computation for depth 13, residue 7438. -/
theorem bounds_13_7438 : exactInterval 13 7438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7438 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7438) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7438 : oddCount 7438 13 = 7 ∧ acceleratedOrbit 13 7438 = 1988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7438 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7438) = 3 ^ 7 * m + 1988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7438.1, data_13_7438.2]

end Collatz.Research.StoppingAtlas.Batch0951
