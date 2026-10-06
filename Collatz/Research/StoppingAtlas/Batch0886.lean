import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0886

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6425. -/
theorem bounds_13_6425 : exactInterval 13 6425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6425 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6425) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6425 : oddCount 6425 13 = 6 ∧ acceleratedOrbit 13 6425 = 572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6425 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6425) = 3 ^ 6 * m + 572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6425.1, data_13_6425.2]

/-- Complete interval computation for depth 13, residue 6426. -/
theorem bounds_13_6426 : exactInterval 13 6426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6426 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6426) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6426 : oddCount 6426 13 = 4 ∧ acceleratedOrbit 13 6426 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6426 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6426) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6426.1, data_13_6426.2]

/-- Complete interval computation for depth 13, residue 6427. -/
theorem bounds_13_6427 : exactInterval 13 6427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6427 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6427) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6427 : oddCount 6427 13 = 9 ∧ acceleratedOrbit 13 6427 = 15446 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6427 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6427) = 3 ^ 9 * m + 15446 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6427.1, data_13_6427.2]

/-- Complete interval computation for depth 13, residue 6428. -/
theorem bounds_13_6428 : exactInterval 13 6428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6428 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6428) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6428 : oddCount 6428 13 = 7 ∧ acceleratedOrbit 13 6428 = 1718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6428 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6428) = 3 ^ 7 * m + 1718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6428.1, data_13_6428.2]

/-- Complete interval computation for depth 13, residue 6429. -/
theorem bounds_13_6429 : exactInterval 13 6429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6429 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6429) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6429 : oddCount 6429 13 = 7 ∧ acceleratedOrbit 13 6429 = 1718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6429 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6429) = 3 ^ 7 * m + 1718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6429.1, data_13_6429.2]

/-- Complete interval computation for depth 13, residue 6430. -/
theorem bounds_13_6430 : exactInterval 13 6430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6430 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6430) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6430 : oddCount 6430 13 = 7 ∧ acceleratedOrbit 13 6430 = 1718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6430 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6430) = 3 ^ 7 * m + 1718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6430.1, data_13_6430.2]

/-- Complete interval computation for depth 13, residue 6431. -/
theorem bounds_13_6431 : exactInterval 13 6431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6431 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6431) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6431 : oddCount 6431 13 = 8 ∧ acceleratedOrbit 13 6431 = 5152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6431 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6431) = 3 ^ 8 * m + 5152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6431.1, data_13_6431.2]

/-- Complete interval computation for depth 13, residue 6432. -/
theorem bounds_13_6432 : exactInterval 13 6432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6432 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6432) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6432 : oddCount 6432 13 = 4 ∧ acceleratedOrbit 13 6432 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6432 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6432) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6432.1, data_13_6432.2]

/-- Complete interval computation for depth 13, residue 6433. -/
theorem bounds_13_6433 : exactInterval 13 6433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6433 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6433) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6433 : oddCount 6433 13 = 5 ∧ acceleratedOrbit 13 6433 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6433 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6433) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6433.1, data_13_6433.2]

/-- Complete interval computation for depth 13, residue 6434. -/
theorem bounds_13_6434 : exactInterval 13 6434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6434 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6434) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6434 : oddCount 6434 13 = 7 ∧ acceleratedOrbit 13 6434 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6434 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6434) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6434.1, data_13_6434.2]

/-- Complete interval computation for depth 13, residue 6435. -/
theorem bounds_13_6435 : exactInterval 13 6435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6435 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6435) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6435 : oddCount 6435 13 = 7 ∧ acceleratedOrbit 13 6435 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6435 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6435) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6435.1, data_13_6435.2]

/-- Complete interval computation for depth 13, residue 6436. -/
theorem bounds_13_6436 : exactInterval 13 6436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6436 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6436) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6436 : oddCount 6436 13 = 7 ∧ acceleratedOrbit 13 6436 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6436 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6436) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6436.1, data_13_6436.2]

/-- Complete interval computation for depth 13, residue 6437. -/
theorem bounds_13_6437 : exactInterval 13 6437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6437 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6437) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6437 : oddCount 6437 13 = 7 ∧ acceleratedOrbit 13 6437 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6437 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6437) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6437.1, data_13_6437.2]

/-- Complete interval computation for depth 13, residue 6438. -/
theorem bounds_13_6438 : exactInterval 13 6438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6438 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6438) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6438 : oddCount 6438 13 = 7 ∧ acceleratedOrbit 13 6438 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6438 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6438) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6438.1, data_13_6438.2]

/-- Complete interval computation for depth 13, residue 6439. -/
theorem bounds_13_6439 : exactInterval 13 6439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6439 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6439) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6439 : oddCount 6439 13 = 8 ∧ acceleratedOrbit 13 6439 = 5159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6439 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6439) = 3 ^ 8 * m + 5159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6439.1, data_13_6439.2]

end Collatz.Research.StoppingAtlas.Batch0886
