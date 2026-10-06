import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0950

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7408. -/
theorem bounds_13_7408 : exactInterval 13 7408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7408 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7408) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7408 : oddCount 7408 13 = 6 ∧ acceleratedOrbit 13 7408 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7408 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7408) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7408.1, data_13_7408.2]

/-- Complete interval computation for depth 13, residue 7409. -/
theorem bounds_13_7409 : exactInterval 13 7409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7409 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7409) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7409 : oddCount 7409 13 = 6 ∧ acceleratedOrbit 13 7409 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7409 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7409) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7409.1, data_13_7409.2]

/-- Complete interval computation for depth 13, residue 7410. -/
theorem bounds_13_7410 : exactInterval 13 7410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7410 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7410) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7410 : oddCount 7410 13 = 8 ∧ acceleratedOrbit 13 7410 = 5939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7410 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7410) = 3 ^ 8 * m + 5939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7410.1, data_13_7410.2]

/-- Complete interval computation for depth 13, residue 7411. -/
theorem bounds_13_7411 : exactInterval 13 7411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7411 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7411) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7411 : oddCount 7411 13 = 8 ∧ acceleratedOrbit 13 7411 = 5939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7411 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7411) = 3 ^ 8 * m + 5939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7411.1, data_13_7411.2]

/-- Complete interval computation for depth 13, residue 7412. -/
theorem bounds_13_7412 : exactInterval 13 7412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7412 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7412) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7412 : oddCount 7412 13 = 6 ∧ acceleratedOrbit 13 7412 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7412 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7412) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7412.1, data_13_7412.2]

/-- Complete interval computation for depth 13, residue 7413. -/
theorem bounds_13_7413 : exactInterval 13 7413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7413 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7413) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7413 : oddCount 7413 13 = 6 ∧ acceleratedOrbit 13 7413 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7413 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7413) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7413.1, data_13_7413.2]

/-- Complete interval computation for depth 13, residue 7414. -/
theorem bounds_13_7414 : exactInterval 13 7414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7414 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7414) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7414 : oddCount 7414 13 = 5 ∧ acceleratedOrbit 13 7414 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7414 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7414) = 3 ^ 5 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7414.1, data_13_7414.2]

/-- Complete interval computation for depth 13, residue 7415. -/
theorem bounds_13_7415 : exactInterval 13 7415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7415 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7415) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7415 : oddCount 7415 13 = 5 ∧ acceleratedOrbit 13 7415 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7415 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7415) = 3 ^ 5 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7415.1, data_13_7415.2]

/-- Complete interval computation for depth 13, residue 7416. -/
theorem bounds_13_7416 : exactInterval 13 7416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7416 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7416) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7416 : oddCount 7416 13 = 7 ∧ acceleratedOrbit 13 7416 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7416 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7416) = 3 ^ 7 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7416.1, data_13_7416.2]

/-- Complete interval computation for depth 13, residue 7417. -/
theorem bounds_13_7417 : exactInterval 13 7417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7417 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7417) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7417 : oddCount 7417 13 = 7 ∧ acceleratedOrbit 13 7417 = 1981 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7417 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7417) = 3 ^ 7 * m + 1981 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7417.1, data_13_7417.2]

/-- Complete interval computation for depth 13, residue 7418. -/
theorem bounds_13_7418 : exactInterval 13 7418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7418 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7418) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7418 : oddCount 7418 13 = 7 ∧ acceleratedOrbit 13 7418 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7418 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7418) = 3 ^ 7 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7418.1, data_13_7418.2]

/-- Complete interval computation for depth 13, residue 7419. -/
theorem bounds_13_7419 : exactInterval 13 7419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7419 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7419) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7419 : oddCount 7419 13 = 9 ∧ acceleratedOrbit 13 7419 = 17830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7419 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7419) = 3 ^ 9 * m + 17830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7419.1, data_13_7419.2]

/-- Complete interval computation for depth 13, residue 7420. -/
theorem bounds_13_7420 : exactInterval 13 7420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7420 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7420) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7420 : oddCount 7420 13 = 7 ∧ acceleratedOrbit 13 7420 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7420 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7420) = 3 ^ 7 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7420.1, data_13_7420.2]

/-- Complete interval computation for depth 13, residue 7421. -/
theorem bounds_13_7421 : exactInterval 13 7421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7421 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7421) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7421 : oddCount 7421 13 = 7 ∧ acceleratedOrbit 13 7421 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7421 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7421) = 3 ^ 7 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7421.1, data_13_7421.2]

/-- Complete interval computation for depth 13, residue 7422. -/
theorem bounds_13_7422 : exactInterval 13 7422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7422 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7422) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7422 : oddCount 7422 13 = 11 ∧ acceleratedOrbit 13 7422 = 160541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7422 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7422) = 3 ^ 11 * m + 160541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7422.1, data_13_7422.2]

/-- Complete interval computation for depth 13, residue 7423. -/
theorem bounds_13_7423 : exactInterval 13 7423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7423 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7423) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7423 : oddCount 7423 13 = 11 ∧ acceleratedOrbit 13 7423 = 160541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7423 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7423) = 3 ^ 11 * m + 160541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7423.1, data_13_7423.2]

end Collatz.Research.StoppingAtlas.Batch0950
