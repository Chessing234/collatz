import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0319

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10420. -/
theorem bounds_15_10420 : exactInterval 15 10420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10420 : oddCount 10420 15 = 6 ∧ acceleratedOrbit 15 10420 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10420) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10420.1, data_15_10420.2]

/-- Complete interval computation for depth 15, residue 10421. -/
theorem bounds_15_10421 : exactInterval 15 10421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10421 : oddCount 10421 15 = 6 ∧ acceleratedOrbit 15 10421 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10421) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10421.1, data_15_10421.2]

/-- Complete interval computation for depth 15, residue 10422. -/
theorem bounds_15_10422 : exactInterval 15 10422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10422 : oddCount 10422 15 = 10 ∧ acceleratedOrbit 15 10422 = 18787 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10422) = 3 ^ 10 * m + 18787 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10422.1, data_15_10422.2]

/-- Complete interval computation for depth 15, residue 10423. -/
theorem bounds_15_10423 : exactInterval 15 10423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10423 : oddCount 10423 15 = 10 ∧ acceleratedOrbit 15 10423 = 18787 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10423) = 3 ^ 10 * m + 18787 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10423.1, data_15_10423.2]

/-- Complete interval computation for depth 15, residue 10424. -/
theorem bounds_15_10424 : exactInterval 15 10424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10424 : oddCount 10424 15 = 6 ∧ acceleratedOrbit 15 10424 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10424) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10424.1, data_15_10424.2]

/-- Complete interval computation for depth 15, residue 10425. -/
theorem bounds_15_10425 : exactInterval 15 10425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10425 : oddCount 10425 15 = 6 ∧ acceleratedOrbit 15 10425 = 232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10425) = 3 ^ 6 * m + 232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10425.1, data_15_10425.2]

/-- Complete interval computation for depth 15, residue 10426. -/
theorem bounds_15_10426 : exactInterval 15 10426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10426 : oddCount 10426 15 = 6 ∧ acceleratedOrbit 15 10426 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10426) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10426.1, data_15_10426.2]

/-- Complete interval computation for depth 15, residue 10427. -/
theorem bounds_15_10427 : exactInterval 15 10427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10427 : oddCount 10427 15 = 9 ∧ acceleratedOrbit 15 10427 = 6265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10427) = 3 ^ 9 * m + 6265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10427.1, data_15_10427.2]

/-- Complete interval computation for depth 15, residue 10428. -/
theorem bounds_15_10428 : exactInterval 15 10428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10428 : oddCount 10428 15 = 8 ∧ acceleratedOrbit 15 10428 = 2089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10428) = 3 ^ 8 * m + 2089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10428.1, data_15_10428.2]

/-- Complete interval computation for depth 15, residue 10429. -/
theorem bounds_15_10429 : exactInterval 15 10429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10429 : oddCount 10429 15 = 8 ∧ acceleratedOrbit 15 10429 = 2089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10429) = 3 ^ 8 * m + 2089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10429.1, data_15_10429.2]

/-- Complete interval computation for depth 15, residue 10430. -/
theorem bounds_15_10430 : exactInterval 15 10430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10430 : oddCount 10430 15 = 8 ∧ acceleratedOrbit 15 10430 = 2089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10430) = 3 ^ 8 * m + 2089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10430.1, data_15_10430.2]

/-- Complete interval computation for depth 15, residue 10431. -/
theorem bounds_15_10431 : exactInterval 15 10431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10431 : oddCount 10431 15 = 8 ∧ acceleratedOrbit 15 10431 = 2089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10431) = 3 ^ 8 * m + 2089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10431.1, data_15_10431.2]

/-- Complete interval computation for depth 15, residue 10432. -/
theorem bounds_15_10432 : exactInterval 15 10432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10432 : oddCount 10432 15 = 5 ∧ acceleratedOrbit 15 10432 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10432) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10432.1, data_15_10432.2]

/-- Complete interval computation for depth 15, residue 10433. -/
theorem bounds_15_10433 : exactInterval 15 10433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10433 : oddCount 10433 15 = 7 ∧ acceleratedOrbit 15 10433 = 697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10433) = 3 ^ 7 * m + 697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10433.1, data_15_10433.2]

/-- Complete interval computation for depth 15, residue 10434. -/
theorem bounds_15_10434 : exactInterval 15 10434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10434 : oddCount 10434 15 = 7 ∧ acceleratedOrbit 15 10434 = 697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10434) = 3 ^ 7 * m + 697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10434.1, data_15_10434.2]

/-- Complete interval computation for depth 15, residue 10435. -/
theorem bounds_15_10435 : exactInterval 15 10435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10435 : oddCount 10435 15 = 7 ∧ acceleratedOrbit 15 10435 = 697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10435) = 3 ^ 7 * m + 697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10435.1, data_15_10435.2]

/-- Complete interval computation for depth 15, residue 10436. -/
theorem bounds_15_10436 : exactInterval 15 10436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10436 : oddCount 10436 15 = 8 ∧ acceleratedOrbit 15 10436 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10436) = 3 ^ 8 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10436.1, data_15_10436.2]

/-- Complete interval computation for depth 15, residue 10437. -/
theorem bounds_15_10437 : exactInterval 15 10437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10437 : oddCount 10437 15 = 8 ∧ acceleratedOrbit 15 10437 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10437) = 3 ^ 8 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10437.1, data_15_10437.2]

/-- Complete interval computation for depth 15, residue 10438. -/
theorem bounds_15_10438 : exactInterval 15 10438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10438 : oddCount 10438 15 = 8 ∧ acceleratedOrbit 15 10438 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10438) = 3 ^ 8 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10438.1, data_15_10438.2]

/-- Complete interval computation for depth 15, residue 10439. -/
theorem bounds_15_10439 : exactInterval 15 10439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10439 : oddCount 10439 15 = 10 ∧ acceleratedOrbit 15 10439 = 18818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10439) = 3 ^ 10 * m + 18818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10439.1, data_15_10439.2]

/-- Complete interval computation for depth 15, residue 10440. -/
theorem bounds_15_10440 : exactInterval 15 10440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10440 : oddCount 10440 15 = 8 ∧ acceleratedOrbit 15 10440 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10440) = 3 ^ 8 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10440.1, data_15_10440.2]

/-- Complete interval computation for depth 15, residue 10441. -/
theorem bounds_15_10441 : exactInterval 15 10441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10441 : oddCount 10441 15 = 6 ∧ acceleratedOrbit 15 10441 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10441) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10441.1, data_15_10441.2]

/-- Complete interval computation for depth 15, residue 10442. -/
theorem bounds_15_10442 : exactInterval 15 10442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10442 : oddCount 10442 15 = 8 ∧ acceleratedOrbit 15 10442 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10442) = 3 ^ 8 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10442.1, data_15_10442.2]

/-- Complete interval computation for depth 15, residue 10443. -/
theorem bounds_15_10443 : exactInterval 15 10443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10443 : oddCount 10443 15 = 9 ∧ acceleratedOrbit 15 10443 = 6277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10443) = 3 ^ 9 * m + 6277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10443.1, data_15_10443.2]

/-- Complete interval computation for depth 15, residue 10444. -/
theorem bounds_15_10444 : exactInterval 15 10444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10444 : oddCount 10444 15 = 8 ∧ acceleratedOrbit 15 10444 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10444) = 3 ^ 8 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10444.1, data_15_10444.2]

/-- Complete interval computation for depth 15, residue 10445. -/
theorem bounds_15_10445 : exactInterval 15 10445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10445 : oddCount 10445 15 = 8 ∧ acceleratedOrbit 15 10445 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10445) = 3 ^ 8 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10445.1, data_15_10445.2]

/-- Complete interval computation for depth 15, residue 10446. -/
theorem bounds_15_10446 : exactInterval 15 10446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10446 : oddCount 10446 15 = 10 ∧ acceleratedOrbit 15 10446 = 18829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10446) = 3 ^ 10 * m + 18829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10446.1, data_15_10446.2]

/-- Complete interval computation for depth 15, residue 10447. -/
theorem bounds_15_10447 : exactInterval 15 10447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10447 : oddCount 10447 15 = 10 ∧ acceleratedOrbit 15 10447 = 18829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10447) = 3 ^ 10 * m + 18829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10447.1, data_15_10447.2]

/-- Complete interval computation for depth 15, residue 10448. -/
theorem bounds_15_10448 : exactInterval 15 10448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10448 : oddCount 10448 15 = 5 ∧ acceleratedOrbit 15 10448 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10448) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10448.1, data_15_10448.2]

/-- Complete interval computation for depth 15, residue 10449. -/
theorem bounds_15_10449 : exactInterval 15 10449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10449 : oddCount 10449 15 = 9 ∧ acceleratedOrbit 15 10449 = 6281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10449) = 3 ^ 9 * m + 6281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10449.1, data_15_10449.2]

/-- Complete interval computation for depth 15, residue 10450. -/
theorem bounds_15_10450 : exactInterval 15 10450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10450 : oddCount 10450 15 = 9 ∧ acceleratedOrbit 15 10450 = 6281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10450) = 3 ^ 9 * m + 6281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10450.1, data_15_10450.2]

/-- Complete interval computation for depth 15, residue 10451. -/
theorem bounds_15_10451 : exactInterval 15 10451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10451 : oddCount 10451 15 = 9 ∧ acceleratedOrbit 15 10451 = 6281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10451) = 3 ^ 9 * m + 6281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10451.1, data_15_10451.2]

end Collatz.Research.PassageAtlas.Batch0319
