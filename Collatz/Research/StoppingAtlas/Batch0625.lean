import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0625

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2416. -/
theorem bounds_13_2416 : exactInterval 13 2416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2416 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2416) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2416 : oddCount 2416 13 = 3 ∧ acceleratedOrbit 13 2416 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2416 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2416) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2416.1, data_13_2416.2]

/-- Complete interval computation for depth 13, residue 2417. -/
theorem bounds_13_2417 : exactInterval 13 2417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2417 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2417) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2417 : oddCount 2417 13 = 3 ∧ acceleratedOrbit 13 2417 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2417 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2417) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2417.1, data_13_2417.2]

/-- Complete interval computation for depth 13, residue 2418. -/
theorem bounds_13_2418 : exactInterval 13 2418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2418 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2418) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2418 : oddCount 2418 13 = 8 ∧ acceleratedOrbit 13 2418 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2418 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2418) = 3 ^ 8 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2418.1, data_13_2418.2]

/-- Complete interval computation for depth 13, residue 2419. -/
theorem bounds_13_2419 : exactInterval 13 2419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2419 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2419) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2419 : oddCount 2419 13 = 8 ∧ acceleratedOrbit 13 2419 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2419 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2419) = 3 ^ 8 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2419.1, data_13_2419.2]

/-- Complete interval computation for depth 13, residue 2420. -/
theorem bounds_13_2420 : exactInterval 13 2420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2420 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2420) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2420 : oddCount 2420 13 = 3 ∧ acceleratedOrbit 13 2420 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2420 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2420) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2420.1, data_13_2420.2]

/-- Complete interval computation for depth 13, residue 2421. -/
theorem bounds_13_2421 : exactInterval 13 2421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2421 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2421) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2421 : oddCount 2421 13 = 3 ∧ acceleratedOrbit 13 2421 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2421 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2421) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2421.1, data_13_2421.2]

/-- Complete interval computation for depth 13, residue 2422. -/
theorem bounds_13_2422 : exactInterval 13 2422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2422 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2422) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2422 : oddCount 2422 13 = 9 ∧ acceleratedOrbit 13 2422 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2422 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2422) = 3 ^ 9 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2422.1, data_13_2422.2]

/-- Complete interval computation for depth 13, residue 2423. -/
theorem bounds_13_2423 : exactInterval 13 2423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2423 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2423) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2423 : oddCount 2423 13 = 9 ∧ acceleratedOrbit 13 2423 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2423 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2423) = 3 ^ 9 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2423.1, data_13_2423.2]

/-- Complete interval computation for depth 13, residue 2424. -/
theorem bounds_13_2424 : exactInterval 13 2424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2424 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2424) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2424 : oddCount 2424 13 = 7 ∧ acceleratedOrbit 13 2424 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2424 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2424) = 3 ^ 7 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2424.1, data_13_2424.2]

/-- Complete interval computation for depth 13, residue 2425. -/
theorem bounds_13_2425 : exactInterval 13 2425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2425 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2425) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2425 : oddCount 2425 13 = 11 ∧ acceleratedOrbit 13 2425 = 52487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2425 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2425) = 3 ^ 11 * m + 52487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2425.1, data_13_2425.2]

/-- Complete interval computation for depth 13, residue 2426. -/
theorem bounds_13_2426 : exactInterval 13 2426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2426 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2426) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2426 : oddCount 2426 13 = 7 ∧ acceleratedOrbit 13 2426 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2426 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2426) = 3 ^ 7 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2426.1, data_13_2426.2]

/-- Complete interval computation for depth 13, residue 2427. -/
theorem bounds_13_2427 : exactInterval 13 2427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2427 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2427) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2427 : oddCount 2427 13 = 8 ∧ acceleratedOrbit 13 2427 = 1946 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2427 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2427) = 3 ^ 8 * m + 1946 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2427.1, data_13_2427.2]

/-- Complete interval computation for depth 13, residue 2428. -/
theorem bounds_13_2428 : exactInterval 13 2428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2428 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2428) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2428 : oddCount 2428 13 = 7 ∧ acceleratedOrbit 13 2428 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2428 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2428) = 3 ^ 7 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2428.1, data_13_2428.2]

/-- Complete interval computation for depth 13, residue 2429. -/
theorem bounds_13_2429 : exactInterval 13 2429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2429 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2429) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2429 : oddCount 2429 13 = 7 ∧ acceleratedOrbit 13 2429 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2429 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2429) = 3 ^ 7 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2429.1, data_13_2429.2]

/-- Complete interval computation for depth 13, residue 2430. -/
theorem bounds_13_2430 : exactInterval 13 2430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2430 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2430) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2430 : oddCount 2430 13 = 8 ∧ acceleratedOrbit 13 2430 = 1948 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2430 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2430) = 3 ^ 8 * m + 1948 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2430.1, data_13_2430.2]

/-- Complete interval computation for depth 13, residue 2431. -/
theorem bounds_13_2431 : exactInterval 13 2431 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2431 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2431) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2431 : oddCount 2431 13 = 8 ∧ acceleratedOrbit 13 2431 = 1948 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2431 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2431) = 3 ^ 8 * m + 1948 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2431.1, data_13_2431.2]

end Collatz.Research.StoppingAtlas.Batch0625
