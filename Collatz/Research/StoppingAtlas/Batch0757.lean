import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0757

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4444. -/
theorem bounds_13_4444 : exactInterval 13 4444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4444 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4444) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4444 : oddCount 4444 13 = 4 ∧ acceleratedOrbit 13 4444 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4444 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4444) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4444.1, data_13_4444.2]

/-- Complete interval computation for depth 13, residue 4445. -/
theorem bounds_13_4445 : exactInterval 13 4445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4445 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4445) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4445 : oddCount 4445 13 = 4 ∧ acceleratedOrbit 13 4445 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4445 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4445) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4445.1, data_13_4445.2]

/-- Complete interval computation for depth 13, residue 4446. -/
theorem bounds_13_4446 : exactInterval 13 4446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4446 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4446) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4446 : oddCount 4446 13 = 9 ∧ acceleratedOrbit 13 4446 = 10691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4446 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4446) = 3 ^ 9 * m + 10691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4446.1, data_13_4446.2]

/-- Complete interval computation for depth 13, residue 4447. -/
theorem bounds_13_4447 : exactInterval 13 4447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4447 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4447) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4447 : oddCount 4447 13 = 9 ∧ acceleratedOrbit 13 4447 = 10691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4447 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4447) = 3 ^ 9 * m + 10691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4447.1, data_13_4447.2]

/-- Complete interval computation for depth 13, residue 4448. -/
theorem bounds_13_4448 : exactInterval 13 4448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4448 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4448) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4448 : oddCount 4448 13 = 5 ∧ acceleratedOrbit 13 4448 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4448 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4448) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4448.1, data_13_4448.2]

/-- Complete interval computation for depth 13, residue 4449. -/
theorem bounds_13_4449 : exactInterval 13 4449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4449 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4449) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4449 : oddCount 4449 13 = 8 ∧ acceleratedOrbit 13 4449 = 3566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4449 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4449) = 3 ^ 8 * m + 3566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4449.1, data_13_4449.2]

/-- Complete interval computation for depth 13, residue 4450. -/
theorem bounds_13_4450 : exactInterval 13 4450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4450 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4450) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4450 : oddCount 4450 13 = 6 ∧ acceleratedOrbit 13 4450 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4450 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4450) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4450.1, data_13_4450.2]

/-- Complete interval computation for depth 13, residue 4451. -/
theorem bounds_13_4451 : exactInterval 13 4451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4451 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4451) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4451 : oddCount 4451 13 = 6 ∧ acceleratedOrbit 13 4451 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4451 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4451) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4451.1, data_13_4451.2]

/-- Complete interval computation for depth 13, residue 4452. -/
theorem bounds_13_4452 : exactInterval 13 4452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4452 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4452) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4452 : oddCount 4452 13 = 6 ∧ acceleratedOrbit 13 4452 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4452 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4452) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4452.1, data_13_4452.2]

/-- Complete interval computation for depth 13, residue 4453. -/
theorem bounds_13_4453 : exactInterval 13 4453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4453 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4453) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4453 : oddCount 4453 13 = 6 ∧ acceleratedOrbit 13 4453 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4453 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4453) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4453.1, data_13_4453.2]

/-- Complete interval computation for depth 13, residue 4454. -/
theorem bounds_13_4454 : exactInterval 13 4454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4454 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4454) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4454 : oddCount 4454 13 = 6 ∧ acceleratedOrbit 13 4454 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4454 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4454) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4454.1, data_13_4454.2]

/-- Complete interval computation for depth 13, residue 4455. -/
theorem bounds_13_4455 : exactInterval 13 4455 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4455 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4455) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4455 : oddCount 4455 13 = 8 ∧ acceleratedOrbit 13 4455 = 3569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4455 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4455) = 3 ^ 8 * m + 3569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4455.1, data_13_4455.2]

/-- Complete interval computation for depth 13, residue 4456. -/
theorem bounds_13_4456 : exactInterval 13 4456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4456 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4456) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4456 : oddCount 4456 13 = 5 ∧ acceleratedOrbit 13 4456 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4456 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4456) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4456.1, data_13_4456.2]

/-- Complete interval computation for depth 13, residue 4457. -/
theorem bounds_13_4457 : exactInterval 13 4457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4457 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4457) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4457 : oddCount 4457 13 = 6 ∧ acceleratedOrbit 13 4457 = 397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4457 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4457) = 3 ^ 6 * m + 397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4457.1, data_13_4457.2]

/-- Complete interval computation for depth 13, residue 4458. -/
theorem bounds_13_4458 : exactInterval 13 4458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4458 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4458) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4458 : oddCount 4458 13 = 5 ∧ acceleratedOrbit 13 4458 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4458 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4458) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4458.1, data_13_4458.2]

end Collatz.Research.StoppingAtlas.Batch0757
