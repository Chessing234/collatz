import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0958

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7531. -/
theorem bounds_13_7531 : exactInterval 13 7531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7531 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7531) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7531 : oddCount 7531 13 = 8 ∧ acceleratedOrbit 13 7531 = 6034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7531 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7531) = 3 ^ 8 * m + 6034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7531.1, data_13_7531.2]

/-- Complete interval computation for depth 13, residue 7532. -/
theorem bounds_13_7532 : exactInterval 13 7532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7532 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7532) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7532 : oddCount 7532 13 = 8 ∧ acceleratedOrbit 13 7532 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7532 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7532) = 3 ^ 8 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7532.1, data_13_7532.2]

/-- Complete interval computation for depth 13, residue 7533. -/
theorem bounds_13_7533 : exactInterval 13 7533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7533 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7533) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7533 : oddCount 7533 13 = 8 ∧ acceleratedOrbit 13 7533 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7533 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7533) = 3 ^ 8 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7533.1, data_13_7533.2]

/-- Complete interval computation for depth 13, residue 7534. -/
theorem bounds_13_7534 : exactInterval 13 7534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7534 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7534) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7534 : oddCount 7534 13 = 8 ∧ acceleratedOrbit 13 7534 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7534 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7534) = 3 ^ 8 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7534.1, data_13_7534.2]

/-- Complete interval computation for depth 13, residue 7535. -/
theorem bounds_13_7535 : exactInterval 13 7535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7535 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7535) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7535 : oddCount 7535 13 = 7 ∧ acceleratedOrbit 13 7535 = 2012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7535 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7535) = 3 ^ 7 * m + 2012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7535.1, data_13_7535.2]

/-- Complete interval computation for depth 13, residue 7536. -/
theorem bounds_13_7536 : exactInterval 13 7536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7536 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7536) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7536 : oddCount 7536 13 = 6 ∧ acceleratedOrbit 13 7536 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7536 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7536) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7536.1, data_13_7536.2]

/-- Complete interval computation for depth 13, residue 7537. -/
theorem bounds_13_7537 : exactInterval 13 7537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7537 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7537) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7537 : oddCount 7537 13 = 6 ∧ acceleratedOrbit 13 7537 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7537 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7537) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7537.1, data_13_7537.2]

/-- Complete interval computation for depth 13, residue 7538. -/
theorem bounds_13_7538 : exactInterval 13 7538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7538 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7538) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7538 : oddCount 7538 13 = 7 ∧ acceleratedOrbit 13 7538 = 2015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7538 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7538) = 3 ^ 7 * m + 2015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7538.1, data_13_7538.2]

/-- Complete interval computation for depth 13, residue 7539. -/
theorem bounds_13_7539 : exactInterval 13 7539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7539 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7539) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7539 : oddCount 7539 13 = 7 ∧ acceleratedOrbit 13 7539 = 2015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7539 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7539) = 3 ^ 7 * m + 2015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7539.1, data_13_7539.2]

/-- Complete interval computation for depth 13, residue 7540. -/
theorem bounds_13_7540 : exactInterval 13 7540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7540 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7540) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7540 : oddCount 7540 13 = 6 ∧ acceleratedOrbit 13 7540 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7540 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7540) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7540.1, data_13_7540.2]

/-- Complete interval computation for depth 13, residue 7541. -/
theorem bounds_13_7541 : exactInterval 13 7541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7541 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7541) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7541 : oddCount 7541 13 = 6 ∧ acceleratedOrbit 13 7541 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7541 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7541) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7541.1, data_13_7541.2]

/-- Complete interval computation for depth 13, residue 7542. -/
theorem bounds_13_7542 : exactInterval 13 7542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7542 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7542) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7542 : oddCount 7542 13 = 7 ∧ acceleratedOrbit 13 7542 = 2015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7542 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7542) = 3 ^ 7 * m + 2015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7542.1, data_13_7542.2]

/-- Complete interval computation for depth 13, residue 7543. -/
theorem bounds_13_7543 : exactInterval 13 7543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7543 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7543) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7543 : oddCount 7543 13 = 7 ∧ acceleratedOrbit 13 7543 = 2015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7543 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7543) = 3 ^ 7 * m + 2015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7543.1, data_13_7543.2]

/-- Complete interval computation for depth 13, residue 7544. -/
theorem bounds_13_7544 : exactInterval 13 7544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7544 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7544) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7544 : oddCount 7544 13 = 5 ∧ acceleratedOrbit 13 7544 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7544 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7544) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7544.1, data_13_7544.2]

/-- Complete interval computation for depth 13, residue 7545. -/
theorem bounds_13_7545 : exactInterval 13 7545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7545 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7545) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7545 : oddCount 7545 13 = 9 ∧ acceleratedOrbit 13 7545 = 18134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7545 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7545) = 3 ^ 9 * m + 18134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7545.1, data_13_7545.2]

end Collatz.Research.StoppingAtlas.Batch0958
