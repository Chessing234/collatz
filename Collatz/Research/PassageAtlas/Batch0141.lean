import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0141

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4587. -/
theorem bounds_15_4587 : exactInterval 15 4587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4587 : oddCount 4587 15 = 10 ∧ acceleratedOrbit 15 4587 = 8270 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4587) = 3 ^ 10 * m + 8270 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4587.1, data_15_4587.2]

/-- Complete interval computation for depth 15, residue 4588. -/
theorem bounds_15_4588 : exactInterval 15 4588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4588 : oddCount 4588 15 = 7 ∧ acceleratedOrbit 15 4588 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4588) = 3 ^ 7 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4588.1, data_15_4588.2]

/-- Complete interval computation for depth 15, residue 4589. -/
theorem bounds_15_4589 : exactInterval 15 4589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4589 : oddCount 4589 15 = 7 ∧ acceleratedOrbit 15 4589 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4589) = 3 ^ 7 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4589.1, data_15_4589.2]

/-- Complete interval computation for depth 15, residue 4590. -/
theorem bounds_15_4590 : exactInterval 15 4590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4590 : oddCount 4590 15 = 7 ∧ acceleratedOrbit 15 4590 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4590) = 3 ^ 7 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4590.1, data_15_4590.2]

/-- Complete interval computation for depth 15, residue 4591. -/
theorem bounds_15_4591 : exactInterval 15 4591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4591 : oddCount 4591 15 = 12 ∧ acceleratedOrbit 15 4591 = 74479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4591) = 3 ^ 12 * m + 74479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4591.1, data_15_4591.2]

/-- Complete interval computation for depth 15, residue 4592. -/
theorem bounds_15_4592 : exactInterval 15 4592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4592 : oddCount 4592 15 = 7 ∧ acceleratedOrbit 15 4592 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4592) = 3 ^ 7 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4592.1, data_15_4592.2]

/-- Complete interval computation for depth 15, residue 4593. -/
theorem bounds_15_4593 : exactInterval 15 4593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4593 : oddCount 4593 15 = 6 ∧ acceleratedOrbit 15 4593 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4593) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4593.1, data_15_4593.2]

/-- Complete interval computation for depth 15, residue 4594. -/
theorem bounds_15_4594 : exactInterval 15 4594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4594 : oddCount 4594 15 = 7 ∧ acceleratedOrbit 15 4594 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4594) = 3 ^ 7 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4594.1, data_15_4594.2]

/-- Complete interval computation for depth 15, residue 4595. -/
theorem bounds_15_4595 : exactInterval 15 4595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4595 : oddCount 4595 15 = 7 ∧ acceleratedOrbit 15 4595 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4595) = 3 ^ 7 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4595.1, data_15_4595.2]

/-- Complete interval computation for depth 15, residue 4596. -/
theorem bounds_15_4596 : exactInterval 15 4596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4596 : oddCount 4596 15 = 7 ∧ acceleratedOrbit 15 4596 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4596) = 3 ^ 7 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4596.1, data_15_4596.2]

/-- Complete interval computation for depth 15, residue 4597. -/
theorem bounds_15_4597 : exactInterval 15 4597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4597 : oddCount 4597 15 = 7 ∧ acceleratedOrbit 15 4597 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4597) = 3 ^ 7 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4597.1, data_15_4597.2]

/-- Complete interval computation for depth 15, residue 4598. -/
theorem bounds_15_4598 : exactInterval 15 4598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4598 : oddCount 4598 15 = 9 ∧ acceleratedOrbit 15 4598 = 2764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4598) = 3 ^ 9 * m + 2764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4598.1, data_15_4598.2]

/-- Complete interval computation for depth 15, residue 4599. -/
theorem bounds_15_4599 : exactInterval 15 4599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4599 : oddCount 4599 15 = 9 ∧ acceleratedOrbit 15 4599 = 2764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4599) = 3 ^ 9 * m + 2764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4599.1, data_15_4599.2]

/-- Complete interval computation for depth 15, residue 4600. -/
theorem bounds_15_4600 : exactInterval 15 4600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4600 : oddCount 4600 15 = 7 ∧ acceleratedOrbit 15 4600 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4600) = 3 ^ 7 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4600.1, data_15_4600.2]

/-- Complete interval computation for depth 15, residue 4601. -/
theorem bounds_15_4601 : exactInterval 15 4601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4601 : oddCount 4601 15 = 8 ∧ acceleratedOrbit 15 4601 = 922 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4601) = 3 ^ 8 * m + 922 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4601.1, data_15_4601.2]

/-- Complete interval computation for depth 15, residue 4602. -/
theorem bounds_15_4602 : exactInterval 15 4602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4602 : oddCount 4602 15 = 7 ∧ acceleratedOrbit 15 4602 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4602) = 3 ^ 7 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4602.1, data_15_4602.2]

/-- Complete interval computation for depth 15, residue 4603. -/
theorem bounds_15_4603 : exactInterval 15 4603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4603 : oddCount 4603 15 = 9 ∧ acceleratedOrbit 15 4603 = 2767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4603) = 3 ^ 9 * m + 2767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4603.1, data_15_4603.2]

/-- Complete interval computation for depth 15, residue 4604. -/
theorem bounds_15_4604 : exactInterval 15 4604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4604 : oddCount 4604 15 = 9 ∧ acceleratedOrbit 15 4604 = 2768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4604) = 3 ^ 9 * m + 2768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4604.1, data_15_4604.2]

/-- Complete interval computation for depth 15, residue 4605. -/
theorem bounds_15_4605 : exactInterval 15 4605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4605 : oddCount 4605 15 = 9 ∧ acceleratedOrbit 15 4605 = 2768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4605) = 3 ^ 9 * m + 2768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4605.1, data_15_4605.2]

/-- Complete interval computation for depth 15, residue 4606. -/
theorem bounds_15_4606 : exactInterval 15 4606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4606 : oddCount 4606 15 = 9 ∧ acceleratedOrbit 15 4606 = 2768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4606) = 3 ^ 9 * m + 2768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4606.1, data_15_4606.2]

/-- Complete interval computation for depth 15, residue 4607. -/
theorem bounds_15_4607 : exactInterval 15 4607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4607 : oddCount 4607 15 = 12 ∧ acceleratedOrbit 15 4607 = 74735 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4607) = 3 ^ 12 * m + 74735 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4607.1, data_15_4607.2]

/-- Complete interval computation for depth 15, residue 4608. -/
theorem bounds_15_4608 : exactInterval 15 4608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4608 : oddCount 4608 15 = 4 ∧ acceleratedOrbit 15 4608 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4608) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4608.1, data_15_4608.2]

/-- Complete interval computation for depth 15, residue 4609. -/
theorem bounds_15_4609 : exactInterval 15 4609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4609 : oddCount 4609 15 = 7 ∧ acceleratedOrbit 15 4609 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4609) = 3 ^ 7 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4609.1, data_15_4609.2]

/-- Complete interval computation for depth 15, residue 4610. -/
theorem bounds_15_4610 : exactInterval 15 4610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4610 : oddCount 4610 15 = 6 ∧ acceleratedOrbit 15 4610 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4610) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4610.1, data_15_4610.2]

/-- Complete interval computation for depth 15, residue 4611. -/
theorem bounds_15_4611 : exactInterval 15 4611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4611 : oddCount 4611 15 = 6 ∧ acceleratedOrbit 15 4611 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4611) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4611.1, data_15_4611.2]

/-- Complete interval computation for depth 15, residue 4612. -/
theorem bounds_15_4612 : exactInterval 15 4612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4612 : oddCount 4612 15 = 9 ∧ acceleratedOrbit 15 4612 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4612) = 3 ^ 9 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4612.1, data_15_4612.2]

/-- Complete interval computation for depth 15, residue 4613. -/
theorem bounds_15_4613 : exactInterval 15 4613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4613 : oddCount 4613 15 = 9 ∧ acceleratedOrbit 15 4613 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4613) = 3 ^ 9 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4613.1, data_15_4613.2]

/-- Complete interval computation for depth 15, residue 4614. -/
theorem bounds_15_4614 : exactInterval 15 4614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4614 : oddCount 4614 15 = 9 ∧ acceleratedOrbit 15 4614 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4614) = 3 ^ 9 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4614.1, data_15_4614.2]

/-- Complete interval computation for depth 15, residue 4615. -/
theorem bounds_15_4615 : exactInterval 15 4615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4615 : oddCount 4615 15 = 9 ∧ acceleratedOrbit 15 4615 = 2774 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4615) = 3 ^ 9 * m + 2774 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4615.1, data_15_4615.2]

/-- Complete interval computation for depth 15, residue 4616. -/
theorem bounds_15_4616 : exactInterval 15 4616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4616 : oddCount 4616 15 = 5 ∧ acceleratedOrbit 15 4616 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4616) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4616.1, data_15_4616.2]

/-- Complete interval computation for depth 15, residue 4617. -/
theorem bounds_15_4617 : exactInterval 15 4617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4617 : oddCount 4617 15 = 6 ∧ acceleratedOrbit 15 4617 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4617) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4617.1, data_15_4617.2]

/-- Complete interval computation for depth 15, residue 4618. -/
theorem bounds_15_4618 : exactInterval 15 4618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4618 : oddCount 4618 15 = 5 ∧ acceleratedOrbit 15 4618 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4618) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4618.1, data_15_4618.2]

/-- Complete interval computation for depth 15, residue 4619. -/
theorem bounds_15_4619 : exactInterval 15 4619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4619 : oddCount 4619 15 = 9 ∧ acceleratedOrbit 15 4619 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4619) = 3 ^ 9 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4619.1, data_15_4619.2]

end Collatz.Research.PassageAtlas.Batch0141
