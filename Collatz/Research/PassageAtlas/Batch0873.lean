import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0873

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28573. -/
theorem bounds_15_28573 : exactInterval 15 28573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28573 : oddCount 28573 15 = 8 ∧ acceleratedOrbit 15 28573 = 5723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28573) = 3 ^ 8 * m + 5723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28573.1, data_15_28573.2]

/-- Complete interval computation for depth 15, residue 28574. -/
theorem bounds_15_28574 : exactInterval 15 28574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28574 : oddCount 28574 15 = 8 ∧ acceleratedOrbit 15 28574 = 5723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28574) = 3 ^ 8 * m + 5723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28574.1, data_15_28574.2]

/-- Complete interval computation for depth 15, residue 28575. -/
theorem bounds_15_28575 : exactInterval 15 28575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28575 : oddCount 28575 15 = 11 ∧ acceleratedOrbit 15 28575 = 154487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28575) = 3 ^ 11 * m + 154487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28575.1, data_15_28575.2]

/-- Complete interval computation for depth 15, residue 28576. -/
theorem bounds_15_28576 : exactInterval 15 28576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28576 : oddCount 28576 15 = 6 ∧ acceleratedOrbit 15 28576 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28576) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28576.1, data_15_28576.2]

/-- Complete interval computation for depth 15, residue 28577. -/
theorem bounds_15_28577 : exactInterval 15 28577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28577 : oddCount 28577 15 = 9 ∧ acceleratedOrbit 15 28577 = 17171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28577) = 3 ^ 9 * m + 17171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28577.1, data_15_28577.2]

/-- Complete interval computation for depth 15, residue 28578. -/
theorem bounds_15_28578 : exactInterval 15 28578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28578 : oddCount 28578 15 = 5 ∧ acceleratedOrbit 15 28578 = 212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28578) = 3 ^ 5 * m + 212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28578.1, data_15_28578.2]

/-- Complete interval computation for depth 15, residue 28579. -/
theorem bounds_15_28579 : exactInterval 15 28579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28579 : oddCount 28579 15 = 5 ∧ acceleratedOrbit 15 28579 = 212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28579) = 3 ^ 5 * m + 212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28579.1, data_15_28579.2]

/-- Complete interval computation for depth 15, residue 28580. -/
theorem bounds_15_28580 : exactInterval 15 28580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28580 : oddCount 28580 15 = 11 ∧ acceleratedOrbit 15 28580 = 154547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28580) = 3 ^ 11 * m + 154547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28580.1, data_15_28580.2]

/-- Complete interval computation for depth 15, residue 28581. -/
theorem bounds_15_28581 : exactInterval 15 28581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28581 : oddCount 28581 15 = 11 ∧ acceleratedOrbit 15 28581 = 154547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28581) = 3 ^ 11 * m + 154547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28581.1, data_15_28581.2]

/-- Complete interval computation for depth 15, residue 28582. -/
theorem bounds_15_28582 : exactInterval 15 28582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28582 : oddCount 28582 15 = 11 ∧ acceleratedOrbit 15 28582 = 154547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28582) = 3 ^ 11 * m + 154547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28582.1, data_15_28582.2]

/-- Complete interval computation for depth 15, residue 28583. -/
theorem bounds_15_28583 : exactInterval 15 28583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28583 : oddCount 28583 15 = 10 ∧ acceleratedOrbit 15 28583 = 51511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28583) = 3 ^ 10 * m + 51511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28583.1, data_15_28583.2]

/-- Complete interval computation for depth 15, residue 28584. -/
theorem bounds_15_28584 : exactInterval 15 28584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28584 : oddCount 28584 15 = 6 ∧ acceleratedOrbit 15 28584 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28584) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28584.1, data_15_28584.2]

/-- Complete interval computation for depth 15, residue 28585. -/
theorem bounds_15_28585 : exactInterval 15 28585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28585 : oddCount 28585 15 = 11 ∧ acceleratedOrbit 15 28585 = 154543 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28585) = 3 ^ 11 * m + 154543 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28585.1, data_15_28585.2]

/-- Complete interval computation for depth 15, residue 28586. -/
theorem bounds_15_28586 : exactInterval 15 28586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28586 : oddCount 28586 15 = 6 ∧ acceleratedOrbit 15 28586 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28586) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28586.1, data_15_28586.2]

/-- Complete interval computation for depth 15, residue 28587. -/
theorem bounds_15_28587 : exactInterval 15 28587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28587 : oddCount 28587 15 = 9 ∧ acceleratedOrbit 15 28587 = 17174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28587) = 3 ^ 9 * m + 17174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28587.1, data_15_28587.2]

/-- Complete interval computation for depth 15, residue 28588. -/
theorem bounds_15_28588 : exactInterval 15 28588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28588 : oddCount 28588 15 = 8 ∧ acceleratedOrbit 15 28588 = 5726 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28588) = 3 ^ 8 * m + 5726 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28588.1, data_15_28588.2]

/-- Complete interval computation for depth 15, residue 28589. -/
theorem bounds_15_28589 : exactInterval 15 28589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28589 : oddCount 28589 15 = 8 ∧ acceleratedOrbit 15 28589 = 5726 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28589) = 3 ^ 8 * m + 5726 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28589.1, data_15_28589.2]

/-- Complete interval computation for depth 15, residue 28590. -/
theorem bounds_15_28590 : exactInterval 15 28590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28590 : oddCount 28590 15 = 8 ∧ acceleratedOrbit 15 28590 = 5726 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28590) = 3 ^ 8 * m + 5726 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28590.1, data_15_28590.2]

/-- Complete interval computation for depth 15, residue 28591. -/
theorem bounds_15_28591 : exactInterval 15 28591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28591 : oddCount 28591 15 = 8 ∧ acceleratedOrbit 15 28591 = 5726 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28591) = 3 ^ 8 * m + 5726 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28591.1, data_15_28591.2]

/-- Complete interval computation for depth 15, residue 28592. -/
theorem bounds_15_28592 : exactInterval 15 28592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28592 : oddCount 28592 15 = 7 ∧ acceleratedOrbit 15 28592 = 1910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28592) = 3 ^ 7 * m + 1910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28592.1, data_15_28592.2]

/-- Complete interval computation for depth 15, residue 28593. -/
theorem bounds_15_28593 : exactInterval 15 28593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28593 : oddCount 28593 15 = 6 ∧ acceleratedOrbit 15 28593 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28593) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28593.1, data_15_28593.2]

/-- Complete interval computation for depth 15, residue 28594. -/
theorem bounds_15_28594 : exactInterval 15 28594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28594 : oddCount 28594 15 = 6 ∧ acceleratedOrbit 15 28594 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28594) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28594.1, data_15_28594.2]

/-- Complete interval computation for depth 15, residue 28595. -/
theorem bounds_15_28595 : exactInterval 15 28595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28595 : oddCount 28595 15 = 6 ∧ acceleratedOrbit 15 28595 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28595) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28595.1, data_15_28595.2]

/-- Complete interval computation for depth 15, residue 28596. -/
theorem bounds_15_28596 : exactInterval 15 28596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28596 : oddCount 28596 15 = 7 ∧ acceleratedOrbit 15 28596 = 1910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28596) = 3 ^ 7 * m + 1910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28596.1, data_15_28596.2]

/-- Complete interval computation for depth 15, residue 28597. -/
theorem bounds_15_28597 : exactInterval 15 28597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28597 : oddCount 28597 15 = 7 ∧ acceleratedOrbit 15 28597 = 1910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28597) = 3 ^ 7 * m + 1910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28597.1, data_15_28597.2]

/-- Complete interval computation for depth 15, residue 28598. -/
theorem bounds_15_28598 : exactInterval 15 28598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28598 : oddCount 28598 15 = 7 ∧ acceleratedOrbit 15 28598 = 1909 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28598) = 3 ^ 7 * m + 1909 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28598.1, data_15_28598.2]

/-- Complete interval computation for depth 15, residue 28599. -/
theorem bounds_15_28599 : exactInterval 15 28599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28599 : oddCount 28599 15 = 7 ∧ acceleratedOrbit 15 28599 = 1909 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28599) = 3 ^ 7 * m + 1909 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28599.1, data_15_28599.2]

/-- Complete interval computation for depth 15, residue 28600. -/
theorem bounds_15_28600 : exactInterval 15 28600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28600 : oddCount 28600 15 = 7 ∧ acceleratedOrbit 15 28600 = 1910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28600) = 3 ^ 7 * m + 1910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28600.1, data_15_28600.2]

/-- Complete interval computation for depth 15, residue 28601. -/
theorem bounds_15_28601 : exactInterval 15 28601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28601 : oddCount 28601 15 = 7 ∧ acceleratedOrbit 15 28601 = 1910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28601) = 3 ^ 7 * m + 1910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28601.1, data_15_28601.2]

/-- Complete interval computation for depth 15, residue 28602. -/
theorem bounds_15_28602 : exactInterval 15 28602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28602 : oddCount 28602 15 = 7 ∧ acceleratedOrbit 15 28602 = 1910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28602) = 3 ^ 7 * m + 1910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28602.1, data_15_28602.2]

/-- Complete interval computation for depth 15, residue 28603. -/
theorem bounds_15_28603 : exactInterval 15 28603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28603 : oddCount 28603 15 = 7 ∧ acceleratedOrbit 15 28603 = 1910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28603) = 3 ^ 7 * m + 1910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28603.1, data_15_28603.2]

/-- Complete interval computation for depth 15, residue 28604. -/
theorem bounds_15_28604 : exactInterval 15 28604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28604 : oddCount 28604 15 = 9 ∧ acceleratedOrbit 15 28604 = 17185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28604) = 3 ^ 9 * m + 17185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28604.1, data_15_28604.2]

/-- Complete interval computation for depth 15, residue 28605. -/
theorem bounds_15_28605 : exactInterval 15 28605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28605 : oddCount 28605 15 = 9 ∧ acceleratedOrbit 15 28605 = 17185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28605) = 3 ^ 9 * m + 17185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28605.1, data_15_28605.2]

end Collatz.Research.PassageAtlas.Batch0873
