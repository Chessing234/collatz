import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0812

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26574. -/
theorem bounds_15_26574 : exactInterval 15 26574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26574 : oddCount 26574 15 = 7 ∧ acceleratedOrbit 15 26574 = 1774 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26574) = 3 ^ 7 * m + 1774 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26574.1, data_15_26574.2]

/-- Complete interval computation for depth 15, residue 26575. -/
theorem bounds_15_26575 : exactInterval 15 26575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26575 : oddCount 26575 15 = 7 ∧ acceleratedOrbit 15 26575 = 1774 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26575) = 3 ^ 7 * m + 1774 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26575.1, data_15_26575.2]

/-- Complete interval computation for depth 15, residue 26576. -/
theorem bounds_15_26576 : exactInterval 15 26576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26576 : oddCount 26576 15 = 7 ∧ acceleratedOrbit 15 26576 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26576) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26576.1, data_15_26576.2]

/-- Complete interval computation for depth 15, residue 26577. -/
theorem bounds_15_26577 : exactInterval 15 26577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26577 : oddCount 26577 15 = 7 ∧ acceleratedOrbit 15 26577 = 1775 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26577) = 3 ^ 7 * m + 1775 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26577.1, data_15_26577.2]

/-- Complete interval computation for depth 15, residue 26578. -/
theorem bounds_15_26578 : exactInterval 15 26578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26578 : oddCount 26578 15 = 9 ∧ acceleratedOrbit 15 26578 = 15967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26578) = 3 ^ 9 * m + 15967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26578.1, data_15_26578.2]

/-- Complete interval computation for depth 15, residue 26579. -/
theorem bounds_15_26579 : exactInterval 15 26579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26579 : oddCount 26579 15 = 9 ∧ acceleratedOrbit 15 26579 = 15967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26579) = 3 ^ 9 * m + 15967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26579.1, data_15_26579.2]

/-- Complete interval computation for depth 15, residue 26580. -/
theorem bounds_15_26580 : exactInterval 15 26580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26580 : oddCount 26580 15 = 7 ∧ acceleratedOrbit 15 26580 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26580) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26580.1, data_15_26580.2]

/-- Complete interval computation for depth 15, residue 26581. -/
theorem bounds_15_26581 : exactInterval 15 26581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26581 : oddCount 26581 15 = 7 ∧ acceleratedOrbit 15 26581 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26581) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26581.1, data_15_26581.2]

/-- Complete interval computation for depth 15, residue 26582. -/
theorem bounds_15_26582 : exactInterval 15 26582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26582 : oddCount 26582 15 = 9 ∧ acceleratedOrbit 15 26582 = 15970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26582) = 3 ^ 9 * m + 15970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26582.1, data_15_26582.2]

/-- Complete interval computation for depth 15, residue 26583. -/
theorem bounds_15_26583 : exactInterval 15 26583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26583 : oddCount 26583 15 = 9 ∧ acceleratedOrbit 15 26583 = 15970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26583) = 3 ^ 9 * m + 15970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26583.1, data_15_26583.2]

/-- Complete interval computation for depth 15, residue 26584. -/
theorem bounds_15_26584 : exactInterval 15 26584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26584 : oddCount 26584 15 = 9 ∧ acceleratedOrbit 15 26584 = 15977 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26584) = 3 ^ 9 * m + 15977 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26584.1, data_15_26584.2]

/-- Complete interval computation for depth 15, residue 26585. -/
theorem bounds_15_26585 : exactInterval 15 26585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26585 : oddCount 26585 15 = 6 ∧ acceleratedOrbit 15 26585 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26585) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26585.1, data_15_26585.2]

/-- Complete interval computation for depth 15, residue 26586. -/
theorem bounds_15_26586 : exactInterval 15 26586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26586 : oddCount 26586 15 = 9 ∧ acceleratedOrbit 15 26586 = 15977 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26586) = 3 ^ 9 * m + 15977 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26586.1, data_15_26586.2]

/-- Complete interval computation for depth 15, residue 26587. -/
theorem bounds_15_26587 : exactInterval 15 26587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26587 : oddCount 26587 15 = 8 ∧ acceleratedOrbit 15 26587 = 5324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26587) = 3 ^ 8 * m + 5324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26587.1, data_15_26587.2]

/-- Complete interval computation for depth 15, residue 26588. -/
theorem bounds_15_26588 : exactInterval 15 26588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26588 : oddCount 26588 15 = 9 ∧ acceleratedOrbit 15 26588 = 15977 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26588) = 3 ^ 9 * m + 15977 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26588.1, data_15_26588.2]

/-- Complete interval computation for depth 15, residue 26589. -/
theorem bounds_15_26589 : exactInterval 15 26589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26589 : oddCount 26589 15 = 9 ∧ acceleratedOrbit 15 26589 = 15977 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26589) = 3 ^ 9 * m + 15977 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26589.1, data_15_26589.2]

/-- Complete interval computation for depth 15, residue 26590. -/
theorem bounds_15_26590 : exactInterval 15 26590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26590 : oddCount 26590 15 = 9 ∧ acceleratedOrbit 15 26590 = 15974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26590) = 3 ^ 9 * m + 15974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26590.1, data_15_26590.2]

/-- Complete interval computation for depth 15, residue 26591. -/
theorem bounds_15_26591 : exactInterval 15 26591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26591 : oddCount 26591 15 = 9 ∧ acceleratedOrbit 15 26591 = 15974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26591) = 3 ^ 9 * m + 15974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26591.1, data_15_26591.2]

/-- Complete interval computation for depth 15, residue 26592. -/
theorem bounds_15_26592 : exactInterval 15 26592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26592 : oddCount 26592 15 = 7 ∧ acceleratedOrbit 15 26592 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26592) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26592.1, data_15_26592.2]

/-- Complete interval computation for depth 15, residue 26593. -/
theorem bounds_15_26593 : exactInterval 15 26593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26593 : oddCount 26593 15 = 10 ∧ acceleratedOrbit 15 26593 = 47927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26593) = 3 ^ 10 * m + 47927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26593.1, data_15_26593.2]

/-- Complete interval computation for depth 15, residue 26594. -/
theorem bounds_15_26594 : exactInterval 15 26594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26594 : oddCount 26594 15 = 7 ∧ acceleratedOrbit 15 26594 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26594) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26594.1, data_15_26594.2]

/-- Complete interval computation for depth 15, residue 26595. -/
theorem bounds_15_26595 : exactInterval 15 26595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26595 : oddCount 26595 15 = 7 ∧ acceleratedOrbit 15 26595 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26595) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26595.1, data_15_26595.2]

/-- Complete interval computation for depth 15, residue 26596. -/
theorem bounds_15_26596 : exactInterval 15 26596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26596 : oddCount 26596 15 = 9 ∧ acceleratedOrbit 15 26596 = 15983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26596) = 3 ^ 9 * m + 15983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26596.1, data_15_26596.2]

/-- Complete interval computation for depth 15, residue 26597. -/
theorem bounds_15_26597 : exactInterval 15 26597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26597 : oddCount 26597 15 = 9 ∧ acceleratedOrbit 15 26597 = 15983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26597) = 3 ^ 9 * m + 15983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26597.1, data_15_26597.2]

/-- Complete interval computation for depth 15, residue 26598. -/
theorem bounds_15_26598 : exactInterval 15 26598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26598 : oddCount 26598 15 = 9 ∧ acceleratedOrbit 15 26598 = 15983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26598) = 3 ^ 9 * m + 15983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26598.1, data_15_26598.2]

/-- Complete interval computation for depth 15, residue 26599. -/
theorem bounds_15_26599 : exactInterval 15 26599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26599 : oddCount 26599 15 = 9 ∧ acceleratedOrbit 15 26599 = 15979 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26599) = 3 ^ 9 * m + 15979 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26599.1, data_15_26599.2]

/-- Complete interval computation for depth 15, residue 26600. -/
theorem bounds_15_26600 : exactInterval 15 26600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26600 : oddCount 26600 15 = 7 ∧ acceleratedOrbit 15 26600 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26600) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26600.1, data_15_26600.2]

/-- Complete interval computation for depth 15, residue 26601. -/
theorem bounds_15_26601 : exactInterval 15 26601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26601 : oddCount 26601 15 = 11 ∧ acceleratedOrbit 15 26601 = 143819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26601) = 3 ^ 11 * m + 143819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26601.1, data_15_26601.2]

/-- Complete interval computation for depth 15, residue 26602. -/
theorem bounds_15_26602 : exactInterval 15 26602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26602 : oddCount 26602 15 = 7 ∧ acceleratedOrbit 15 26602 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26602) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26602.1, data_15_26602.2]

/-- Complete interval computation for depth 15, residue 26603. -/
theorem bounds_15_26603 : exactInterval 15 26603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26603 : oddCount 26603 15 = 8 ∧ acceleratedOrbit 15 26603 = 5327 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26603) = 3 ^ 8 * m + 5327 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26603.1, data_15_26603.2]

/-- Complete interval computation for depth 15, residue 26604. -/
theorem bounds_15_26604 : exactInterval 15 26604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26604 : oddCount 26604 15 = 6 ∧ acceleratedOrbit 15 26604 = 592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26604) = 3 ^ 6 * m + 592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26604.1, data_15_26604.2]

/-- Complete interval computation for depth 15, residue 26605. -/
theorem bounds_15_26605 : exactInterval 15 26605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26605 : oddCount 26605 15 = 6 ∧ acceleratedOrbit 15 26605 = 592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26605) = 3 ^ 6 * m + 592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26605.1, data_15_26605.2]

/-- Complete interval computation for depth 15, residue 26606. -/
theorem bounds_15_26606 : exactInterval 15 26606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26606 : oddCount 26606 15 = 6 ∧ acceleratedOrbit 15 26606 = 592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26606) = 3 ^ 6 * m + 592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26606.1, data_15_26606.2]

end Collatz.Research.PassageAtlas.Batch0812
