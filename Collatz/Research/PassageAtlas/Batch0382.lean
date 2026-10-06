import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0382

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12484. -/
theorem bounds_15_12484 : exactInterval 15 12484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12484 : oddCount 12484 15 = 7 ∧ acceleratedOrbit 15 12484 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12484) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12484.1, data_15_12484.2]

/-- Complete interval computation for depth 15, residue 12485. -/
theorem bounds_15_12485 : exactInterval 15 12485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12485 : oddCount 12485 15 = 7 ∧ acceleratedOrbit 15 12485 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12485) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12485.1, data_15_12485.2]

/-- Complete interval computation for depth 15, residue 12486. -/
theorem bounds_15_12486 : exactInterval 15 12486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12486 : oddCount 12486 15 = 7 ∧ acceleratedOrbit 15 12486 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12486) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12486.1, data_15_12486.2]

/-- Complete interval computation for depth 15, residue 12487. -/
theorem bounds_15_12487 : exactInterval 15 12487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12487 : oddCount 12487 15 = 10 ∧ acceleratedOrbit 15 12487 = 22508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12487) = 3 ^ 10 * m + 22508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12487.1, data_15_12487.2]

/-- Complete interval computation for depth 15, residue 12488. -/
theorem bounds_15_12488 : exactInterval 15 12488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12488 : oddCount 12488 15 = 7 ∧ acceleratedOrbit 15 12488 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12488) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12488.1, data_15_12488.2]

/-- Complete interval computation for depth 15, residue 12489. -/
theorem bounds_15_12489 : exactInterval 15 12489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12489 : oddCount 12489 15 = 7 ∧ acceleratedOrbit 15 12489 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12489) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12489.1, data_15_12489.2]

/-- Complete interval computation for depth 15, residue 12490. -/
theorem bounds_15_12490 : exactInterval 15 12490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12490 : oddCount 12490 15 = 7 ∧ acceleratedOrbit 15 12490 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12490) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12490.1, data_15_12490.2]

/-- Complete interval computation for depth 15, residue 12491. -/
theorem bounds_15_12491 : exactInterval 15 12491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12491 : oddCount 12491 15 = 6 ∧ acceleratedOrbit 15 12491 = 278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12491) = 3 ^ 6 * m + 278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12491.1, data_15_12491.2]

/-- Complete interval computation for depth 15, residue 12492. -/
theorem bounds_15_12492 : exactInterval 15 12492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12492 : oddCount 12492 15 = 7 ∧ acceleratedOrbit 15 12492 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12492) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12492.1, data_15_12492.2]

/-- Complete interval computation for depth 15, residue 12493. -/
theorem bounds_15_12493 : exactInterval 15 12493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12493 : oddCount 12493 15 = 7 ∧ acceleratedOrbit 15 12493 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12493) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12493.1, data_15_12493.2]

/-- Complete interval computation for depth 15, residue 12494. -/
theorem bounds_15_12494 : exactInterval 15 12494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12494 : oddCount 12494 15 = 10 ∧ acceleratedOrbit 15 12494 = 22520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12494) = 3 ^ 10 * m + 22520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12494.1, data_15_12494.2]

/-- Complete interval computation for depth 15, residue 12495. -/
theorem bounds_15_12495 : exactInterval 15 12495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12495 : oddCount 12495 15 = 10 ∧ acceleratedOrbit 15 12495 = 22520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12495) = 3 ^ 10 * m + 22520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12495.1, data_15_12495.2]

/-- Complete interval computation for depth 15, residue 12496. -/
theorem bounds_15_12496 : exactInterval 15 12496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12496 : oddCount 12496 15 = 5 ∧ acceleratedOrbit 15 12496 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12496) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12496.1, data_15_12496.2]

/-- Complete interval computation for depth 15, residue 12497. -/
theorem bounds_15_12497 : exactInterval 15 12497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12497 : oddCount 12497 15 = 8 ∧ acceleratedOrbit 15 12497 = 2504 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12497) = 3 ^ 8 * m + 2504 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12497.1, data_15_12497.2]

/-- Complete interval computation for depth 15, residue 12498. -/
theorem bounds_15_12498 : exactInterval 15 12498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12498 : oddCount 12498 15 = 8 ∧ acceleratedOrbit 15 12498 = 2504 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12498) = 3 ^ 8 * m + 2504 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12498.1, data_15_12498.2]

/-- Complete interval computation for depth 15, residue 12499. -/
theorem bounds_15_12499 : exactInterval 15 12499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12499 : oddCount 12499 15 = 8 ∧ acceleratedOrbit 15 12499 = 2504 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12499) = 3 ^ 8 * m + 2504 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12499.1, data_15_12499.2]

/-- Complete interval computation for depth 15, residue 12500. -/
theorem bounds_15_12500 : exactInterval 15 12500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12500 : oddCount 12500 15 = 5 ∧ acceleratedOrbit 15 12500 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12500) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12500.1, data_15_12500.2]

/-- Complete interval computation for depth 15, residue 12501. -/
theorem bounds_15_12501 : exactInterval 15 12501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12501 : oddCount 12501 15 = 5 ∧ acceleratedOrbit 15 12501 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12501) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12501.1, data_15_12501.2]

/-- Complete interval computation for depth 15, residue 12502. -/
theorem bounds_15_12502 : exactInterval 15 12502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12502 : oddCount 12502 15 = 10 ∧ acceleratedOrbit 15 12502 = 22538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12502) = 3 ^ 10 * m + 22538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12502.1, data_15_12502.2]

/-- Complete interval computation for depth 15, residue 12503. -/
theorem bounds_15_12503 : exactInterval 15 12503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12503 : oddCount 12503 15 = 10 ∧ acceleratedOrbit 15 12503 = 22538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12503) = 3 ^ 10 * m + 22538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12503.1, data_15_12503.2]

/-- Complete interval computation for depth 15, residue 12504. -/
theorem bounds_15_12504 : exactInterval 15 12504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12504 : oddCount 12504 15 = 8 ∧ acceleratedOrbit 15 12504 = 2506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12504) = 3 ^ 8 * m + 2506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12504.1, data_15_12504.2]

/-- Complete interval computation for depth 15, residue 12505. -/
theorem bounds_15_12505 : exactInterval 15 12505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12505 : oddCount 12505 15 = 8 ∧ acceleratedOrbit 15 12505 = 2506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12505) = 3 ^ 8 * m + 2506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12505.1, data_15_12505.2]

/-- Complete interval computation for depth 15, residue 12506. -/
theorem bounds_15_12506 : exactInterval 15 12506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12506 : oddCount 12506 15 = 8 ∧ acceleratedOrbit 15 12506 = 2506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12506) = 3 ^ 8 * m + 2506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12506.1, data_15_12506.2]

/-- Complete interval computation for depth 15, residue 12507. -/
theorem bounds_15_12507 : exactInterval 15 12507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12507 : oddCount 12507 15 = 10 ∧ acceleratedOrbit 15 12507 = 22544 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12507) = 3 ^ 10 * m + 22544 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12507.1, data_15_12507.2]

/-- Complete interval computation for depth 15, residue 12508. -/
theorem bounds_15_12508 : exactInterval 15 12508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12508 : oddCount 12508 15 = 8 ∧ acceleratedOrbit 15 12508 = 2506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12508) = 3 ^ 8 * m + 2506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12508.1, data_15_12508.2]

/-- Complete interval computation for depth 15, residue 12509. -/
theorem bounds_15_12509 : exactInterval 15 12509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12509 : oddCount 12509 15 = 8 ∧ acceleratedOrbit 15 12509 = 2506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12509) = 3 ^ 8 * m + 2506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12509.1, data_15_12509.2]

/-- Complete interval computation for depth 15, residue 12510. -/
theorem bounds_15_12510 : exactInterval 15 12510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12510 : oddCount 12510 15 = 9 ∧ acceleratedOrbit 15 12510 = 7516 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12510) = 3 ^ 9 * m + 7516 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12510.1, data_15_12510.2]

/-- Complete interval computation for depth 15, residue 12511. -/
theorem bounds_15_12511 : exactInterval 15 12511 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12511) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12511 : oddCount 12511 15 = 9 ∧ acceleratedOrbit 15 12511 = 7516 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12511) = 3 ^ 9 * m + 7516 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12511.1, data_15_12511.2]

/-- Complete interval computation for depth 15, residue 12512. -/
theorem bounds_15_12512 : exactInterval 15 12512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12512 : oddCount 12512 15 = 4 ∧ acceleratedOrbit 15 12512 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12512) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12512.1, data_15_12512.2]

/-- Complete interval computation for depth 15, residue 12513. -/
theorem bounds_15_12513 : exactInterval 15 12513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12513 : oddCount 12513 15 = 11 ∧ acceleratedOrbit 15 12513 = 67661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12513) = 3 ^ 11 * m + 67661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12513.1, data_15_12513.2]

/-- Complete interval computation for depth 15, residue 12514. -/
theorem bounds_15_12514 : exactInterval 15 12514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12514 : oddCount 12514 15 = 5 ∧ acceleratedOrbit 15 12514 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12514) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12514.1, data_15_12514.2]

/-- Complete interval computation for depth 15, residue 12515. -/
theorem bounds_15_12515 : exactInterval 15 12515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12515 : oddCount 12515 15 = 5 ∧ acceleratedOrbit 15 12515 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12515) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12515.1, data_15_12515.2]

/-- Complete interval computation for depth 15, residue 12516. -/
theorem bounds_15_12516 : exactInterval 15 12516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12516 : oddCount 12516 15 = 8 ∧ acceleratedOrbit 15 12516 = 2510 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12516) = 3 ^ 8 * m + 2510 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12516.1, data_15_12516.2]

end Collatz.Research.PassageAtlas.Batch0382
