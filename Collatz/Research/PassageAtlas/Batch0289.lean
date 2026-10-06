import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0289

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9437. -/
theorem bounds_15_9437 : exactInterval 15 9437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9437 : oddCount 9437 15 = 8 ∧ acceleratedOrbit 15 9437 = 1891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9437) = 3 ^ 8 * m + 1891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9437.1, data_15_9437.2]

/-- Complete interval computation for depth 15, residue 9438. -/
theorem bounds_15_9438 : exactInterval 15 9438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9438 : oddCount 9438 15 = 9 ∧ acceleratedOrbit 15 9438 = 5671 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9438) = 3 ^ 9 * m + 5671 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9438.1, data_15_9438.2]

/-- Complete interval computation for depth 15, residue 9439. -/
theorem bounds_15_9439 : exactInterval 15 9439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9439 : oddCount 9439 15 = 9 ∧ acceleratedOrbit 15 9439 = 5671 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9439) = 3 ^ 9 * m + 5671 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9439.1, data_15_9439.2]

/-- Complete interval computation for depth 15, residue 9440. -/
theorem bounds_15_9440 : exactInterval 15 9440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9440 : oddCount 9440 15 = 6 ∧ acceleratedOrbit 15 9440 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9440) = 3 ^ 6 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9440.1, data_15_9440.2]

/-- Complete interval computation for depth 15, residue 9441. -/
theorem bounds_15_9441 : exactInterval 15 9441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9441 : oddCount 9441 15 = 10 ∧ acceleratedOrbit 15 9441 = 17018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9441) = 3 ^ 10 * m + 17018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9441.1, data_15_9441.2]

/-- Complete interval computation for depth 15, residue 9442. -/
theorem bounds_15_9442 : exactInterval 15 9442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9442 : oddCount 9442 15 = 5 ∧ acceleratedOrbit 15 9442 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9442) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9442.1, data_15_9442.2]

/-- Complete interval computation for depth 15, residue 9443. -/
theorem bounds_15_9443 : exactInterval 15 9443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9443 : oddCount 9443 15 = 5 ∧ acceleratedOrbit 15 9443 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9443) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9443.1, data_15_9443.2]

/-- Complete interval computation for depth 15, residue 9444. -/
theorem bounds_15_9444 : exactInterval 15 9444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9444 : oddCount 9444 15 = 7 ∧ acceleratedOrbit 15 9444 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9444) = 3 ^ 7 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9444.1, data_15_9444.2]

/-- Complete interval computation for depth 15, residue 9445. -/
theorem bounds_15_9445 : exactInterval 15 9445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9445 : oddCount 9445 15 = 7 ∧ acceleratedOrbit 15 9445 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9445) = 3 ^ 7 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9445.1, data_15_9445.2]

/-- Complete interval computation for depth 15, residue 9446. -/
theorem bounds_15_9446 : exactInterval 15 9446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9446 : oddCount 9446 15 = 7 ∧ acceleratedOrbit 15 9446 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9446) = 3 ^ 7 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9446.1, data_15_9446.2]

/-- Complete interval computation for depth 15, residue 9447. -/
theorem bounds_15_9447 : exactInterval 15 9447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9447 : oddCount 9447 15 = 10 ∧ acceleratedOrbit 15 9447 = 17027 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9447) = 3 ^ 10 * m + 17027 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9447.1, data_15_9447.2]

/-- Complete interval computation for depth 15, residue 9448. -/
theorem bounds_15_9448 : exactInterval 15 9448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9448 : oddCount 9448 15 = 6 ∧ acceleratedOrbit 15 9448 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9448) = 3 ^ 6 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9448.1, data_15_9448.2]

/-- Complete interval computation for depth 15, residue 9449. -/
theorem bounds_15_9449 : exactInterval 15 9449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9449 : oddCount 9449 15 = 7 ∧ acceleratedOrbit 15 9449 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9449) = 3 ^ 7 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9449.1, data_15_9449.2]

/-- Complete interval computation for depth 15, residue 9450. -/
theorem bounds_15_9450 : exactInterval 15 9450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9450 : oddCount 9450 15 = 6 ∧ acceleratedOrbit 15 9450 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9450) = 3 ^ 6 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9450.1, data_15_9450.2]

/-- Complete interval computation for depth 15, residue 9451. -/
theorem bounds_15_9451 : exactInterval 15 9451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9451 : oddCount 9451 15 = 10 ∧ acceleratedOrbit 15 9451 = 17036 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9451) = 3 ^ 10 * m + 17036 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9451.1, data_15_9451.2]

/-- Complete interval computation for depth 15, residue 9452. -/
theorem bounds_15_9452 : exactInterval 15 9452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9452 : oddCount 9452 15 = 6 ∧ acceleratedOrbit 15 9452 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9452) = 3 ^ 6 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9452.1, data_15_9452.2]

/-- Complete interval computation for depth 15, residue 9453. -/
theorem bounds_15_9453 : exactInterval 15 9453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9453 : oddCount 9453 15 = 6 ∧ acceleratedOrbit 15 9453 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9453) = 3 ^ 6 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9453.1, data_15_9453.2]

/-- Complete interval computation for depth 15, residue 9454. -/
theorem bounds_15_9454 : exactInterval 15 9454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9454 : oddCount 9454 15 = 6 ∧ acceleratedOrbit 15 9454 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9454) = 3 ^ 6 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9454.1, data_15_9454.2]

/-- Complete interval computation for depth 15, residue 9455. -/
theorem bounds_15_9455 : exactInterval 15 9455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9455 : oddCount 9455 15 = 11 ∧ acceleratedOrbit 15 9455 = 51121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9455) = 3 ^ 11 * m + 51121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9455.1, data_15_9455.2]

/-- Complete interval computation for depth 15, residue 9456. -/
theorem bounds_15_9456 : exactInterval 15 9456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9456 : oddCount 9456 15 = 6 ∧ acceleratedOrbit 15 9456 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9456) = 3 ^ 6 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9456.1, data_15_9456.2]

/-- Complete interval computation for depth 15, residue 9457. -/
theorem bounds_15_9457 : exactInterval 15 9457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9457 : oddCount 9457 15 = 6 ∧ acceleratedOrbit 15 9457 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9457) = 3 ^ 6 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9457.1, data_15_9457.2]

/-- Complete interval computation for depth 15, residue 9458. -/
theorem bounds_15_9458 : exactInterval 15 9458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9458 : oddCount 9458 15 = 7 ∧ acceleratedOrbit 15 9458 = 632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9458) = 3 ^ 7 * m + 632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9458.1, data_15_9458.2]

/-- Complete interval computation for depth 15, residue 9459. -/
theorem bounds_15_9459 : exactInterval 15 9459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9459 : oddCount 9459 15 = 7 ∧ acceleratedOrbit 15 9459 = 632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9459) = 3 ^ 7 * m + 632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9459.1, data_15_9459.2]

/-- Complete interval computation for depth 15, residue 9460. -/
theorem bounds_15_9460 : exactInterval 15 9460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9460 : oddCount 9460 15 = 6 ∧ acceleratedOrbit 15 9460 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9460) = 3 ^ 6 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9460.1, data_15_9460.2]

/-- Complete interval computation for depth 15, residue 9461. -/
theorem bounds_15_9461 : exactInterval 15 9461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9461 : oddCount 9461 15 = 6 ∧ acceleratedOrbit 15 9461 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9461) = 3 ^ 6 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9461.1, data_15_9461.2]

/-- Complete interval computation for depth 15, residue 9462. -/
theorem bounds_15_9462 : exactInterval 15 9462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9462 : oddCount 9462 15 = 7 ∧ acceleratedOrbit 15 9462 = 632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9462) = 3 ^ 7 * m + 632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9462.1, data_15_9462.2]

/-- Complete interval computation for depth 15, residue 9463. -/
theorem bounds_15_9463 : exactInterval 15 9463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9463 : oddCount 9463 15 = 7 ∧ acceleratedOrbit 15 9463 = 632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9463) = 3 ^ 7 * m + 632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9463.1, data_15_9463.2]

/-- Complete interval computation for depth 15, residue 9464. -/
theorem bounds_15_9464 : exactInterval 15 9464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9464 : oddCount 9464 15 = 9 ∧ acceleratedOrbit 15 9464 = 5690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9464) = 3 ^ 9 * m + 5690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9464.1, data_15_9464.2]

/-- Complete interval computation for depth 15, residue 9465. -/
theorem bounds_15_9465 : exactInterval 15 9465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9465 : oddCount 9465 15 = 7 ∧ acceleratedOrbit 15 9465 = 632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9465) = 3 ^ 7 * m + 632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9465.1, data_15_9465.2]

/-- Complete interval computation for depth 15, residue 9466. -/
theorem bounds_15_9466 : exactInterval 15 9466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9466 : oddCount 9466 15 = 9 ∧ acceleratedOrbit 15 9466 = 5690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9466) = 3 ^ 9 * m + 5690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9466.1, data_15_9466.2]

/-- Complete interval computation for depth 15, residue 9467. -/
theorem bounds_15_9467 : exactInterval 15 9467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9467 : oddCount 9467 15 = 11 ∧ acceleratedOrbit 15 9467 = 51191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9467) = 3 ^ 11 * m + 51191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9467.1, data_15_9467.2]

/-- Complete interval computation for depth 15, residue 9468. -/
theorem bounds_15_9468 : exactInterval 15 9468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9468 : oddCount 9468 15 = 9 ∧ acceleratedOrbit 15 9468 = 5690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9468) = 3 ^ 9 * m + 5690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9468.1, data_15_9468.2]

end Collatz.Research.PassageAtlas.Batch0289
