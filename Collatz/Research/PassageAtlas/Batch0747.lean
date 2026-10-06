import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0747

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24444. -/
theorem bounds_15_24444 : exactInterval 15 24444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24444 : oddCount 24444 15 = 9 ∧ acceleratedOrbit 15 24444 = 14687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24444) = 3 ^ 9 * m + 14687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24444.1, data_15_24444.2]

/-- Complete interval computation for depth 15, residue 24445. -/
theorem bounds_15_24445 : exactInterval 15 24445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24445 : oddCount 24445 15 = 9 ∧ acceleratedOrbit 15 24445 = 14687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24445) = 3 ^ 9 * m + 14687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24445.1, data_15_24445.2]

/-- Complete interval computation for depth 15, residue 24446. -/
theorem bounds_15_24446 : exactInterval 15 24446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24446 : oddCount 24446 15 = 10 ∧ acceleratedOrbit 15 24446 = 44057 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24446) = 3 ^ 10 * m + 44057 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24446.1, data_15_24446.2]

/-- Complete interval computation for depth 15, residue 24447. -/
theorem bounds_15_24447 : exactInterval 15 24447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24447 : oddCount 24447 15 = 10 ∧ acceleratedOrbit 15 24447 = 44057 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24447) = 3 ^ 10 * m + 44057 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24447.1, data_15_24447.2]

/-- Complete interval computation for depth 15, residue 24448. -/
theorem bounds_15_24448 : exactInterval 15 24448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24448 : oddCount 24448 15 = 7 ∧ acceleratedOrbit 15 24448 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24448) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24448.1, data_15_24448.2]

/-- Complete interval computation for depth 15, residue 24449. -/
theorem bounds_15_24449 : exactInterval 15 24449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24449 : oddCount 24449 15 = 6 ∧ acceleratedOrbit 15 24449 = 544 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24449) = 3 ^ 6 * m + 544 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24449.1, data_15_24449.2]

/-- Complete interval computation for depth 15, residue 24450. -/
theorem bounds_15_24450 : exactInterval 15 24450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24450 : oddCount 24450 15 = 7 ∧ acceleratedOrbit 15 24450 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24450) = 3 ^ 7 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24450.1, data_15_24450.2]

/-- Complete interval computation for depth 15, residue 24451. -/
theorem bounds_15_24451 : exactInterval 15 24451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24451 : oddCount 24451 15 = 7 ∧ acceleratedOrbit 15 24451 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24451) = 3 ^ 7 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24451.1, data_15_24451.2]

/-- Complete interval computation for depth 15, residue 24452. -/
theorem bounds_15_24452 : exactInterval 15 24452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24452 : oddCount 24452 15 = 8 ∧ acceleratedOrbit 15 24452 = 4898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24452) = 3 ^ 8 * m + 4898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24452.1, data_15_24452.2]

/-- Complete interval computation for depth 15, residue 24453. -/
theorem bounds_15_24453 : exactInterval 15 24453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24453 : oddCount 24453 15 = 8 ∧ acceleratedOrbit 15 24453 = 4898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24453) = 3 ^ 8 * m + 4898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24453.1, data_15_24453.2]

/-- Complete interval computation for depth 15, residue 24454. -/
theorem bounds_15_24454 : exactInterval 15 24454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24454 : oddCount 24454 15 = 8 ∧ acceleratedOrbit 15 24454 = 4898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24454) = 3 ^ 8 * m + 4898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24454.1, data_15_24454.2]

/-- Complete interval computation for depth 15, residue 24455. -/
theorem bounds_15_24455 : exactInterval 15 24455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24455 : oddCount 24455 15 = 7 ∧ acceleratedOrbit 15 24455 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24455) = 3 ^ 7 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24455.1, data_15_24455.2]

/-- Complete interval computation for depth 15, residue 24456. -/
theorem bounds_15_24456 : exactInterval 15 24456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24456 : oddCount 24456 15 = 5 ∧ acceleratedOrbit 15 24456 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24456) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24456.1, data_15_24456.2]

/-- Complete interval computation for depth 15, residue 24457. -/
theorem bounds_15_24457 : exactInterval 15 24457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24457 : oddCount 24457 15 = 10 ∧ acceleratedOrbit 15 24457 = 44077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24457) = 3 ^ 10 * m + 44077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24457.1, data_15_24457.2]

/-- Complete interval computation for depth 15, residue 24458. -/
theorem bounds_15_24458 : exactInterval 15 24458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24458 : oddCount 24458 15 = 5 ∧ acceleratedOrbit 15 24458 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24458) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24458.1, data_15_24458.2]

/-- Complete interval computation for depth 15, residue 24459. -/
theorem bounds_15_24459 : exactInterval 15 24459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24459 : oddCount 24459 15 = 8 ∧ acceleratedOrbit 15 24459 = 4898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24459) = 3 ^ 8 * m + 4898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24459.1, data_15_24459.2]

/-- Complete interval computation for depth 15, residue 24460. -/
theorem bounds_15_24460 : exactInterval 15 24460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24460 : oddCount 24460 15 = 5 ∧ acceleratedOrbit 15 24460 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24460) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24460.1, data_15_24460.2]

/-- Complete interval computation for depth 15, residue 24461. -/
theorem bounds_15_24461 : exactInterval 15 24461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24461 : oddCount 24461 15 = 5 ∧ acceleratedOrbit 15 24461 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24461) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24461.1, data_15_24461.2]

/-- Complete interval computation for depth 15, residue 24462. -/
theorem bounds_15_24462 : exactInterval 15 24462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24462 : oddCount 24462 15 = 10 ∧ acceleratedOrbit 15 24462 = 44090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24462) = 3 ^ 10 * m + 44090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24462.1, data_15_24462.2]

/-- Complete interval computation for depth 15, residue 24463. -/
theorem bounds_15_24463 : exactInterval 15 24463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24463 : oddCount 24463 15 = 10 ∧ acceleratedOrbit 15 24463 = 44090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24463) = 3 ^ 10 * m + 44090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24463.1, data_15_24463.2]

/-- Complete interval computation for depth 15, residue 24464. -/
theorem bounds_15_24464 : exactInterval 15 24464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24464 : oddCount 24464 15 = 6 ∧ acceleratedOrbit 15 24464 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24464) = 3 ^ 6 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24464.1, data_15_24464.2]

/-- Complete interval computation for depth 15, residue 24465. -/
theorem bounds_15_24465 : exactInterval 15 24465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24465 : oddCount 24465 15 = 9 ∧ acceleratedOrbit 15 24465 = 14701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24465) = 3 ^ 9 * m + 14701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24465.1, data_15_24465.2]

/-- Complete interval computation for depth 15, residue 24466. -/
theorem bounds_15_24466 : exactInterval 15 24466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24466 : oddCount 24466 15 = 9 ∧ acceleratedOrbit 15 24466 = 14701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24466) = 3 ^ 9 * m + 14701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24466.1, data_15_24466.2]

/-- Complete interval computation for depth 15, residue 24467. -/
theorem bounds_15_24467 : exactInterval 15 24467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24467 : oddCount 24467 15 = 9 ∧ acceleratedOrbit 15 24467 = 14701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24467) = 3 ^ 9 * m + 14701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24467.1, data_15_24467.2]

/-- Complete interval computation for depth 15, residue 24468. -/
theorem bounds_15_24468 : exactInterval 15 24468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24468 : oddCount 24468 15 = 6 ∧ acceleratedOrbit 15 24468 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24468) = 3 ^ 6 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24468.1, data_15_24468.2]

/-- Complete interval computation for depth 15, residue 24469. -/
theorem bounds_15_24469 : exactInterval 15 24469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24469 : oddCount 24469 15 = 6 ∧ acceleratedOrbit 15 24469 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24469) = 3 ^ 6 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24469.1, data_15_24469.2]

/-- Complete interval computation for depth 15, residue 24470. -/
theorem bounds_15_24470 : exactInterval 15 24470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24470 : oddCount 24470 15 = 5 ∧ acceleratedOrbit 15 24470 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24470) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24470.1, data_15_24470.2]

/-- Complete interval computation for depth 15, residue 24471. -/
theorem bounds_15_24471 : exactInterval 15 24471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24471 : oddCount 24471 15 = 5 ∧ acceleratedOrbit 15 24471 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24471) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24471.1, data_15_24471.2]

/-- Complete interval computation for depth 15, residue 24472. -/
theorem bounds_15_24472 : exactInterval 15 24472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24472 : oddCount 24472 15 = 6 ∧ acceleratedOrbit 15 24472 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24472) = 3 ^ 6 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24472.1, data_15_24472.2]

/-- Complete interval computation for depth 15, residue 24473. -/
theorem bounds_15_24473 : exactInterval 15 24473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24473 : oddCount 24473 15 = 5 ∧ acceleratedOrbit 15 24473 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24473) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24473.1, data_15_24473.2]

/-- Complete interval computation for depth 15, residue 24474. -/
theorem bounds_15_24474 : exactInterval 15 24474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24474 : oddCount 24474 15 = 6 ∧ acceleratedOrbit 15 24474 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24474) = 3 ^ 6 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24474.1, data_15_24474.2]

/-- Complete interval computation for depth 15, residue 24475. -/
theorem bounds_15_24475 : exactInterval 15 24475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24475 : oddCount 24475 15 = 8 ∧ acceleratedOrbit 15 24475 = 4901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24475) = 3 ^ 8 * m + 4901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24475.1, data_15_24475.2]

/-- Complete interval computation for depth 15, residue 24476. -/
theorem bounds_15_24476 : exactInterval 15 24476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24476 : oddCount 24476 15 = 7 ∧ acceleratedOrbit 15 24476 = 1634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24476) = 3 ^ 7 * m + 1634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24476.1, data_15_24476.2]

end Collatz.Research.PassageAtlas.Batch0747
