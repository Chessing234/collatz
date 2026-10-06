import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0443

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14483. -/
theorem bounds_15_14483 : exactInterval 15 14483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14483 : oddCount 14483 15 = 10 ∧ acceleratedOrbit 15 14483 = 26108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14483) = 3 ^ 10 * m + 26108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14483.1, data_15_14483.2]

/-- Complete interval computation for depth 15, residue 14484. -/
theorem bounds_15_14484 : exactInterval 15 14484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14484 : oddCount 14484 15 = 8 ∧ acceleratedOrbit 15 14484 = 2906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14484) = 3 ^ 8 * m + 2906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14484.1, data_15_14484.2]

/-- Complete interval computation for depth 15, residue 14485. -/
theorem bounds_15_14485 : exactInterval 15 14485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14485 : oddCount 14485 15 = 8 ∧ acceleratedOrbit 15 14485 = 2906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14485) = 3 ^ 8 * m + 2906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14485.1, data_15_14485.2]

/-- Complete interval computation for depth 15, residue 14486. -/
theorem bounds_15_14486 : exactInterval 15 14486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14486 : oddCount 14486 15 = 7 ∧ acceleratedOrbit 15 14486 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14486) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14486.1, data_15_14486.2]

/-- Complete interval computation for depth 15, residue 14487. -/
theorem bounds_15_14487 : exactInterval 15 14487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14487 : oddCount 14487 15 = 7 ∧ acceleratedOrbit 15 14487 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14487) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14487.1, data_15_14487.2]

/-- Complete interval computation for depth 15, residue 14488. -/
theorem bounds_15_14488 : exactInterval 15 14488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14488 : oddCount 14488 15 = 8 ∧ acceleratedOrbit 15 14488 = 2906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14488) = 3 ^ 8 * m + 2906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14488.1, data_15_14488.2]

/-- Complete interval computation for depth 15, residue 14489. -/
theorem bounds_15_14489 : exactInterval 15 14489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14489 : oddCount 14489 15 = 9 ∧ acceleratedOrbit 15 14489 = 8707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14489) = 3 ^ 9 * m + 8707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14489.1, data_15_14489.2]

/-- Complete interval computation for depth 15, residue 14490. -/
theorem bounds_15_14490 : exactInterval 15 14490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14490 : oddCount 14490 15 = 8 ∧ acceleratedOrbit 15 14490 = 2906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14490) = 3 ^ 8 * m + 2906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14490.1, data_15_14490.2]

/-- Complete interval computation for depth 15, residue 14491. -/
theorem bounds_15_14491 : exactInterval 15 14491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14491 : oddCount 14491 15 = 8 ∧ acceleratedOrbit 15 14491 = 2902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14491) = 3 ^ 8 * m + 2902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14491.1, data_15_14491.2]

/-- Complete interval computation for depth 15, residue 14492. -/
theorem bounds_15_14492 : exactInterval 15 14492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14492 : oddCount 14492 15 = 6 ∧ acceleratedOrbit 15 14492 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14492) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14492.1, data_15_14492.2]

/-- Complete interval computation for depth 15, residue 14493. -/
theorem bounds_15_14493 : exactInterval 15 14493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14493 : oddCount 14493 15 = 6 ∧ acceleratedOrbit 15 14493 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14493) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14493.1, data_15_14493.2]

/-- Complete interval computation for depth 15, residue 14494. -/
theorem bounds_15_14494 : exactInterval 15 14494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14494 : oddCount 14494 15 = 6 ∧ acceleratedOrbit 15 14494 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14494) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14494.1, data_15_14494.2]

/-- Complete interval computation for depth 15, residue 14495. -/
theorem bounds_15_14495 : exactInterval 15 14495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14495 : oddCount 14495 15 = 13 ∧ acceleratedOrbit 15 14495 = 705307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14495) = 3 ^ 13 * m + 705307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14495.1, data_15_14495.2]

/-- Complete interval computation for depth 15, residue 14496. -/
theorem bounds_15_14496 : exactInterval 15 14496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14496 : oddCount 14496 15 = 2 ∧ acceleratedOrbit 15 14496 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14496) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14496.1, data_15_14496.2]

/-- Complete interval computation for depth 15, residue 14497. -/
theorem bounds_15_14497 : exactInterval 15 14497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14497 : oddCount 14497 15 = 9 ∧ acceleratedOrbit 15 14497 = 8711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14497) = 3 ^ 9 * m + 8711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14497.1, data_15_14497.2]

/-- Complete interval computation for depth 15, residue 14498. -/
theorem bounds_15_14498 : exactInterval 15 14498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14498 : oddCount 14498 15 = 8 ∧ acceleratedOrbit 15 14498 = 2906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14498) = 3 ^ 8 * m + 2906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14498.1, data_15_14498.2]

/-- Complete interval computation for depth 15, residue 14499. -/
theorem bounds_15_14499 : exactInterval 15 14499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14499 : oddCount 14499 15 = 8 ∧ acceleratedOrbit 15 14499 = 2906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14499) = 3 ^ 8 * m + 2906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14499.1, data_15_14499.2]

/-- Complete interval computation for depth 15, residue 14500. -/
theorem bounds_15_14500 : exactInterval 15 14500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14500 : oddCount 14500 15 = 9 ∧ acceleratedOrbit 15 14500 = 8714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14500) = 3 ^ 9 * m + 8714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14500.1, data_15_14500.2]

/-- Complete interval computation for depth 15, residue 14501. -/
theorem bounds_15_14501 : exactInterval 15 14501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14501 : oddCount 14501 15 = 9 ∧ acceleratedOrbit 15 14501 = 8714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14501) = 3 ^ 9 * m + 8714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14501.1, data_15_14501.2]

/-- Complete interval computation for depth 15, residue 14502. -/
theorem bounds_15_14502 : exactInterval 15 14502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14502 : oddCount 14502 15 = 9 ∧ acceleratedOrbit 15 14502 = 8714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14502) = 3 ^ 9 * m + 8714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14502.1, data_15_14502.2]

/-- Complete interval computation for depth 15, residue 14503. -/
theorem bounds_15_14503 : exactInterval 15 14503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14503 : oddCount 14503 15 = 10 ∧ acceleratedOrbit 15 14503 = 26138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14503) = 3 ^ 10 * m + 26138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14503.1, data_15_14503.2]

/-- Complete interval computation for depth 15, residue 14504. -/
theorem bounds_15_14504 : exactInterval 15 14504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14504 : oddCount 14504 15 = 2 ∧ acceleratedOrbit 15 14504 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14504) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14504.1, data_15_14504.2]

/-- Complete interval computation for depth 15, residue 14505. -/
theorem bounds_15_14505 : exactInterval 15 14505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14505 : oddCount 14505 15 = 11 ∧ acceleratedOrbit 15 14505 = 78425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14505) = 3 ^ 11 * m + 78425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14505.1, data_15_14505.2]

/-- Complete interval computation for depth 15, residue 14506. -/
theorem bounds_15_14506 : exactInterval 15 14506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14506 : oddCount 14506 15 = 2 ∧ acceleratedOrbit 15 14506 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14506) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14506.1, data_15_14506.2]

/-- Complete interval computation for depth 15, residue 14507. -/
theorem bounds_15_14507 : exactInterval 15 14507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14507 : oddCount 14507 15 = 8 ∧ acceleratedOrbit 15 14507 = 2906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14507) = 3 ^ 8 * m + 2906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14507.1, data_15_14507.2]

/-- Complete interval computation for depth 15, residue 14508. -/
theorem bounds_15_14508 : exactInterval 15 14508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14508 : oddCount 14508 15 = 7 ∧ acceleratedOrbit 15 14508 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14508) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14508.1, data_15_14508.2]

/-- Complete interval computation for depth 15, residue 14509. -/
theorem bounds_15_14509 : exactInterval 15 14509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14509 : oddCount 14509 15 = 7 ∧ acceleratedOrbit 15 14509 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14509) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14509.1, data_15_14509.2]

/-- Complete interval computation for depth 15, residue 14510. -/
theorem bounds_15_14510 : exactInterval 15 14510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14510 : oddCount 14510 15 = 7 ∧ acceleratedOrbit 15 14510 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14510) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14510.1, data_15_14510.2]

/-- Complete interval computation for depth 15, residue 14511. -/
theorem bounds_15_14511 : exactInterval 15 14511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14511 : oddCount 14511 15 = 10 ∧ acceleratedOrbit 15 14511 = 26153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14511) = 3 ^ 10 * m + 26153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14511.1, data_15_14511.2]

/-- Complete interval computation for depth 15, residue 14512. -/
theorem bounds_15_14512 : exactInterval 15 14512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14512 : oddCount 14512 15 = 8 ∧ acceleratedOrbit 15 14512 = 2915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14512) = 3 ^ 8 * m + 2915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14512.1, data_15_14512.2]

/-- Complete interval computation for depth 15, residue 14513. -/
theorem bounds_15_14513 : exactInterval 15 14513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14513 : oddCount 14513 15 = 8 ∧ acceleratedOrbit 15 14513 = 2909 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14513) = 3 ^ 8 * m + 2909 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14513.1, data_15_14513.2]

/-- Complete interval computation for depth 15, residue 14514. -/
theorem bounds_15_14514 : exactInterval 15 14514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14514 : oddCount 14514 15 = 8 ∧ acceleratedOrbit 15 14514 = 2909 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14514) = 3 ^ 8 * m + 2909 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14514.1, data_15_14514.2]

/-- Complete interval computation for depth 15, residue 14515. -/
theorem bounds_15_14515 : exactInterval 15 14515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14515 : oddCount 14515 15 = 8 ∧ acceleratedOrbit 15 14515 = 2909 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14515) = 3 ^ 8 * m + 2909 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14515.1, data_15_14515.2]

end Collatz.Research.PassageAtlas.Batch0443
