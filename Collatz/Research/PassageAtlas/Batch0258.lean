import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0258

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8421. -/
theorem bounds_15_8421 : exactInterval 15 8421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8421 : oddCount 8421 15 = 6 ∧ acceleratedOrbit 15 8421 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8421) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8421.1, data_15_8421.2]

/-- Complete interval computation for depth 15, residue 8422. -/
theorem bounds_15_8422 : exactInterval 15 8422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8422 : oddCount 8422 15 = 6 ∧ acceleratedOrbit 15 8422 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8422) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8422.1, data_15_8422.2]

/-- Complete interval computation for depth 15, residue 8423. -/
theorem bounds_15_8423 : exactInterval 15 8423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8423 : oddCount 8423 15 = 8 ∧ acceleratedOrbit 15 8423 = 1687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8423) = 3 ^ 8 * m + 1687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8423.1, data_15_8423.2]

/-- Complete interval computation for depth 15, residue 8424. -/
theorem bounds_15_8424 : exactInterval 15 8424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8424 : oddCount 8424 15 = 7 ∧ acceleratedOrbit 15 8424 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8424) = 3 ^ 7 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8424.1, data_15_8424.2]

/-- Complete interval computation for depth 15, residue 8425. -/
theorem bounds_15_8425 : exactInterval 15 8425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8425 : oddCount 8425 15 = 10 ∧ acceleratedOrbit 15 8425 = 15187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8425) = 3 ^ 10 * m + 15187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8425.1, data_15_8425.2]

/-- Complete interval computation for depth 15, residue 8426. -/
theorem bounds_15_8426 : exactInterval 15 8426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8426 : oddCount 8426 15 = 7 ∧ acceleratedOrbit 15 8426 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8426) = 3 ^ 7 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8426.1, data_15_8426.2]

/-- Complete interval computation for depth 15, residue 8427. -/
theorem bounds_15_8427 : exactInterval 15 8427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8427 : oddCount 8427 15 = 10 ∧ acceleratedOrbit 15 8427 = 15191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8427) = 3 ^ 10 * m + 15191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8427.1, data_15_8427.2]

/-- Complete interval computation for depth 15, residue 8428. -/
theorem bounds_15_8428 : exactInterval 15 8428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8428 : oddCount 8428 15 = 8 ∧ acceleratedOrbit 15 8428 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8428) = 3 ^ 8 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8428.1, data_15_8428.2]

/-- Complete interval computation for depth 15, residue 8429. -/
theorem bounds_15_8429 : exactInterval 15 8429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8429 : oddCount 8429 15 = 8 ∧ acceleratedOrbit 15 8429 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8429) = 3 ^ 8 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8429.1, data_15_8429.2]

/-- Complete interval computation for depth 15, residue 8430. -/
theorem bounds_15_8430 : exactInterval 15 8430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8430 : oddCount 8430 15 = 8 ∧ acceleratedOrbit 15 8430 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8430) = 3 ^ 8 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8430.1, data_15_8430.2]

/-- Complete interval computation for depth 15, residue 8431. -/
theorem bounds_15_8431 : exactInterval 15 8431 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8431) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8431 : oddCount 8431 15 = 9 ∧ acceleratedOrbit 15 8431 = 5065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8431) = 3 ^ 9 * m + 5065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8431.1, data_15_8431.2]

/-- Complete interval computation for depth 15, residue 8432. -/
theorem bounds_15_8432 : exactInterval 15 8432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8432 : oddCount 8432 15 = 7 ∧ acceleratedOrbit 15 8432 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8432) = 3 ^ 7 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8432.1, data_15_8432.2]

/-- Complete interval computation for depth 15, residue 8433. -/
theorem bounds_15_8433 : exactInterval 15 8433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8433 : oddCount 8433 15 = 7 ∧ acceleratedOrbit 15 8433 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8433) = 3 ^ 7 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8433.1, data_15_8433.2]

/-- Complete interval computation for depth 15, residue 8434. -/
theorem bounds_15_8434 : exactInterval 15 8434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8434 : oddCount 8434 15 = 9 ∧ acceleratedOrbit 15 8434 = 5069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8434) = 3 ^ 9 * m + 5069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8434.1, data_15_8434.2]

/-- Complete interval computation for depth 15, residue 8435. -/
theorem bounds_15_8435 : exactInterval 15 8435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8435 : oddCount 8435 15 = 9 ∧ acceleratedOrbit 15 8435 = 5069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8435) = 3 ^ 9 * m + 5069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8435.1, data_15_8435.2]

/-- Complete interval computation for depth 15, residue 8436. -/
theorem bounds_15_8436 : exactInterval 15 8436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8436 : oddCount 8436 15 = 7 ∧ acceleratedOrbit 15 8436 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8436) = 3 ^ 7 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8436.1, data_15_8436.2]

/-- Complete interval computation for depth 15, residue 8437. -/
theorem bounds_15_8437 : exactInterval 15 8437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8437 : oddCount 8437 15 = 7 ∧ acceleratedOrbit 15 8437 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8437) = 3 ^ 7 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8437.1, data_15_8437.2]

/-- Complete interval computation for depth 15, residue 8438. -/
theorem bounds_15_8438 : exactInterval 15 8438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8438 : oddCount 8438 15 = 8 ∧ acceleratedOrbit 15 8438 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8438) = 3 ^ 8 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8438.1, data_15_8438.2]

/-- Complete interval computation for depth 15, residue 8439. -/
theorem bounds_15_8439 : exactInterval 15 8439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8439 : oddCount 8439 15 = 8 ∧ acceleratedOrbit 15 8439 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8439) = 3 ^ 8 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8439.1, data_15_8439.2]

/-- Complete interval computation for depth 15, residue 8440. -/
theorem bounds_15_8440 : exactInterval 15 8440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8440 : oddCount 8440 15 = 10 ∧ acceleratedOrbit 15 8440 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8440) = 3 ^ 10 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8440.1, data_15_8440.2]

/-- Complete interval computation for depth 15, residue 8441. -/
theorem bounds_15_8441 : exactInterval 15 8441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8441 : oddCount 8441 15 = 10 ∧ acceleratedOrbit 15 8441 = 15218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8441) = 3 ^ 10 * m + 15218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8441.1, data_15_8441.2]

/-- Complete interval computation for depth 15, residue 8442. -/
theorem bounds_15_8442 : exactInterval 15 8442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8442 : oddCount 8442 15 = 10 ∧ acceleratedOrbit 15 8442 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8442) = 3 ^ 10 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8442.1, data_15_8442.2]

/-- Complete interval computation for depth 15, residue 8443. -/
theorem bounds_15_8443 : exactInterval 15 8443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8443 : oddCount 8443 15 = 12 ∧ acceleratedOrbit 15 8443 = 136961 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8443) = 3 ^ 12 * m + 136961 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8443.1, data_15_8443.2]

/-- Complete interval computation for depth 15, residue 8444. -/
theorem bounds_15_8444 : exactInterval 15 8444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8444 : oddCount 8444 15 = 10 ∧ acceleratedOrbit 15 8444 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8444) = 3 ^ 10 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8444.1, data_15_8444.2]

/-- Complete interval computation for depth 15, residue 8445. -/
theorem bounds_15_8445 : exactInterval 15 8445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8445 : oddCount 8445 15 = 10 ∧ acceleratedOrbit 15 8445 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8445) = 3 ^ 10 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8445.1, data_15_8445.2]

/-- Complete interval computation for depth 15, residue 8446. -/
theorem bounds_15_8446 : exactInterval 15 8446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8446 : oddCount 8446 15 = 9 ∧ acceleratedOrbit 15 8446 = 5075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8446) = 3 ^ 9 * m + 5075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8446.1, data_15_8446.2]

/-- Complete interval computation for depth 15, residue 8447. -/
theorem bounds_15_8447 : exactInterval 15 8447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8447 : oddCount 8447 15 = 9 ∧ acceleratedOrbit 15 8447 = 5075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8447) = 3 ^ 9 * m + 5075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8447.1, data_15_8447.2]

/-- Complete interval computation for depth 15, residue 8448. -/
theorem bounds_15_8448 : exactInterval 15 8448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8448 : oddCount 8448 15 = 4 ∧ acceleratedOrbit 15 8448 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8448) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8448.1, data_15_8448.2]

/-- Complete interval computation for depth 15, residue 8449. -/
theorem bounds_15_8449 : exactInterval 15 8449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8449 : oddCount 8449 15 = 8 ∧ acceleratedOrbit 15 8449 = 1694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8449) = 3 ^ 8 * m + 1694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8449.1, data_15_8449.2]

/-- Complete interval computation for depth 15, residue 8450. -/
theorem bounds_15_8450 : exactInterval 15 8450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8450 : oddCount 8450 15 = 8 ∧ acceleratedOrbit 15 8450 = 1694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8450) = 3 ^ 8 * m + 1694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8450.1, data_15_8450.2]

/-- Complete interval computation for depth 15, residue 8451. -/
theorem bounds_15_8451 : exactInterval 15 8451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8451 : oddCount 8451 15 = 8 ∧ acceleratedOrbit 15 8451 = 1694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8451) = 3 ^ 8 * m + 1694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8451.1, data_15_8451.2]

/-- Complete interval computation for depth 15, residue 8452. -/
theorem bounds_15_8452 : exactInterval 15 8452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8452 : oddCount 8452 15 = 8 ∧ acceleratedOrbit 15 8452 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8452) = 3 ^ 8 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8452.1, data_15_8452.2]

/-- Complete interval computation for depth 15, residue 8453. -/
theorem bounds_15_8453 : exactInterval 15 8453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8453 : oddCount 8453 15 = 8 ∧ acceleratedOrbit 15 8453 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8453) = 3 ^ 8 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8453.1, data_15_8453.2]

end Collatz.Research.PassageAtlas.Batch0258
