import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0380

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12419. -/
theorem bounds_15_12419 : exactInterval 15 12419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12419 : oddCount 12419 15 = 7 ∧ acceleratedOrbit 15 12419 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12419) = 3 ^ 7 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12419.1, data_15_12419.2]

/-- Complete interval computation for depth 15, residue 12420. -/
theorem bounds_15_12420 : exactInterval 15 12420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12420 : oddCount 12420 15 = 7 ∧ acceleratedOrbit 15 12420 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12420) = 3 ^ 7 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12420.1, data_15_12420.2]

/-- Complete interval computation for depth 15, residue 12421. -/
theorem bounds_15_12421 : exactInterval 15 12421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12421 : oddCount 12421 15 = 7 ∧ acceleratedOrbit 15 12421 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12421) = 3 ^ 7 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12421.1, data_15_12421.2]

/-- Complete interval computation for depth 15, residue 12422. -/
theorem bounds_15_12422 : exactInterval 15 12422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12422 : oddCount 12422 15 = 7 ∧ acceleratedOrbit 15 12422 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12422) = 3 ^ 7 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12422.1, data_15_12422.2]

/-- Complete interval computation for depth 15, residue 12423. -/
theorem bounds_15_12423 : exactInterval 15 12423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12423 : oddCount 12423 15 = 9 ∧ acceleratedOrbit 15 12423 = 7465 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12423) = 3 ^ 9 * m + 7465 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12423.1, data_15_12423.2]

/-- Complete interval computation for depth 15, residue 12424. -/
theorem bounds_15_12424 : exactInterval 15 12424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12424 : oddCount 12424 15 = 4 ∧ acceleratedOrbit 15 12424 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12424) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12424.1, data_15_12424.2]

/-- Complete interval computation for depth 15, residue 12425. -/
theorem bounds_15_12425 : exactInterval 15 12425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12425 : oddCount 12425 15 = 10 ∧ acceleratedOrbit 15 12425 = 22394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12425) = 3 ^ 10 * m + 22394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12425.1, data_15_12425.2]

/-- Complete interval computation for depth 15, residue 12426. -/
theorem bounds_15_12426 : exactInterval 15 12426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12426 : oddCount 12426 15 = 4 ∧ acceleratedOrbit 15 12426 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12426) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12426.1, data_15_12426.2]

/-- Complete interval computation for depth 15, residue 12427. -/
theorem bounds_15_12427 : exactInterval 15 12427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12427 : oddCount 12427 15 = 8 ∧ acceleratedOrbit 15 12427 = 2489 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12427) = 3 ^ 8 * m + 2489 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12427.1, data_15_12427.2]

/-- Complete interval computation for depth 15, residue 12428. -/
theorem bounds_15_12428 : exactInterval 15 12428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12428 : oddCount 12428 15 = 4 ∧ acceleratedOrbit 15 12428 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12428) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12428.1, data_15_12428.2]

/-- Complete interval computation for depth 15, residue 12429. -/
theorem bounds_15_12429 : exactInterval 15 12429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12429 : oddCount 12429 15 = 4 ∧ acceleratedOrbit 15 12429 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12429) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12429.1, data_15_12429.2]

/-- Complete interval computation for depth 15, residue 12430. -/
theorem bounds_15_12430 : exactInterval 15 12430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12430 : oddCount 12430 15 = 9 ∧ acceleratedOrbit 15 12430 = 7469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12430) = 3 ^ 9 * m + 7469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12430.1, data_15_12430.2]

/-- Complete interval computation for depth 15, residue 12431. -/
theorem bounds_15_12431 : exactInterval 15 12431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12431 : oddCount 12431 15 = 9 ∧ acceleratedOrbit 15 12431 = 7469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12431) = 3 ^ 9 * m + 7469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12431.1, data_15_12431.2]

/-- Complete interval computation for depth 15, residue 12432. -/
theorem bounds_15_12432 : exactInterval 15 12432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12432 : oddCount 12432 15 = 7 ∧ acceleratedOrbit 15 12432 = 832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12432) = 3 ^ 7 * m + 832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12432.1, data_15_12432.2]

/-- Complete interval computation for depth 15, residue 12433. -/
theorem bounds_15_12433 : exactInterval 15 12433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12433 : oddCount 12433 15 = 9 ∧ acceleratedOrbit 15 12433 = 7472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12433) = 3 ^ 9 * m + 7472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12433.1, data_15_12433.2]

/-- Complete interval computation for depth 15, residue 12434. -/
theorem bounds_15_12434 : exactInterval 15 12434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12434 : oddCount 12434 15 = 9 ∧ acceleratedOrbit 15 12434 = 7472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12434) = 3 ^ 9 * m + 7472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12434.1, data_15_12434.2]

/-- Complete interval computation for depth 15, residue 12435. -/
theorem bounds_15_12435 : exactInterval 15 12435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12435 : oddCount 12435 15 = 9 ∧ acceleratedOrbit 15 12435 = 7472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12435) = 3 ^ 9 * m + 7472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12435.1, data_15_12435.2]

/-- Complete interval computation for depth 15, residue 12436. -/
theorem bounds_15_12436 : exactInterval 15 12436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12436 : oddCount 12436 15 = 7 ∧ acceleratedOrbit 15 12436 = 832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12436) = 3 ^ 7 * m + 832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12436.1, data_15_12436.2]

/-- Complete interval computation for depth 15, residue 12437. -/
theorem bounds_15_12437 : exactInterval 15 12437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12437 : oddCount 12437 15 = 7 ∧ acceleratedOrbit 15 12437 = 832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12437) = 3 ^ 7 * m + 832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12437.1, data_15_12437.2]

/-- Complete interval computation for depth 15, residue 12438. -/
theorem bounds_15_12438 : exactInterval 15 12438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12438 : oddCount 12438 15 = 4 ∧ acceleratedOrbit 15 12438 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12438) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12438.1, data_15_12438.2]

/-- Complete interval computation for depth 15, residue 12439. -/
theorem bounds_15_12439 : exactInterval 15 12439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12439 : oddCount 12439 15 = 4 ∧ acceleratedOrbit 15 12439 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12439) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12439.1, data_15_12439.2]

/-- Complete interval computation for depth 15, residue 12440. -/
theorem bounds_15_12440 : exactInterval 15 12440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12440 : oddCount 12440 15 = 7 ∧ acceleratedOrbit 15 12440 = 832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12440) = 3 ^ 7 * m + 832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12440.1, data_15_12440.2]

/-- Complete interval computation for depth 15, residue 12441. -/
theorem bounds_15_12441 : exactInterval 15 12441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12441 : oddCount 12441 15 = 9 ∧ acceleratedOrbit 15 12441 = 7478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12441) = 3 ^ 9 * m + 7478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12441.1, data_15_12441.2]

/-- Complete interval computation for depth 15, residue 12442. -/
theorem bounds_15_12442 : exactInterval 15 12442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12442 : oddCount 12442 15 = 7 ∧ acceleratedOrbit 15 12442 = 832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12442) = 3 ^ 7 * m + 832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12442.1, data_15_12442.2]

/-- Complete interval computation for depth 15, residue 12443. -/
theorem bounds_15_12443 : exactInterval 15 12443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12443 : oddCount 12443 15 = 10 ∧ acceleratedOrbit 15 12443 = 22427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12443) = 3 ^ 10 * m + 22427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12443.1, data_15_12443.2]

/-- Complete interval computation for depth 15, residue 12444. -/
theorem bounds_15_12444 : exactInterval 15 12444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12444 : oddCount 12444 15 = 6 ∧ acceleratedOrbit 15 12444 = 277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12444) = 3 ^ 6 * m + 277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12444.1, data_15_12444.2]

/-- Complete interval computation for depth 15, residue 12445. -/
theorem bounds_15_12445 : exactInterval 15 12445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12445 : oddCount 12445 15 = 6 ∧ acceleratedOrbit 15 12445 = 277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12445) = 3 ^ 6 * m + 277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12445.1, data_15_12445.2]

/-- Complete interval computation for depth 15, residue 12446. -/
theorem bounds_15_12446 : exactInterval 15 12446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12446 : oddCount 12446 15 = 6 ∧ acceleratedOrbit 15 12446 = 277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12446) = 3 ^ 6 * m + 277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12446.1, data_15_12446.2]

/-- Complete interval computation for depth 15, residue 12447. -/
theorem bounds_15_12447 : exactInterval 15 12447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12447 : oddCount 12447 15 = 13 ∧ acceleratedOrbit 15 12447 = 605663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12447) = 3 ^ 13 * m + 605663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12447.1, data_15_12447.2]

/-- Complete interval computation for depth 15, residue 12448. -/
theorem bounds_15_12448 : exactInterval 15 12448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12448 : oddCount 12448 15 = 5 ∧ acceleratedOrbit 15 12448 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12448) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12448.1, data_15_12448.2]

/-- Complete interval computation for depth 15, residue 12449. -/
theorem bounds_15_12449 : exactInterval 15 12449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12449 : oddCount 12449 15 = 9 ∧ acceleratedOrbit 15 12449 = 7480 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12449) = 3 ^ 9 * m + 7480 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12449.1, data_15_12449.2]

/-- Complete interval computation for depth 15, residue 12450. -/
theorem bounds_15_12450 : exactInterval 15 12450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12450 : oddCount 12450 15 = 7 ∧ acceleratedOrbit 15 12450 = 832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12450) = 3 ^ 7 * m + 832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12450.1, data_15_12450.2]

end Collatz.Research.PassageAtlas.Batch0380
