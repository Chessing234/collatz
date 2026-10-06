import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0441

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14417. -/
theorem bounds_15_14417 : exactInterval 15 14417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14417 : oddCount 14417 15 = 9 ∧ acceleratedOrbit 15 14417 = 8666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14417) = 3 ^ 9 * m + 8666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14417.1, data_15_14417.2]

/-- Complete interval computation for depth 15, residue 14418. -/
theorem bounds_15_14418 : exactInterval 15 14418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14418 : oddCount 14418 15 = 8 ∧ acceleratedOrbit 15 14418 = 2888 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14418) = 3 ^ 8 * m + 2888 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14418.1, data_15_14418.2]

/-- Complete interval computation for depth 15, residue 14419. -/
theorem bounds_15_14419 : exactInterval 15 14419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14419 : oddCount 14419 15 = 8 ∧ acceleratedOrbit 15 14419 = 2888 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14419) = 3 ^ 8 * m + 2888 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14419.1, data_15_14419.2]

/-- Complete interval computation for depth 15, residue 14420. -/
theorem bounds_15_14420 : exactInterval 15 14420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14420 : oddCount 14420 15 = 7 ∧ acceleratedOrbit 15 14420 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14420) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14420.1, data_15_14420.2]

/-- Complete interval computation for depth 15, residue 14421. -/
theorem bounds_15_14421 : exactInterval 15 14421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14421 : oddCount 14421 15 = 7 ∧ acceleratedOrbit 15 14421 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14421) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14421.1, data_15_14421.2]

/-- Complete interval computation for depth 15, residue 14422. -/
theorem bounds_15_14422 : exactInterval 15 14422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14422 : oddCount 14422 15 = 5 ∧ acceleratedOrbit 15 14422 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14422) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14422.1, data_15_14422.2]

/-- Complete interval computation for depth 15, residue 14423. -/
theorem bounds_15_14423 : exactInterval 15 14423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14423 : oddCount 14423 15 = 5 ∧ acceleratedOrbit 15 14423 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14423) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14423.1, data_15_14423.2]

/-- Complete interval computation for depth 15, residue 14424. -/
theorem bounds_15_14424 : exactInterval 15 14424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14424 : oddCount 14424 15 = 7 ∧ acceleratedOrbit 15 14424 = 965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14424) = 3 ^ 7 * m + 965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14424.1, data_15_14424.2]

/-- Complete interval computation for depth 15, residue 14425. -/
theorem bounds_15_14425 : exactInterval 15 14425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14425 : oddCount 14425 15 = 5 ∧ acceleratedOrbit 15 14425 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14425) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14425.1, data_15_14425.2]

/-- Complete interval computation for depth 15, residue 14426. -/
theorem bounds_15_14426 : exactInterval 15 14426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14426 : oddCount 14426 15 = 7 ∧ acceleratedOrbit 15 14426 = 965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14426) = 3 ^ 7 * m + 965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14426.1, data_15_14426.2]

/-- Complete interval computation for depth 15, residue 14427. -/
theorem bounds_15_14427 : exactInterval 15 14427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14427 : oddCount 14427 15 = 13 ∧ acceleratedOrbit 15 14427 = 702026 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14427) = 3 ^ 13 * m + 702026 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14427.1, data_15_14427.2]

/-- Complete interval computation for depth 15, residue 14428. -/
theorem bounds_15_14428 : exactInterval 15 14428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14428 : oddCount 14428 15 = 7 ∧ acceleratedOrbit 15 14428 = 965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14428) = 3 ^ 7 * m + 965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14428.1, data_15_14428.2]

/-- Complete interval computation for depth 15, residue 14429. -/
theorem bounds_15_14429 : exactInterval 15 14429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14429 : oddCount 14429 15 = 7 ∧ acceleratedOrbit 15 14429 = 965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14429) = 3 ^ 7 * m + 965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14429.1, data_15_14429.2]

/-- Complete interval computation for depth 15, residue 14430. -/
theorem bounds_15_14430 : exactInterval 15 14430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14430 : oddCount 14430 15 = 8 ∧ acceleratedOrbit 15 14430 = 2890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14430) = 3 ^ 8 * m + 2890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14430.1, data_15_14430.2]

/-- Complete interval computation for depth 15, residue 14431. -/
theorem bounds_15_14431 : exactInterval 15 14431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14431 : oddCount 14431 15 = 8 ∧ acceleratedOrbit 15 14431 = 2890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14431) = 3 ^ 8 * m + 2890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14431.1, data_15_14431.2]

/-- Complete interval computation for depth 15, residue 14432. -/
theorem bounds_15_14432 : exactInterval 15 14432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14432 : oddCount 14432 15 = 7 ∧ acceleratedOrbit 15 14432 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14432) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14432.1, data_15_14432.2]

/-- Complete interval computation for depth 15, residue 14433. -/
theorem bounds_15_14433 : exactInterval 15 14433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14433 : oddCount 14433 15 = 8 ∧ acceleratedOrbit 15 14433 = 2891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14433) = 3 ^ 8 * m + 2891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14433.1, data_15_14433.2]

/-- Complete interval computation for depth 15, residue 14434. -/
theorem bounds_15_14434 : exactInterval 15 14434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14434 : oddCount 14434 15 = 7 ∧ acceleratedOrbit 15 14434 = 965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14434) = 3 ^ 7 * m + 965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14434.1, data_15_14434.2]

/-- Complete interval computation for depth 15, residue 14435. -/
theorem bounds_15_14435 : exactInterval 15 14435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14435 : oddCount 14435 15 = 7 ∧ acceleratedOrbit 15 14435 = 965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14435) = 3 ^ 7 * m + 965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14435.1, data_15_14435.2]

/-- Complete interval computation for depth 15, residue 14436. -/
theorem bounds_15_14436 : exactInterval 15 14436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14436 : oddCount 14436 15 = 7 ∧ acceleratedOrbit 15 14436 = 965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14436) = 3 ^ 7 * m + 965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14436.1, data_15_14436.2]

/-- Complete interval computation for depth 15, residue 14437. -/
theorem bounds_15_14437 : exactInterval 15 14437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14437 : oddCount 14437 15 = 7 ∧ acceleratedOrbit 15 14437 = 965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14437) = 3 ^ 7 * m + 965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14437.1, data_15_14437.2]

/-- Complete interval computation for depth 15, residue 14438. -/
theorem bounds_15_14438 : exactInterval 15 14438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14438 : oddCount 14438 15 = 7 ∧ acceleratedOrbit 15 14438 = 965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14438) = 3 ^ 7 * m + 965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14438.1, data_15_14438.2]

/-- Complete interval computation for depth 15, residue 14439. -/
theorem bounds_15_14439 : exactInterval 15 14439 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14439) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14439 : oddCount 14439 15 = 9 ∧ acceleratedOrbit 15 14439 = 8674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14439) = 3 ^ 9 * m + 8674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14439.1, data_15_14439.2]

/-- Complete interval computation for depth 15, residue 14440. -/
theorem bounds_15_14440 : exactInterval 15 14440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14440 : oddCount 14440 15 = 7 ∧ acceleratedOrbit 15 14440 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14440) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14440.1, data_15_14440.2]

/-- Complete interval computation for depth 15, residue 14441. -/
theorem bounds_15_14441 : exactInterval 15 14441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14441 : oddCount 14441 15 = 7 ∧ acceleratedOrbit 15 14441 = 964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14441) = 3 ^ 7 * m + 964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14441.1, data_15_14441.2]

/-- Complete interval computation for depth 15, residue 14442. -/
theorem bounds_15_14442 : exactInterval 15 14442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14442 : oddCount 14442 15 = 7 ∧ acceleratedOrbit 15 14442 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14442) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14442.1, data_15_14442.2]

/-- Complete interval computation for depth 15, residue 14443. -/
theorem bounds_15_14443 : exactInterval 15 14443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14443 : oddCount 14443 15 = 9 ∧ acceleratedOrbit 15 14443 = 8677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14443) = 3 ^ 9 * m + 8677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14443.1, data_15_14443.2]

/-- Complete interval computation for depth 15, residue 14444. -/
theorem bounds_15_14444 : exactInterval 15 14444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14444 : oddCount 14444 15 = 9 ∧ acceleratedOrbit 15 14444 = 8680 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14444) = 3 ^ 9 * m + 8680 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14444.1, data_15_14444.2]

/-- Complete interval computation for depth 15, residue 14445. -/
theorem bounds_15_14445 : exactInterval 15 14445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14445 : oddCount 14445 15 = 9 ∧ acceleratedOrbit 15 14445 = 8680 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14445) = 3 ^ 9 * m + 8680 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14445.1, data_15_14445.2]

/-- Complete interval computation for depth 15, residue 14446. -/
theorem bounds_15_14446 : exactInterval 15 14446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14446 : oddCount 14446 15 = 9 ∧ acceleratedOrbit 15 14446 = 8680 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14446) = 3 ^ 9 * m + 8680 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14446.1, data_15_14446.2]

/-- Complete interval computation for depth 15, residue 14447. -/
theorem bounds_15_14447 : exactInterval 15 14447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14447 : oddCount 14447 15 = 11 ∧ acceleratedOrbit 15 14447 = 78110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14447) = 3 ^ 11 * m + 78110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14447.1, data_15_14447.2]

/-- Complete interval computation for depth 15, residue 14448. -/
theorem bounds_15_14448 : exactInterval 15 14448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14448 : oddCount 14448 15 = 6 ∧ acceleratedOrbit 15 14448 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14448) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14448.1, data_15_14448.2]

/-- Complete interval computation for depth 15, residue 14449. -/
theorem bounds_15_14449 : exactInterval 15 14449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14449 : oddCount 14449 15 = 7 ∧ acceleratedOrbit 15 14449 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14449) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14449.1, data_15_14449.2]

end Collatz.Research.PassageAtlas.Batch0441
