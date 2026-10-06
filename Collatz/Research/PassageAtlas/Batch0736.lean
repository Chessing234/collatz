import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0736

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24084. -/
theorem bounds_15_24084 : exactInterval 15 24084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24084 : oddCount 24084 15 = 7 ∧ acceleratedOrbit 15 24084 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24084) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24084.1, data_15_24084.2]

/-- Complete interval computation for depth 15, residue 24085. -/
theorem bounds_15_24085 : exactInterval 15 24085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24085 : oddCount 24085 15 = 7 ∧ acceleratedOrbit 15 24085 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24085) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24085.1, data_15_24085.2]

/-- Complete interval computation for depth 15, residue 24086. -/
theorem bounds_15_24086 : exactInterval 15 24086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24086 : oddCount 24086 15 = 6 ∧ acceleratedOrbit 15 24086 = 536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24086) = 3 ^ 6 * m + 536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24086.1, data_15_24086.2]

/-- Complete interval computation for depth 15, residue 24087. -/
theorem bounds_15_24087 : exactInterval 15 24087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24087 : oddCount 24087 15 = 6 ∧ acceleratedOrbit 15 24087 = 536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24087) = 3 ^ 6 * m + 536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24087.1, data_15_24087.2]

/-- Complete interval computation for depth 15, residue 24088. -/
theorem bounds_15_24088 : exactInterval 15 24088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24088 : oddCount 24088 15 = 7 ∧ acceleratedOrbit 15 24088 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24088) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24088.1, data_15_24088.2]

/-- Complete interval computation for depth 15, residue 24089. -/
theorem bounds_15_24089 : exactInterval 15 24089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24089 : oddCount 24089 15 = 6 ∧ acceleratedOrbit 15 24089 = 536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24089) = 3 ^ 6 * m + 536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24089.1, data_15_24089.2]

/-- Complete interval computation for depth 15, residue 24090. -/
theorem bounds_15_24090 : exactInterval 15 24090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24090 : oddCount 24090 15 = 7 ∧ acceleratedOrbit 15 24090 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24090) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24090.1, data_15_24090.2]

/-- Complete interval computation for depth 15, residue 24091. -/
theorem bounds_15_24091 : exactInterval 15 24091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24091 : oddCount 24091 15 = 12 ∧ acceleratedOrbit 15 24091 = 390743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24091) = 3 ^ 12 * m + 390743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24091.1, data_15_24091.2]

/-- Complete interval computation for depth 15, residue 24092. -/
theorem bounds_15_24092 : exactInterval 15 24092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24092 : oddCount 24092 15 = 7 ∧ acceleratedOrbit 15 24092 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24092) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24092.1, data_15_24092.2]

/-- Complete interval computation for depth 15, residue 24093. -/
theorem bounds_15_24093 : exactInterval 15 24093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24093 : oddCount 24093 15 = 7 ∧ acceleratedOrbit 15 24093 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24093) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24093.1, data_15_24093.2]

/-- Complete interval computation for depth 15, residue 24094. -/
theorem bounds_15_24094 : exactInterval 15 24094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24094 : oddCount 24094 15 = 7 ∧ acceleratedOrbit 15 24094 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24094) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24094.1, data_15_24094.2]

/-- Complete interval computation for depth 15, residue 24095. -/
theorem bounds_15_24095 : exactInterval 15 24095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24095 : oddCount 24095 15 = 11 ∧ acceleratedOrbit 15 24095 = 130268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24095) = 3 ^ 11 * m + 130268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24095.1, data_15_24095.2]

/-- Complete interval computation for depth 15, residue 24096. -/
theorem bounds_15_24096 : exactInterval 15 24096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24096 : oddCount 24096 15 = 3 ∧ acceleratedOrbit 15 24096 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24096) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24096.1, data_15_24096.2]

/-- Complete interval computation for depth 15, residue 24097. -/
theorem bounds_15_24097 : exactInterval 15 24097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24097 : oddCount 24097 15 = 8 ∧ acceleratedOrbit 15 24097 = 4826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24097) = 3 ^ 8 * m + 4826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24097.1, data_15_24097.2]

/-- Complete interval computation for depth 15, residue 24098. -/
theorem bounds_15_24098 : exactInterval 15 24098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24098 : oddCount 24098 15 = 7 ∧ acceleratedOrbit 15 24098 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24098) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24098.1, data_15_24098.2]

/-- Complete interval computation for depth 15, residue 24099. -/
theorem bounds_15_24099 : exactInterval 15 24099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24099 : oddCount 24099 15 = 7 ∧ acceleratedOrbit 15 24099 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24099) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24099.1, data_15_24099.2]

/-- Complete interval computation for depth 15, residue 24100. -/
theorem bounds_15_24100 : exactInterval 15 24100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24100 : oddCount 24100 15 = 7 ∧ acceleratedOrbit 15 24100 = 1609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24100) = 3 ^ 7 * m + 1609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24100.1, data_15_24100.2]

/-- Complete interval computation for depth 15, residue 24101. -/
theorem bounds_15_24101 : exactInterval 15 24101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24101 : oddCount 24101 15 = 7 ∧ acceleratedOrbit 15 24101 = 1609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24101) = 3 ^ 7 * m + 1609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24101.1, data_15_24101.2]

/-- Complete interval computation for depth 15, residue 24102. -/
theorem bounds_15_24102 : exactInterval 15 24102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24102 : oddCount 24102 15 = 7 ∧ acceleratedOrbit 15 24102 = 1609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24102) = 3 ^ 7 * m + 1609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24102.1, data_15_24102.2]

/-- Complete interval computation for depth 15, residue 24103. -/
theorem bounds_15_24103 : exactInterval 15 24103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24103 : oddCount 24103 15 = 7 ∧ acceleratedOrbit 15 24103 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24103) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24103.1, data_15_24103.2]

/-- Complete interval computation for depth 15, residue 24104. -/
theorem bounds_15_24104 : exactInterval 15 24104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24104 : oddCount 24104 15 = 3 ∧ acceleratedOrbit 15 24104 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24104) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24104.1, data_15_24104.2]

/-- Complete interval computation for depth 15, residue 24105. -/
theorem bounds_15_24105 : exactInterval 15 24105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24105 : oddCount 24105 15 = 11 ∧ acceleratedOrbit 15 24105 = 130324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24105) = 3 ^ 11 * m + 130324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24105.1, data_15_24105.2]

/-- Complete interval computation for depth 15, residue 24106. -/
theorem bounds_15_24106 : exactInterval 15 24106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24106 : oddCount 24106 15 = 3 ∧ acceleratedOrbit 15 24106 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24106) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24106.1, data_15_24106.2]

/-- Complete interval computation for depth 15, residue 24107. -/
theorem bounds_15_24107 : exactInterval 15 24107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24107 : oddCount 24107 15 = 7 ∧ acceleratedOrbit 15 24107 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24107) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24107.1, data_15_24107.2]

/-- Complete interval computation for depth 15, residue 24108. -/
theorem bounds_15_24108 : exactInterval 15 24108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24108 : oddCount 24108 15 = 9 ∧ acceleratedOrbit 15 24108 = 14489 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24108) = 3 ^ 9 * m + 14489 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24108.1, data_15_24108.2]

/-- Complete interval computation for depth 15, residue 24109. -/
theorem bounds_15_24109 : exactInterval 15 24109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24109 : oddCount 24109 15 = 9 ∧ acceleratedOrbit 15 24109 = 14489 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24109) = 3 ^ 9 * m + 14489 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24109.1, data_15_24109.2]

/-- Complete interval computation for depth 15, residue 24110. -/
theorem bounds_15_24110 : exactInterval 15 24110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24110 : oddCount 24110 15 = 9 ∧ acceleratedOrbit 15 24110 = 14489 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24110) = 3 ^ 9 * m + 14489 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24110.1, data_15_24110.2]

/-- Complete interval computation for depth 15, residue 24111. -/
theorem bounds_15_24111 : exactInterval 15 24111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24111 : oddCount 24111 15 = 11 ∧ acceleratedOrbit 15 24111 = 130355 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24111) = 3 ^ 11 * m + 130355 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24111.1, data_15_24111.2]

/-- Complete interval computation for depth 15, residue 24112. -/
theorem bounds_15_24112 : exactInterval 15 24112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24112 : oddCount 24112 15 = 3 ∧ acceleratedOrbit 15 24112 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24112) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24112.1, data_15_24112.2]

/-- Complete interval computation for depth 15, residue 24113. -/
theorem bounds_15_24113 : exactInterval 15 24113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24113 : oddCount 24113 15 = 9 ∧ acceleratedOrbit 15 24113 = 14489 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24113) = 3 ^ 9 * m + 14489 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24113.1, data_15_24113.2]

/-- Complete interval computation for depth 15, residue 24114. -/
theorem bounds_15_24114 : exactInterval 15 24114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24114 : oddCount 24114 15 = 9 ∧ acceleratedOrbit 15 24114 = 14489 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24114) = 3 ^ 9 * m + 14489 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24114.1, data_15_24114.2]

/-- Complete interval computation for depth 15, residue 24115. -/
theorem bounds_15_24115 : exactInterval 15 24115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24115 : oddCount 24115 15 = 9 ∧ acceleratedOrbit 15 24115 = 14489 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24115) = 3 ^ 9 * m + 14489 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24115.1, data_15_24115.2]

/-- Complete interval computation for depth 15, residue 24116. -/
theorem bounds_15_24116 : exactInterval 15 24116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24116 : oddCount 24116 15 = 3 ∧ acceleratedOrbit 15 24116 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24116) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24116.1, data_15_24116.2]

end Collatz.Research.PassageAtlas.Batch0736
