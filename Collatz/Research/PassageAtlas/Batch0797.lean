import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0797

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26083. -/
theorem bounds_15_26083 : exactInterval 15 26083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26083 : oddCount 26083 15 = 4 ∧ acceleratedOrbit 15 26083 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26083) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26083.1, data_15_26083.2]

/-- Complete interval computation for depth 15, residue 26084. -/
theorem bounds_15_26084 : exactInterval 15 26084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26084 : oddCount 26084 15 = 10 ∧ acceleratedOrbit 15 26084 = 47020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26084) = 3 ^ 10 * m + 47020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26084.1, data_15_26084.2]

/-- Complete interval computation for depth 15, residue 26085. -/
theorem bounds_15_26085 : exactInterval 15 26085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26085 : oddCount 26085 15 = 10 ∧ acceleratedOrbit 15 26085 = 47020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26085) = 3 ^ 10 * m + 47020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26085.1, data_15_26085.2]

/-- Complete interval computation for depth 15, residue 26086. -/
theorem bounds_15_26086 : exactInterval 15 26086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26086 : oddCount 26086 15 = 10 ∧ acceleratedOrbit 15 26086 = 47020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26086) = 3 ^ 10 * m + 47020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26086.1, data_15_26086.2]

/-- Complete interval computation for depth 15, residue 26087. -/
theorem bounds_15_26087 : exactInterval 15 26087 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26087) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26087 : oddCount 26087 15 = 9 ∧ acceleratedOrbit 15 26087 = 15671 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26087) = 3 ^ 9 * m + 15671 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26087.1, data_15_26087.2]

/-- Complete interval computation for depth 15, residue 26088. -/
theorem bounds_15_26088 : exactInterval 15 26088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26088 : oddCount 26088 15 = 6 ∧ acceleratedOrbit 15 26088 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26088) = 3 ^ 6 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26088.1, data_15_26088.2]

/-- Complete interval computation for depth 15, residue 26089. -/
theorem bounds_15_26089 : exactInterval 15 26089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26089 : oddCount 26089 15 = 10 ∧ acceleratedOrbit 15 26089 = 47017 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26089) = 3 ^ 10 * m + 47017 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26089.1, data_15_26089.2]

/-- Complete interval computation for depth 15, residue 26090. -/
theorem bounds_15_26090 : exactInterval 15 26090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26090 : oddCount 26090 15 = 6 ∧ acceleratedOrbit 15 26090 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26090) = 3 ^ 6 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26090.1, data_15_26090.2]

/-- Complete interval computation for depth 15, residue 26091. -/
theorem bounds_15_26091 : exactInterval 15 26091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26091 : oddCount 26091 15 = 12 ∧ acceleratedOrbit 15 26091 = 423184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26091) = 3 ^ 12 * m + 423184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26091.1, data_15_26091.2]

/-- Complete interval computation for depth 15, residue 26092. -/
theorem bounds_15_26092 : exactInterval 15 26092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26092 : oddCount 26092 15 = 7 ∧ acceleratedOrbit 15 26092 = 1742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26092) = 3 ^ 7 * m + 1742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26092.1, data_15_26092.2]

/-- Complete interval computation for depth 15, residue 26093. -/
theorem bounds_15_26093 : exactInterval 15 26093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26093 : oddCount 26093 15 = 7 ∧ acceleratedOrbit 15 26093 = 1742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26093) = 3 ^ 7 * m + 1742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26093.1, data_15_26093.2]

/-- Complete interval computation for depth 15, residue 26094. -/
theorem bounds_15_26094 : exactInterval 15 26094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26094 : oddCount 26094 15 = 7 ∧ acceleratedOrbit 15 26094 = 1742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26094) = 3 ^ 7 * m + 1742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26094.1, data_15_26094.2]

/-- Complete interval computation for depth 15, residue 26095. -/
theorem bounds_15_26095 : exactInterval 15 26095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26095 : oddCount 26095 15 = 10 ∧ acceleratedOrbit 15 26095 = 47027 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26095) = 3 ^ 10 * m + 47027 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26095.1, data_15_26095.2]

/-- Complete interval computation for depth 15, residue 26096. -/
theorem bounds_15_26096 : exactInterval 15 26096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26096 : oddCount 26096 15 = 6 ∧ acceleratedOrbit 15 26096 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26096) = 3 ^ 6 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26096.1, data_15_26096.2]

/-- Complete interval computation for depth 15, residue 26097. -/
theorem bounds_15_26097 : exactInterval 15 26097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26097 : oddCount 26097 15 = 6 ∧ acceleratedOrbit 15 26097 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26097) = 3 ^ 6 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26097.1, data_15_26097.2]

/-- Complete interval computation for depth 15, residue 26098. -/
theorem bounds_15_26098 : exactInterval 15 26098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26098 : oddCount 26098 15 = 8 ∧ acceleratedOrbit 15 26098 = 5228 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26098) = 3 ^ 8 * m + 5228 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26098.1, data_15_26098.2]

/-- Complete interval computation for depth 15, residue 26099. -/
theorem bounds_15_26099 : exactInterval 15 26099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26099 : oddCount 26099 15 = 8 ∧ acceleratedOrbit 15 26099 = 5228 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26099) = 3 ^ 8 * m + 5228 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26099.1, data_15_26099.2]

/-- Complete interval computation for depth 15, residue 26100. -/
theorem bounds_15_26100 : exactInterval 15 26100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26100 : oddCount 26100 15 = 6 ∧ acceleratedOrbit 15 26100 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26100) = 3 ^ 6 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26100.1, data_15_26100.2]

/-- Complete interval computation for depth 15, residue 26101. -/
theorem bounds_15_26101 : exactInterval 15 26101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26101 : oddCount 26101 15 = 6 ∧ acceleratedOrbit 15 26101 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26101) = 3 ^ 6 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26101.1, data_15_26101.2]

/-- Complete interval computation for depth 15, residue 26102. -/
theorem bounds_15_26102 : exactInterval 15 26102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26102 : oddCount 26102 15 = 8 ∧ acceleratedOrbit 15 26102 = 5227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26102) = 3 ^ 8 * m + 5227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26102.1, data_15_26102.2]

/-- Complete interval computation for depth 15, residue 26103. -/
theorem bounds_15_26103 : exactInterval 15 26103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26103 : oddCount 26103 15 = 8 ∧ acceleratedOrbit 15 26103 = 5227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26103) = 3 ^ 8 * m + 5227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26103.1, data_15_26103.2]

/-- Complete interval computation for depth 15, residue 26104. -/
theorem bounds_15_26104 : exactInterval 15 26104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26104 : oddCount 26104 15 = 9 ∧ acceleratedOrbit 15 26104 = 15686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26104) = 3 ^ 9 * m + 15686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26104.1, data_15_26104.2]

/-- Complete interval computation for depth 15, residue 26105. -/
theorem bounds_15_26105 : exactInterval 15 26105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26105 : oddCount 26105 15 = 8 ∧ acceleratedOrbit 15 26105 = 5228 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26105) = 3 ^ 8 * m + 5228 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26105.1, data_15_26105.2]

/-- Complete interval computation for depth 15, residue 26106. -/
theorem bounds_15_26106 : exactInterval 15 26106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26106 : oddCount 26106 15 = 9 ∧ acceleratedOrbit 15 26106 = 15686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26106) = 3 ^ 9 * m + 15686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26106.1, data_15_26106.2]

/-- Complete interval computation for depth 15, residue 26107. -/
theorem bounds_15_26107 : exactInterval 15 26107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26107 : oddCount 26107 15 = 10 ∧ acceleratedOrbit 15 26107 = 47051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26107) = 3 ^ 10 * m + 47051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26107.1, data_15_26107.2]

/-- Complete interval computation for depth 15, residue 26108. -/
theorem bounds_15_26108 : exactInterval 15 26108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26108 : oddCount 26108 15 = 9 ∧ acceleratedOrbit 15 26108 = 15686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26108) = 3 ^ 9 * m + 15686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26108.1, data_15_26108.2]

/-- Complete interval computation for depth 15, residue 26109. -/
theorem bounds_15_26109 : exactInterval 15 26109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26109 : oddCount 26109 15 = 9 ∧ acceleratedOrbit 15 26109 = 15686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26109) = 3 ^ 9 * m + 15686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26109.1, data_15_26109.2]

/-- Complete interval computation for depth 15, residue 26110. -/
theorem bounds_15_26110 : exactInterval 15 26110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26110 : oddCount 26110 15 = 12 ∧ acceleratedOrbit 15 26110 = 423494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26110) = 3 ^ 12 * m + 423494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26110.1, data_15_26110.2]

/-- Complete interval computation for depth 15, residue 26111. -/
theorem bounds_15_26111 : exactInterval 15 26111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26111 : oddCount 26111 15 = 12 ∧ acceleratedOrbit 15 26111 = 423494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26111) = 3 ^ 12 * m + 423494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26111.1, data_15_26111.2]

/-- Complete interval computation for depth 15, residue 26112. -/
theorem bounds_15_26112 : exactInterval 15 26112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26112 : oddCount 26112 15 = 3 ∧ acceleratedOrbit 15 26112 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26112) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26112.1, data_15_26112.2]

/-- Complete interval computation for depth 15, residue 26113. -/
theorem bounds_15_26113 : exactInterval 15 26113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26113 : oddCount 26113 15 = 9 ∧ acceleratedOrbit 15 26113 = 15689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26113) = 3 ^ 9 * m + 15689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26113.1, data_15_26113.2]

/-- Complete interval computation for depth 15, residue 26114. -/
theorem bounds_15_26114 : exactInterval 15 26114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26114 : oddCount 26114 15 = 7 ∧ acceleratedOrbit 15 26114 = 1745 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26114) = 3 ^ 7 * m + 1745 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26114.1, data_15_26114.2]

/-- Complete interval computation for depth 15, residue 26115. -/
theorem bounds_15_26115 : exactInterval 15 26115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26115 : oddCount 26115 15 = 7 ∧ acceleratedOrbit 15 26115 = 1745 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26115) = 3 ^ 7 * m + 1745 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26115.1, data_15_26115.2]

end Collatz.Research.PassageAtlas.Batch0797
