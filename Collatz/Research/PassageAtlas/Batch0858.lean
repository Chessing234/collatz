import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0858

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28082. -/
theorem bounds_15_28082 : exactInterval 15 28082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28082 : oddCount 28082 15 = 7 ∧ acceleratedOrbit 15 28082 = 1876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28082) = 3 ^ 7 * m + 1876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28082.1, data_15_28082.2]

/-- Complete interval computation for depth 15, residue 28083. -/
theorem bounds_15_28083 : exactInterval 15 28083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28083 : oddCount 28083 15 = 7 ∧ acceleratedOrbit 15 28083 = 1876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28083) = 3 ^ 7 * m + 1876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28083.1, data_15_28083.2]

/-- Complete interval computation for depth 15, residue 28084. -/
theorem bounds_15_28084 : exactInterval 15 28084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28084 : oddCount 28084 15 = 7 ∧ acceleratedOrbit 15 28084 = 1876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28084) = 3 ^ 7 * m + 1876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28084.1, data_15_28084.2]

/-- Complete interval computation for depth 15, residue 28085. -/
theorem bounds_15_28085 : exactInterval 15 28085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28085 : oddCount 28085 15 = 7 ∧ acceleratedOrbit 15 28085 = 1876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28085) = 3 ^ 7 * m + 1876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28085.1, data_15_28085.2]

/-- Complete interval computation for depth 15, residue 28086. -/
theorem bounds_15_28086 : exactInterval 15 28086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28086 : oddCount 28086 15 = 9 ∧ acceleratedOrbit 15 28086 = 16874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28086) = 3 ^ 9 * m + 16874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28086.1, data_15_28086.2]

/-- Complete interval computation for depth 15, residue 28087. -/
theorem bounds_15_28087 : exactInterval 15 28087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28087 : oddCount 28087 15 = 9 ∧ acceleratedOrbit 15 28087 = 16874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28087) = 3 ^ 9 * m + 16874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28087.1, data_15_28087.2]

/-- Complete interval computation for depth 15, residue 28088. -/
theorem bounds_15_28088 : exactInterval 15 28088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28088 : oddCount 28088 15 = 7 ∧ acceleratedOrbit 15 28088 = 1876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28088) = 3 ^ 7 * m + 1876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28088.1, data_15_28088.2]

/-- Complete interval computation for depth 15, residue 28089. -/
theorem bounds_15_28089 : exactInterval 15 28089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28089 : oddCount 28089 15 = 7 ∧ acceleratedOrbit 15 28089 = 1876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28089) = 3 ^ 7 * m + 1876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28089.1, data_15_28089.2]

/-- Complete interval computation for depth 15, residue 28090. -/
theorem bounds_15_28090 : exactInterval 15 28090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28090 : oddCount 28090 15 = 7 ∧ acceleratedOrbit 15 28090 = 1876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28090) = 3 ^ 7 * m + 1876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28090.1, data_15_28090.2]

/-- Complete interval computation for depth 15, residue 28091. -/
theorem bounds_15_28091 : exactInterval 15 28091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28091 : oddCount 28091 15 = 6 ∧ acceleratedOrbit 15 28091 = 625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28091) = 3 ^ 6 * m + 625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28091.1, data_15_28091.2]

/-- Complete interval computation for depth 15, residue 28092. -/
theorem bounds_15_28092 : exactInterval 15 28092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28092 : oddCount 28092 15 = 8 ∧ acceleratedOrbit 15 28092 = 5626 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28092) = 3 ^ 8 * m + 5626 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28092.1, data_15_28092.2]

/-- Complete interval computation for depth 15, residue 28093. -/
theorem bounds_15_28093 : exactInterval 15 28093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28093 : oddCount 28093 15 = 8 ∧ acceleratedOrbit 15 28093 = 5626 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28093) = 3 ^ 8 * m + 5626 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28093.1, data_15_28093.2]

/-- Complete interval computation for depth 15, residue 28094. -/
theorem bounds_15_28094 : exactInterval 15 28094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28094 : oddCount 28094 15 = 8 ∧ acceleratedOrbit 15 28094 = 5626 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28094) = 3 ^ 8 * m + 5626 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28094.1, data_15_28094.2]

/-- Complete interval computation for depth 15, residue 28095. -/
theorem bounds_15_28095 : exactInterval 15 28095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28095 : oddCount 28095 15 = 10 ∧ acceleratedOrbit 15 28095 = 50630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28095) = 3 ^ 10 * m + 50630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28095.1, data_15_28095.2]

/-- Complete interval computation for depth 15, residue 28096. -/
theorem bounds_15_28096 : exactInterval 15 28096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28096 : oddCount 28096 15 = 5 ∧ acceleratedOrbit 15 28096 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28096) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28096.1, data_15_28096.2]

/-- Complete interval computation for depth 15, residue 28097. -/
theorem bounds_15_28097 : exactInterval 15 28097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28097 : oddCount 28097 15 = 8 ∧ acceleratedOrbit 15 28097 = 5627 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28097) = 3 ^ 8 * m + 5627 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28097.1, data_15_28097.2]

/-- Complete interval computation for depth 15, residue 28098. -/
theorem bounds_15_28098 : exactInterval 15 28098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28098 : oddCount 28098 15 = 8 ∧ acceleratedOrbit 15 28098 = 5627 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28098) = 3 ^ 8 * m + 5627 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28098.1, data_15_28098.2]

/-- Complete interval computation for depth 15, residue 28099. -/
theorem bounds_15_28099 : exactInterval 15 28099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28099 : oddCount 28099 15 = 8 ∧ acceleratedOrbit 15 28099 = 5627 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28099) = 3 ^ 8 * m + 5627 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28099.1, data_15_28099.2]

/-- Complete interval computation for depth 15, residue 28100. -/
theorem bounds_15_28100 : exactInterval 15 28100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28100 : oddCount 28100 15 = 5 ∧ acceleratedOrbit 15 28100 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28100) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28100.1, data_15_28100.2]

/-- Complete interval computation for depth 15, residue 28101. -/
theorem bounds_15_28101 : exactInterval 15 28101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28101 : oddCount 28101 15 = 5 ∧ acceleratedOrbit 15 28101 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28101) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28101.1, data_15_28101.2]

/-- Complete interval computation for depth 15, residue 28102. -/
theorem bounds_15_28102 : exactInterval 15 28102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28102 : oddCount 28102 15 = 5 ∧ acceleratedOrbit 15 28102 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28102) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28102.1, data_15_28102.2]

/-- Complete interval computation for depth 15, residue 28103. -/
theorem bounds_15_28103 : exactInterval 15 28103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28103 : oddCount 28103 15 = 7 ∧ acceleratedOrbit 15 28103 = 1876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28103) = 3 ^ 7 * m + 1876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28103.1, data_15_28103.2]

/-- Complete interval computation for depth 15, residue 28104. -/
theorem bounds_15_28104 : exactInterval 15 28104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28104 : oddCount 28104 15 = 5 ∧ acceleratedOrbit 15 28104 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28104) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28104.1, data_15_28104.2]

/-- Complete interval computation for depth 15, residue 28105. -/
theorem bounds_15_28105 : exactInterval 15 28105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28105 : oddCount 28105 15 = 8 ∧ acceleratedOrbit 15 28105 = 5629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28105) = 3 ^ 8 * m + 5629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28105.1, data_15_28105.2]

/-- Complete interval computation for depth 15, residue 28106. -/
theorem bounds_15_28106 : exactInterval 15 28106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28106 : oddCount 28106 15 = 5 ∧ acceleratedOrbit 15 28106 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28106) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28106.1, data_15_28106.2]

/-- Complete interval computation for depth 15, residue 28107. -/
theorem bounds_15_28107 : exactInterval 15 28107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28107 : oddCount 28107 15 = 9 ∧ acceleratedOrbit 15 28107 = 16888 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28107) = 3 ^ 9 * m + 16888 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28107.1, data_15_28107.2]

/-- Complete interval computation for depth 15, residue 28108. -/
theorem bounds_15_28108 : exactInterval 15 28108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28108 : oddCount 28108 15 = 5 ∧ acceleratedOrbit 15 28108 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28108) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28108.1, data_15_28108.2]

/-- Complete interval computation for depth 15, residue 28109. -/
theorem bounds_15_28109 : exactInterval 15 28109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28109 : oddCount 28109 15 = 5 ∧ acceleratedOrbit 15 28109 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28109) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28109.1, data_15_28109.2]

/-- Complete interval computation for depth 15, residue 28110. -/
theorem bounds_15_28110 : exactInterval 15 28110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28110 : oddCount 28110 15 = 11 ∧ acceleratedOrbit 15 28110 = 151982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28110) = 3 ^ 11 * m + 151982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28110.1, data_15_28110.2]

/-- Complete interval computation for depth 15, residue 28111. -/
theorem bounds_15_28111 : exactInterval 15 28111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28111 : oddCount 28111 15 = 11 ∧ acceleratedOrbit 15 28111 = 151982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28111) = 3 ^ 11 * m + 151982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28111.1, data_15_28111.2]

/-- Complete interval computation for depth 15, residue 28112. -/
theorem bounds_15_28112 : exactInterval 15 28112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28112 : oddCount 28112 15 = 5 ∧ acceleratedOrbit 15 28112 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28112) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28112.1, data_15_28112.2]

/-- Complete interval computation for depth 15, residue 28113. -/
theorem bounds_15_28113 : exactInterval 15 28113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28113 : oddCount 28113 15 = 5 ∧ acceleratedOrbit 15 28113 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28113) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28113.1, data_15_28113.2]

end Collatz.Research.PassageAtlas.Batch0858
