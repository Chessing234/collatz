import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0491

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16056. -/
theorem bounds_15_16056 : exactInterval 15 16056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16056 : oddCount 16056 15 = 7 ∧ acceleratedOrbit 15 16056 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16056) = 3 ^ 7 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16056.1, data_15_16056.2]

/-- Complete interval computation for depth 15, residue 16057. -/
theorem bounds_15_16057 : exactInterval 15 16057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16057 : oddCount 16057 15 = 7 ∧ acceleratedOrbit 15 16057 = 1072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16057) = 3 ^ 7 * m + 1072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16057.1, data_15_16057.2]

/-- Complete interval computation for depth 15, residue 16058. -/
theorem bounds_15_16058 : exactInterval 15 16058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16058 : oddCount 16058 15 = 7 ∧ acceleratedOrbit 15 16058 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16058) = 3 ^ 7 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16058.1, data_15_16058.2]

/-- Complete interval computation for depth 15, residue 16059. -/
theorem bounds_15_16059 : exactInterval 15 16059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16059 : oddCount 16059 15 = 7 ∧ acceleratedOrbit 15 16059 = 1072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16059) = 3 ^ 7 * m + 1072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16059.1, data_15_16059.2]

/-- Complete interval computation for depth 15, residue 16060. -/
theorem bounds_15_16060 : exactInterval 15 16060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16060 : oddCount 16060 15 = 7 ∧ acceleratedOrbit 15 16060 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16060) = 3 ^ 7 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16060.1, data_15_16060.2]

/-- Complete interval computation for depth 15, residue 16061. -/
theorem bounds_15_16061 : exactInterval 15 16061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16061 : oddCount 16061 15 = 7 ∧ acceleratedOrbit 15 16061 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16061) = 3 ^ 7 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16061.1, data_15_16061.2]

/-- Complete interval computation for depth 15, residue 16062. -/
theorem bounds_15_16062 : exactInterval 15 16062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16062 : oddCount 16062 15 = 7 ∧ acceleratedOrbit 15 16062 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16062) = 3 ^ 7 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16062.1, data_15_16062.2]

/-- Complete interval computation for depth 15, residue 16063. -/
theorem bounds_15_16063 : exactInterval 15 16063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16063 : oddCount 16063 15 = 11 ∧ acceleratedOrbit 15 16063 = 86845 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16063) = 3 ^ 11 * m + 86845 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16063.1, data_15_16063.2]

/-- Complete interval computation for depth 15, residue 16064. -/
theorem bounds_15_16064 : exactInterval 15 16064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16064 : oddCount 16064 15 = 7 ∧ acceleratedOrbit 15 16064 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16064) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16064.1, data_15_16064.2]

/-- Complete interval computation for depth 15, residue 16065. -/
theorem bounds_15_16065 : exactInterval 15 16065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16065 : oddCount 16065 15 = 7 ∧ acceleratedOrbit 15 16065 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16065) = 3 ^ 7 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16065.1, data_15_16065.2]

/-- Complete interval computation for depth 15, residue 16066. -/
theorem bounds_15_16066 : exactInterval 15 16066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16066 : oddCount 16066 15 = 8 ∧ acceleratedOrbit 15 16066 = 3218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16066) = 3 ^ 8 * m + 3218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16066.1, data_15_16066.2]

/-- Complete interval computation for depth 15, residue 16067. -/
theorem bounds_15_16067 : exactInterval 15 16067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16067 : oddCount 16067 15 = 8 ∧ acceleratedOrbit 15 16067 = 3218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16067) = 3 ^ 8 * m + 3218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16067.1, data_15_16067.2]

/-- Complete interval computation for depth 15, residue 16068. -/
theorem bounds_15_16068 : exactInterval 15 16068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16068 : oddCount 16068 15 = 4 ∧ acceleratedOrbit 15 16068 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16068) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16068.1, data_15_16068.2]

/-- Complete interval computation for depth 15, residue 16069. -/
theorem bounds_15_16069 : exactInterval 15 16069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16069 : oddCount 16069 15 = 4 ∧ acceleratedOrbit 15 16069 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16069) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16069.1, data_15_16069.2]

/-- Complete interval computation for depth 15, residue 16070. -/
theorem bounds_15_16070 : exactInterval 15 16070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16070 : oddCount 16070 15 = 4 ∧ acceleratedOrbit 15 16070 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16070) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16070.1, data_15_16070.2]

/-- Complete interval computation for depth 15, residue 16071. -/
theorem bounds_15_16071 : exactInterval 15 16071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16071 : oddCount 16071 15 = 7 ∧ acceleratedOrbit 15 16071 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16071) = 3 ^ 7 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16071.1, data_15_16071.2]

/-- Complete interval computation for depth 15, residue 16072. -/
theorem bounds_15_16072 : exactInterval 15 16072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16072 : oddCount 16072 15 = 4 ∧ acceleratedOrbit 15 16072 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16072) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16072.1, data_15_16072.2]

/-- Complete interval computation for depth 15, residue 16073. -/
theorem bounds_15_16073 : exactInterval 15 16073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16073 : oddCount 16073 15 = 9 ∧ acceleratedOrbit 15 16073 = 9659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16073) = 3 ^ 9 * m + 9659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16073.1, data_15_16073.2]

/-- Complete interval computation for depth 15, residue 16074. -/
theorem bounds_15_16074 : exactInterval 15 16074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16074 : oddCount 16074 15 = 4 ∧ acceleratedOrbit 15 16074 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16074) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16074.1, data_15_16074.2]

/-- Complete interval computation for depth 15, residue 16075. -/
theorem bounds_15_16075 : exactInterval 15 16075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16075 : oddCount 16075 15 = 9 ∧ acceleratedOrbit 15 16075 = 9659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16075) = 3 ^ 9 * m + 9659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16075.1, data_15_16075.2]

/-- Complete interval computation for depth 15, residue 16076. -/
theorem bounds_15_16076 : exactInterval 15 16076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16076 : oddCount 16076 15 = 4 ∧ acceleratedOrbit 15 16076 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16076) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16076.1, data_15_16076.2]

/-- Complete interval computation for depth 15, residue 16077. -/
theorem bounds_15_16077 : exactInterval 15 16077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16077 : oddCount 16077 15 = 4 ∧ acceleratedOrbit 15 16077 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16077) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16077.1, data_15_16077.2]

/-- Complete interval computation for depth 15, residue 16078. -/
theorem bounds_15_16078 : exactInterval 15 16078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16078 : oddCount 16078 15 = 11 ∧ acceleratedOrbit 15 16078 = 86933 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16078) = 3 ^ 11 * m + 86933 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16078.1, data_15_16078.2]

/-- Complete interval computation for depth 15, residue 16079. -/
theorem bounds_15_16079 : exactInterval 15 16079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16079 : oddCount 16079 15 = 11 ∧ acceleratedOrbit 15 16079 = 86933 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16079) = 3 ^ 11 * m + 86933 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16079.1, data_15_16079.2]

/-- Complete interval computation for depth 15, residue 16080. -/
theorem bounds_15_16080 : exactInterval 15 16080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16080 : oddCount 16080 15 = 7 ∧ acceleratedOrbit 15 16080 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16080) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16080.1, data_15_16080.2]

/-- Complete interval computation for depth 15, residue 16081. -/
theorem bounds_15_16081 : exactInterval 15 16081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16081 : oddCount 16081 15 = 9 ∧ acceleratedOrbit 15 16081 = 9665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16081) = 3 ^ 9 * m + 9665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16081.1, data_15_16081.2]

/-- Complete interval computation for depth 15, residue 16082. -/
theorem bounds_15_16082 : exactInterval 15 16082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16082 : oddCount 16082 15 = 9 ∧ acceleratedOrbit 15 16082 = 9665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16082) = 3 ^ 9 * m + 9665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16082.1, data_15_16082.2]

/-- Complete interval computation for depth 15, residue 16083. -/
theorem bounds_15_16083 : exactInterval 15 16083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16083 : oddCount 16083 15 = 9 ∧ acceleratedOrbit 15 16083 = 9665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16083) = 3 ^ 9 * m + 9665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16083.1, data_15_16083.2]

/-- Complete interval computation for depth 15, residue 16084. -/
theorem bounds_15_16084 : exactInterval 15 16084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16084 : oddCount 16084 15 = 7 ∧ acceleratedOrbit 15 16084 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16084) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16084.1, data_15_16084.2]

/-- Complete interval computation for depth 15, residue 16085. -/
theorem bounds_15_16085 : exactInterval 15 16085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16085 : oddCount 16085 15 = 7 ∧ acceleratedOrbit 15 16085 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16085) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16085.1, data_15_16085.2]

/-- Complete interval computation for depth 15, residue 16086. -/
theorem bounds_15_16086 : exactInterval 15 16086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16086 : oddCount 16086 15 = 6 ∧ acceleratedOrbit 15 16086 = 358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16086) = 3 ^ 6 * m + 358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16086.1, data_15_16086.2]

/-- Complete interval computation for depth 15, residue 16087. -/
theorem bounds_15_16087 : exactInterval 15 16087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16087 : oddCount 16087 15 = 6 ∧ acceleratedOrbit 15 16087 = 358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16087) = 3 ^ 6 * m + 358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16087.1, data_15_16087.2]

/-- Complete interval computation for depth 15, residue 16088. -/
theorem bounds_15_16088 : exactInterval 15 16088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16088 : oddCount 16088 15 = 7 ∧ acceleratedOrbit 15 16088 = 1075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16088) = 3 ^ 7 * m + 1075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16088.1, data_15_16088.2]

end Collatz.Research.PassageAtlas.Batch0491
