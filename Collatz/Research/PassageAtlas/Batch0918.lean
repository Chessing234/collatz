import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0918

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30048. -/
theorem bounds_15_30048 : exactInterval 15 30048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30048 : oddCount 30048 15 = 6 ∧ acceleratedOrbit 15 30048 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30048) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30048.1, data_15_30048.2]

/-- Complete interval computation for depth 15, residue 30049. -/
theorem bounds_15_30049 : exactInterval 15 30049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30049 : oddCount 30049 15 = 9 ∧ acceleratedOrbit 15 30049 = 18053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30049) = 3 ^ 9 * m + 18053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30049.1, data_15_30049.2]

/-- Complete interval computation for depth 15, residue 30050. -/
theorem bounds_15_30050 : exactInterval 15 30050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30050 : oddCount 30050 15 = 5 ∧ acceleratedOrbit 15 30050 = 223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30050) = 3 ^ 5 * m + 223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30050.1, data_15_30050.2]

/-- Complete interval computation for depth 15, residue 30051. -/
theorem bounds_15_30051 : exactInterval 15 30051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30051 : oddCount 30051 15 = 5 ∧ acceleratedOrbit 15 30051 = 223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30051) = 3 ^ 5 * m + 223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30051.1, data_15_30051.2]

/-- Complete interval computation for depth 15, residue 30052. -/
theorem bounds_15_30052 : exactInterval 15 30052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30052 : oddCount 30052 15 = 5 ∧ acceleratedOrbit 15 30052 = 223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30052) = 3 ^ 5 * m + 223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30052.1, data_15_30052.2]

/-- Complete interval computation for depth 15, residue 30053. -/
theorem bounds_15_30053 : exactInterval 15 30053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30053 : oddCount 30053 15 = 5 ∧ acceleratedOrbit 15 30053 = 223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30053) = 3 ^ 5 * m + 223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30053.1, data_15_30053.2]

/-- Complete interval computation for depth 15, residue 30054. -/
theorem bounds_15_30054 : exactInterval 15 30054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30054 : oddCount 30054 15 = 5 ∧ acceleratedOrbit 15 30054 = 223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30054) = 3 ^ 5 * m + 223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30054.1, data_15_30054.2]

/-- Complete interval computation for depth 15, residue 30055. -/
theorem bounds_15_30055 : exactInterval 15 30055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30055 : oddCount 30055 15 = 11 ∧ acceleratedOrbit 15 30055 = 162488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30055) = 3 ^ 11 * m + 162488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30055.1, data_15_30055.2]

/-- Complete interval computation for depth 15, residue 30056. -/
theorem bounds_15_30056 : exactInterval 15 30056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30056 : oddCount 30056 15 = 6 ∧ acceleratedOrbit 15 30056 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30056) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30056.1, data_15_30056.2]

/-- Complete interval computation for depth 15, residue 30057. -/
theorem bounds_15_30057 : exactInterval 15 30057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30057 : oddCount 30057 15 = 8 ∧ acceleratedOrbit 15 30057 = 6020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30057) = 3 ^ 8 * m + 6020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30057.1, data_15_30057.2]

/-- Complete interval computation for depth 15, residue 30058. -/
theorem bounds_15_30058 : exactInterval 15 30058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30058 : oddCount 30058 15 = 6 ∧ acceleratedOrbit 15 30058 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30058) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30058.1, data_15_30058.2]

/-- Complete interval computation for depth 15, residue 30059. -/
theorem bounds_15_30059 : exactInterval 15 30059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30059 : oddCount 30059 15 = 9 ∧ acceleratedOrbit 15 30059 = 18058 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30059) = 3 ^ 9 * m + 18058 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30059.1, data_15_30059.2]

/-- Complete interval computation for depth 15, residue 30060. -/
theorem bounds_15_30060 : exactInterval 15 30060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30060 : oddCount 30060 15 = 9 ∧ acceleratedOrbit 15 30060 = 18062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30060) = 3 ^ 9 * m + 18062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30060.1, data_15_30060.2]

/-- Complete interval computation for depth 15, residue 30061. -/
theorem bounds_15_30061 : exactInterval 15 30061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30061 : oddCount 30061 15 = 9 ∧ acceleratedOrbit 15 30061 = 18062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30061) = 3 ^ 9 * m + 18062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30061.1, data_15_30061.2]

/-- Complete interval computation for depth 15, residue 30062. -/
theorem bounds_15_30062 : exactInterval 15 30062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30062 : oddCount 30062 15 = 9 ∧ acceleratedOrbit 15 30062 = 18062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30062) = 3 ^ 9 * m + 18062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30062.1, data_15_30062.2]

/-- Complete interval computation for depth 15, residue 30063. -/
theorem bounds_15_30063 : exactInterval 15 30063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30063 : oddCount 30063 15 = 10 ∧ acceleratedOrbit 15 30063 = 54179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30063) = 3 ^ 10 * m + 54179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30063.1, data_15_30063.2]

/-- Complete interval computation for depth 15, residue 30064. -/
theorem bounds_15_30064 : exactInterval 15 30064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30064 : oddCount 30064 15 = 6 ∧ acceleratedOrbit 15 30064 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30064) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30064.1, data_15_30064.2]

/-- Complete interval computation for depth 15, residue 30065. -/
theorem bounds_15_30065 : exactInterval 15 30065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30065 : oddCount 30065 15 = 6 ∧ acceleratedOrbit 15 30065 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30065) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30065.1, data_15_30065.2]

/-- Complete interval computation for depth 15, residue 30066. -/
theorem bounds_15_30066 : exactInterval 15 30066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30066 : oddCount 30066 15 = 5 ∧ acceleratedOrbit 15 30066 = 223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30066) = 3 ^ 5 * m + 223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30066.1, data_15_30066.2]

/-- Complete interval computation for depth 15, residue 30067. -/
theorem bounds_15_30067 : exactInterval 15 30067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30067 : oddCount 30067 15 = 5 ∧ acceleratedOrbit 15 30067 = 223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30067) = 3 ^ 5 * m + 223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30067.1, data_15_30067.2]

/-- Complete interval computation for depth 15, residue 30068. -/
theorem bounds_15_30068 : exactInterval 15 30068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30068 : oddCount 30068 15 = 6 ∧ acceleratedOrbit 15 30068 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30068) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30068.1, data_15_30068.2]

/-- Complete interval computation for depth 15, residue 30069. -/
theorem bounds_15_30069 : exactInterval 15 30069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30069 : oddCount 30069 15 = 6 ∧ acceleratedOrbit 15 30069 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30069) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30069.1, data_15_30069.2]

/-- Complete interval computation for depth 15, residue 30070. -/
theorem bounds_15_30070 : exactInterval 15 30070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30070 : oddCount 30070 15 = 8 ∧ acceleratedOrbit 15 30070 = 6022 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30070) = 3 ^ 8 * m + 6022 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30070.1, data_15_30070.2]

/-- Complete interval computation for depth 15, residue 30071. -/
theorem bounds_15_30071 : exactInterval 15 30071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30071 : oddCount 30071 15 = 8 ∧ acceleratedOrbit 15 30071 = 6022 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30071) = 3 ^ 8 * m + 6022 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30071.1, data_15_30071.2]

/-- Complete interval computation for depth 15, residue 30072. -/
theorem bounds_15_30072 : exactInterval 15 30072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30072 : oddCount 30072 15 = 7 ∧ acceleratedOrbit 15 30072 = 2008 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30072) = 3 ^ 7 * m + 2008 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30072.1, data_15_30072.2]

/-- Complete interval computation for depth 15, residue 30073. -/
theorem bounds_15_30073 : exactInterval 15 30073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30073 : oddCount 30073 15 = 10 ∧ acceleratedOrbit 15 30073 = 54197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30073) = 3 ^ 10 * m + 54197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30073.1, data_15_30073.2]

/-- Complete interval computation for depth 15, residue 30074. -/
theorem bounds_15_30074 : exactInterval 15 30074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30074 : oddCount 30074 15 = 7 ∧ acceleratedOrbit 15 30074 = 2008 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30074) = 3 ^ 7 * m + 2008 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30074.1, data_15_30074.2]

/-- Complete interval computation for depth 15, residue 30075. -/
theorem bounds_15_30075 : exactInterval 15 30075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30075 : oddCount 30075 15 = 8 ∧ acceleratedOrbit 15 30075 = 6023 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30075) = 3 ^ 8 * m + 6023 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30075.1, data_15_30075.2]

/-- Complete interval computation for depth 15, residue 30076. -/
theorem bounds_15_30076 : exactInterval 15 30076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30076 : oddCount 30076 15 = 7 ∧ acceleratedOrbit 15 30076 = 2008 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30076) = 3 ^ 7 * m + 2008 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30076.1, data_15_30076.2]

/-- Complete interval computation for depth 15, residue 30077. -/
theorem bounds_15_30077 : exactInterval 15 30077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30077 : oddCount 30077 15 = 7 ∧ acceleratedOrbit 15 30077 = 2008 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30077) = 3 ^ 7 * m + 2008 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30077.1, data_15_30077.2]

/-- Complete interval computation for depth 15, residue 30078. -/
theorem bounds_15_30078 : exactInterval 15 30078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30078 : oddCount 30078 15 = 10 ∧ acceleratedOrbit 15 30078 = 54206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30078) = 3 ^ 10 * m + 54206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30078.1, data_15_30078.2]

/-- Complete interval computation for depth 15, residue 30079. -/
theorem bounds_15_30079 : exactInterval 15 30079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30079 : oddCount 30079 15 = 10 ∧ acceleratedOrbit 15 30079 = 54206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30079) = 3 ^ 10 * m + 54206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30079.1, data_15_30079.2]

/-- Complete interval computation for depth 15, residue 30080. -/
theorem bounds_15_30080 : exactInterval 15 30080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30080 : oddCount 30080 15 = 6 ∧ acceleratedOrbit 15 30080 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30080) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30080.1, data_15_30080.2]

end Collatz.Research.PassageAtlas.Batch0918
