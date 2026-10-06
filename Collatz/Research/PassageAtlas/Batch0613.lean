import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0613

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20054. -/
theorem bounds_15_20054 : exactInterval 15 20054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20054 : oddCount 20054 15 = 7 ∧ acceleratedOrbit 15 20054 = 1340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20054) = 3 ^ 7 * m + 1340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20054.1, data_15_20054.2]

/-- Complete interval computation for depth 15, residue 20055. -/
theorem bounds_15_20055 : exactInterval 15 20055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20055 : oddCount 20055 15 = 7 ∧ acceleratedOrbit 15 20055 = 1340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20055) = 3 ^ 7 * m + 1340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20055.1, data_15_20055.2]

/-- Complete interval computation for depth 15, residue 20056. -/
theorem bounds_15_20056 : exactInterval 15 20056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20056 : oddCount 20056 15 = 5 ∧ acceleratedOrbit 15 20056 = 149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20056) = 3 ^ 5 * m + 149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20056.1, data_15_20056.2]

/-- Complete interval computation for depth 15, residue 20057. -/
theorem bounds_15_20057 : exactInterval 15 20057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20057 : oddCount 20057 15 = 7 ∧ acceleratedOrbit 15 20057 = 1339 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20057) = 3 ^ 7 * m + 1339 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20057.1, data_15_20057.2]

/-- Complete interval computation for depth 15, residue 20058. -/
theorem bounds_15_20058 : exactInterval 15 20058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20058 : oddCount 20058 15 = 5 ∧ acceleratedOrbit 15 20058 = 149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20058) = 3 ^ 5 * m + 149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20058.1, data_15_20058.2]

/-- Complete interval computation for depth 15, residue 20059. -/
theorem bounds_15_20059 : exactInterval 15 20059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20059 : oddCount 20059 15 = 10 ∧ acceleratedOrbit 15 20059 = 36152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20059) = 3 ^ 10 * m + 36152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20059.1, data_15_20059.2]

/-- Complete interval computation for depth 15, residue 20060. -/
theorem bounds_15_20060 : exactInterval 15 20060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20060 : oddCount 20060 15 = 5 ∧ acceleratedOrbit 15 20060 = 149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20060) = 3 ^ 5 * m + 149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20060.1, data_15_20060.2]

/-- Complete interval computation for depth 15, residue 20061. -/
theorem bounds_15_20061 : exactInterval 15 20061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20061 : oddCount 20061 15 = 5 ∧ acceleratedOrbit 15 20061 = 149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20061) = 3 ^ 5 * m + 149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20061.1, data_15_20061.2]

/-- Complete interval computation for depth 15, residue 20062. -/
theorem bounds_15_20062 : exactInterval 15 20062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20062 : oddCount 20062 15 = 8 ∧ acceleratedOrbit 15 20062 = 4018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20062) = 3 ^ 8 * m + 4018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20062.1, data_15_20062.2]

/-- Complete interval computation for depth 15, residue 20063. -/
theorem bounds_15_20063 : exactInterval 15 20063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20063 : oddCount 20063 15 = 8 ∧ acceleratedOrbit 15 20063 = 4018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20063) = 3 ^ 8 * m + 4018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20063.1, data_15_20063.2]

/-- Complete interval computation for depth 15, residue 20064. -/
theorem bounds_15_20064 : exactInterval 15 20064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20064 : oddCount 20064 15 = 6 ∧ acceleratedOrbit 15 20064 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20064) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20064.1, data_15_20064.2]

/-- Complete interval computation for depth 15, residue 20065. -/
theorem bounds_15_20065 : exactInterval 15 20065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20065 : oddCount 20065 15 = 7 ∧ acceleratedOrbit 15 20065 = 1340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20065) = 3 ^ 7 * m + 1340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20065.1, data_15_20065.2]

/-- Complete interval computation for depth 15, residue 20066. -/
theorem bounds_15_20066 : exactInterval 15 20066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20066 : oddCount 20066 15 = 5 ∧ acceleratedOrbit 15 20066 = 149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20066) = 3 ^ 5 * m + 149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20066.1, data_15_20066.2]

/-- Complete interval computation for depth 15, residue 20067. -/
theorem bounds_15_20067 : exactInterval 15 20067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20067 : oddCount 20067 15 = 5 ∧ acceleratedOrbit 15 20067 = 149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20067) = 3 ^ 5 * m + 149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20067.1, data_15_20067.2]

/-- Complete interval computation for depth 15, residue 20068. -/
theorem bounds_15_20068 : exactInterval 15 20068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20068 : oddCount 20068 15 = 5 ∧ acceleratedOrbit 15 20068 = 149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20068) = 3 ^ 5 * m + 149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20068.1, data_15_20068.2]

/-- Complete interval computation for depth 15, residue 20069. -/
theorem bounds_15_20069 : exactInterval 15 20069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20069 : oddCount 20069 15 = 5 ∧ acceleratedOrbit 15 20069 = 149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20069) = 3 ^ 5 * m + 149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20069.1, data_15_20069.2]

/-- Complete interval computation for depth 15, residue 20070. -/
theorem bounds_15_20070 : exactInterval 15 20070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20070 : oddCount 20070 15 = 5 ∧ acceleratedOrbit 15 20070 = 149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20070) = 3 ^ 5 * m + 149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20070.1, data_15_20070.2]

/-- Complete interval computation for depth 15, residue 20071. -/
theorem bounds_15_20071 : exactInterval 15 20071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20071 : oddCount 20071 15 = 8 ∧ acceleratedOrbit 15 20071 = 4019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20071) = 3 ^ 8 * m + 4019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20071.1, data_15_20071.2]

/-- Complete interval computation for depth 15, residue 20072. -/
theorem bounds_15_20072 : exactInterval 15 20072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20072 : oddCount 20072 15 = 6 ∧ acceleratedOrbit 15 20072 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20072) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20072.1, data_15_20072.2]

/-- Complete interval computation for depth 15, residue 20073. -/
theorem bounds_15_20073 : exactInterval 15 20073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20073 : oddCount 20073 15 = 11 ∧ acceleratedOrbit 15 20073 = 108530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20073) = 3 ^ 11 * m + 108530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20073.1, data_15_20073.2]

/-- Complete interval computation for depth 15, residue 20074. -/
theorem bounds_15_20074 : exactInterval 15 20074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20074 : oddCount 20074 15 = 6 ∧ acceleratedOrbit 15 20074 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20074) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20074.1, data_15_20074.2]

/-- Complete interval computation for depth 15, residue 20075. -/
theorem bounds_15_20075 : exactInterval 15 20075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20075 : oddCount 20075 15 = 7 ∧ acceleratedOrbit 15 20075 = 1340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20075) = 3 ^ 7 * m + 1340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20075.1, data_15_20075.2]

/-- Complete interval computation for depth 15, residue 20076. -/
theorem bounds_15_20076 : exactInterval 15 20076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20076 : oddCount 20076 15 = 8 ∧ acceleratedOrbit 15 20076 = 4022 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20076) = 3 ^ 8 * m + 4022 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20076.1, data_15_20076.2]

/-- Complete interval computation for depth 15, residue 20077. -/
theorem bounds_15_20077 : exactInterval 15 20077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20077 : oddCount 20077 15 = 8 ∧ acceleratedOrbit 15 20077 = 4022 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20077) = 3 ^ 8 * m + 4022 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20077.1, data_15_20077.2]

/-- Complete interval computation for depth 15, residue 20078. -/
theorem bounds_15_20078 : exactInterval 15 20078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20078 : oddCount 20078 15 = 8 ∧ acceleratedOrbit 15 20078 = 4022 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20078) = 3 ^ 8 * m + 4022 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20078.1, data_15_20078.2]

/-- Complete interval computation for depth 15, residue 20079. -/
theorem bounds_15_20079 : exactInterval 15 20079 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20079) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20079 : oddCount 20079 15 = 9 ∧ acceleratedOrbit 15 20079 = 12062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20079) = 3 ^ 9 * m + 12062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20079.1, data_15_20079.2]

/-- Complete interval computation for depth 15, residue 20080. -/
theorem bounds_15_20080 : exactInterval 15 20080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20080 : oddCount 20080 15 = 8 ∧ acceleratedOrbit 15 20080 = 4025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20080) = 3 ^ 8 * m + 4025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20080.1, data_15_20080.2]

/-- Complete interval computation for depth 15, residue 20081. -/
theorem bounds_15_20081 : exactInterval 15 20081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20081 : oddCount 20081 15 = 6 ∧ acceleratedOrbit 15 20081 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20081) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20081.1, data_15_20081.2]

/-- Complete interval computation for depth 15, residue 20082. -/
theorem bounds_15_20082 : exactInterval 15 20082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20082 : oddCount 20082 15 = 9 ∧ acceleratedOrbit 15 20082 = 12068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20082) = 3 ^ 9 * m + 12068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20082.1, data_15_20082.2]

/-- Complete interval computation for depth 15, residue 20083. -/
theorem bounds_15_20083 : exactInterval 15 20083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20083 : oddCount 20083 15 = 9 ∧ acceleratedOrbit 15 20083 = 12068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20083) = 3 ^ 9 * m + 12068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20083.1, data_15_20083.2]

/-- Complete interval computation for depth 15, residue 20084. -/
theorem bounds_15_20084 : exactInterval 15 20084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20084 : oddCount 20084 15 = 8 ∧ acceleratedOrbit 15 20084 = 4025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20084) = 3 ^ 8 * m + 4025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20084.1, data_15_20084.2]

/-- Complete interval computation for depth 15, residue 20085. -/
theorem bounds_15_20085 : exactInterval 15 20085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20085 : oddCount 20085 15 = 8 ∧ acceleratedOrbit 15 20085 = 4025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20085) = 3 ^ 8 * m + 4025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20085.1, data_15_20085.2]

end Collatz.Research.PassageAtlas.Batch0613
