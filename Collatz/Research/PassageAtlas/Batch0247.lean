import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0247

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8060. -/
theorem bounds_15_8060 : exactInterval 15 8060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8060 : oddCount 8060 15 = 8 ∧ acceleratedOrbit 15 8060 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8060) = 3 ^ 8 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8060.1, data_15_8060.2]

/-- Complete interval computation for depth 15, residue 8061. -/
theorem bounds_15_8061 : exactInterval 15 8061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8061 : oddCount 8061 15 = 8 ∧ acceleratedOrbit 15 8061 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8061) = 3 ^ 8 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8061.1, data_15_8061.2]

/-- Complete interval computation for depth 15, residue 8062. -/
theorem bounds_15_8062 : exactInterval 15 8062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8062 : oddCount 8062 15 = 9 ∧ acceleratedOrbit 15 8062 = 4844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8062) = 3 ^ 9 * m + 4844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8062.1, data_15_8062.2]

/-- Complete interval computation for depth 15, residue 8063. -/
theorem bounds_15_8063 : exactInterval 15 8063 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8063) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8063 : oddCount 8063 15 = 9 ∧ acceleratedOrbit 15 8063 = 4844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8063) = 3 ^ 9 * m + 4844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8063.1, data_15_8063.2]

/-- Complete interval computation for depth 15, residue 8064. -/
theorem bounds_15_8064 : exactInterval 15 8064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8064 : oddCount 8064 15 = 6 ∧ acceleratedOrbit 15 8064 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8064) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8064.1, data_15_8064.2]

/-- Complete interval computation for depth 15, residue 8065. -/
theorem bounds_15_8065 : exactInterval 15 8065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8065 : oddCount 8065 15 = 7 ∧ acceleratedOrbit 15 8065 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8065) = 3 ^ 7 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8065.1, data_15_8065.2]

/-- Complete interval computation for depth 15, residue 8066. -/
theorem bounds_15_8066 : exactInterval 15 8066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8066 : oddCount 8066 15 = 8 ∧ acceleratedOrbit 15 8066 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8066) = 3 ^ 8 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8066.1, data_15_8066.2]

/-- Complete interval computation for depth 15, residue 8067. -/
theorem bounds_15_8067 : exactInterval 15 8067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8067 : oddCount 8067 15 = 8 ∧ acceleratedOrbit 15 8067 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8067) = 3 ^ 8 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8067.1, data_15_8067.2]

/-- Complete interval computation for depth 15, residue 8068. -/
theorem bounds_15_8068 : exactInterval 15 8068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8068 : oddCount 8068 15 = 9 ∧ acceleratedOrbit 15 8068 = 4853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8068) = 3 ^ 9 * m + 4853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8068.1, data_15_8068.2]

/-- Complete interval computation for depth 15, residue 8069. -/
theorem bounds_15_8069 : exactInterval 15 8069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8069 : oddCount 8069 15 = 9 ∧ acceleratedOrbit 15 8069 = 4853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8069) = 3 ^ 9 * m + 4853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8069.1, data_15_8069.2]

/-- Complete interval computation for depth 15, residue 8070. -/
theorem bounds_15_8070 : exactInterval 15 8070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8070 : oddCount 8070 15 = 9 ∧ acceleratedOrbit 15 8070 = 4853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8070) = 3 ^ 9 * m + 4853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8070.1, data_15_8070.2]

/-- Complete interval computation for depth 15, residue 8071. -/
theorem bounds_15_8071 : exactInterval 15 8071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8071 : oddCount 8071 15 = 8 ∧ acceleratedOrbit 15 8071 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8071) = 3 ^ 8 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8071.1, data_15_8071.2]

/-- Complete interval computation for depth 15, residue 8072. -/
theorem bounds_15_8072 : exactInterval 15 8072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8072 : oddCount 8072 15 = 6 ∧ acceleratedOrbit 15 8072 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8072) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8072.1, data_15_8072.2]

/-- Complete interval computation for depth 15, residue 8073. -/
theorem bounds_15_8073 : exactInterval 15 8073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8073 : oddCount 8073 15 = 11 ∧ acceleratedOrbit 15 8073 = 43658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8073) = 3 ^ 11 * m + 43658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8073.1, data_15_8073.2]

/-- Complete interval computation for depth 15, residue 8074. -/
theorem bounds_15_8074 : exactInterval 15 8074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8074 : oddCount 8074 15 = 6 ∧ acceleratedOrbit 15 8074 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8074) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8074.1, data_15_8074.2]

/-- Complete interval computation for depth 15, residue 8075. -/
theorem bounds_15_8075 : exactInterval 15 8075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8075 : oddCount 8075 15 = 9 ∧ acceleratedOrbit 15 8075 = 4853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8075) = 3 ^ 9 * m + 4853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8075.1, data_15_8075.2]

/-- Complete interval computation for depth 15, residue 8076. -/
theorem bounds_15_8076 : exactInterval 15 8076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8076 : oddCount 8076 15 = 6 ∧ acceleratedOrbit 15 8076 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8076) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8076.1, data_15_8076.2]

/-- Complete interval computation for depth 15, residue 8077. -/
theorem bounds_15_8077 : exactInterval 15 8077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8077 : oddCount 8077 15 = 6 ∧ acceleratedOrbit 15 8077 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8077) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8077.1, data_15_8077.2]

/-- Complete interval computation for depth 15, residue 8078. -/
theorem bounds_15_8078 : exactInterval 15 8078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8078 : oddCount 8078 15 = 9 ∧ acceleratedOrbit 15 8078 = 4855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8078) = 3 ^ 9 * m + 4855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8078.1, data_15_8078.2]

/-- Complete interval computation for depth 15, residue 8079. -/
theorem bounds_15_8079 : exactInterval 15 8079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8079 : oddCount 8079 15 = 9 ∧ acceleratedOrbit 15 8079 = 4855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8079) = 3 ^ 9 * m + 4855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8079.1, data_15_8079.2]

/-- Complete interval computation for depth 15, residue 8080. -/
theorem bounds_15_8080 : exactInterval 15 8080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8080 : oddCount 8080 15 = 7 ∧ acceleratedOrbit 15 8080 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8080) = 3 ^ 7 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8080.1, data_15_8080.2]

/-- Complete interval computation for depth 15, residue 8081. -/
theorem bounds_15_8081 : exactInterval 15 8081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8081 : oddCount 8081 15 = 10 ∧ acceleratedOrbit 15 8081 = 14579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8081) = 3 ^ 10 * m + 14579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8081.1, data_15_8081.2]

/-- Complete interval computation for depth 15, residue 8082. -/
theorem bounds_15_8082 : exactInterval 15 8082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8082 : oddCount 8082 15 = 10 ∧ acceleratedOrbit 15 8082 = 14579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8082) = 3 ^ 10 * m + 14579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8082.1, data_15_8082.2]

/-- Complete interval computation for depth 15, residue 8083. -/
theorem bounds_15_8083 : exactInterval 15 8083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8083 : oddCount 8083 15 = 10 ∧ acceleratedOrbit 15 8083 = 14579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8083) = 3 ^ 10 * m + 14579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8083.1, data_15_8083.2]

/-- Complete interval computation for depth 15, residue 8084. -/
theorem bounds_15_8084 : exactInterval 15 8084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8084 : oddCount 8084 15 = 7 ∧ acceleratedOrbit 15 8084 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8084) = 3 ^ 7 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8084.1, data_15_8084.2]

/-- Complete interval computation for depth 15, residue 8085. -/
theorem bounds_15_8085 : exactInterval 15 8085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8085 : oddCount 8085 15 = 7 ∧ acceleratedOrbit 15 8085 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8085) = 3 ^ 7 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8085.1, data_15_8085.2]

/-- Complete interval computation for depth 15, residue 8086. -/
theorem bounds_15_8086 : exactInterval 15 8086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8086 : oddCount 8086 15 = 4 ∧ acceleratedOrbit 15 8086 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8086) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8086.1, data_15_8086.2]

/-- Complete interval computation for depth 15, residue 8087. -/
theorem bounds_15_8087 : exactInterval 15 8087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8087 : oddCount 8087 15 = 4 ∧ acceleratedOrbit 15 8087 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8087) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8087.1, data_15_8087.2]

/-- Complete interval computation for depth 15, residue 8088. -/
theorem bounds_15_8088 : exactInterval 15 8088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8088 : oddCount 8088 15 = 7 ∧ acceleratedOrbit 15 8088 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8088) = 3 ^ 7 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8088.1, data_15_8088.2]

/-- Complete interval computation for depth 15, residue 8089. -/
theorem bounds_15_8089 : exactInterval 15 8089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8089 : oddCount 8089 15 = 4 ∧ acceleratedOrbit 15 8089 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8089) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8089.1, data_15_8089.2]

/-- Complete interval computation for depth 15, residue 8090. -/
theorem bounds_15_8090 : exactInterval 15 8090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8090 : oddCount 8090 15 = 7 ∧ acceleratedOrbit 15 8090 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8090) = 3 ^ 7 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8090.1, data_15_8090.2]

/-- Complete interval computation for depth 15, residue 8091. -/
theorem bounds_15_8091 : exactInterval 15 8091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8091 : oddCount 8091 15 = 9 ∧ acceleratedOrbit 15 8091 = 4862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8091) = 3 ^ 9 * m + 4862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8091.1, data_15_8091.2]

/-- Complete interval computation for depth 15, residue 8092. -/
theorem bounds_15_8092 : exactInterval 15 8092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8092 : oddCount 8092 15 = 8 ∧ acceleratedOrbit 15 8092 = 1622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8092) = 3 ^ 8 * m + 1622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8092.1, data_15_8092.2]

end Collatz.Research.PassageAtlas.Batch0247
