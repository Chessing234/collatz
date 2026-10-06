import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0993

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 8069. -/
theorem bounds_13_8069 : exactInterval 13 8069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8069 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8069) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8069 : oddCount 8069 13 = 8 ∧ acceleratedOrbit 13 8069 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8069 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8069) = 3 ^ 8 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8069.1, data_13_8069.2]

/-- Complete interval computation for depth 13, residue 8070. -/
theorem bounds_13_8070 : exactInterval 13 8070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8070 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8070) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8070 : oddCount 8070 13 = 8 ∧ acceleratedOrbit 13 8070 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8070 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8070) = 3 ^ 8 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8070.1, data_13_8070.2]

/-- Complete interval computation for depth 13, residue 8071. -/
theorem bounds_13_8071 : exactInterval 13 8071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8071 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8071) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8071 : oddCount 8071 13 = 6 ∧ acceleratedOrbit 13 8071 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8071 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8071) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8071.1, data_13_8071.2]

/-- Complete interval computation for depth 13, residue 8072. -/
theorem bounds_13_8072 : exactInterval 13 8072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8072 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8072) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8072 : oddCount 8072 13 = 5 ∧ acceleratedOrbit 13 8072 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8072 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8072) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8072.1, data_13_8072.2]

/-- Complete interval computation for depth 13, residue 8073. -/
theorem bounds_13_8073 : exactInterval 13 8073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8073 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8073) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8073 : oddCount 8073 13 = 9 ∧ acceleratedOrbit 13 8073 = 19403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8073 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8073) = 3 ^ 9 * m + 19403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8073.1, data_13_8073.2]

/-- Complete interval computation for depth 13, residue 8074. -/
theorem bounds_13_8074 : exactInterval 13 8074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8074 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8074) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8074 : oddCount 8074 13 = 5 ∧ acceleratedOrbit 13 8074 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8074 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8074) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8074.1, data_13_8074.2]

/-- Complete interval computation for depth 13, residue 8075. -/
theorem bounds_13_8075 : exactInterval 13 8075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8075 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8075) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8075 : oddCount 8075 13 = 8 ∧ acceleratedOrbit 13 8075 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8075 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8075) = 3 ^ 8 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8075.1, data_13_8075.2]

/-- Complete interval computation for depth 13, residue 8076. -/
theorem bounds_13_8076 : exactInterval 13 8076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8076 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8076) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8076 : oddCount 8076 13 = 5 ∧ acceleratedOrbit 13 8076 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8076 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8076) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8076.1, data_13_8076.2]

/-- Complete interval computation for depth 13, residue 8077. -/
theorem bounds_13_8077 : exactInterval 13 8077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8077 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8077) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8077 : oddCount 8077 13 = 5 ∧ acceleratedOrbit 13 8077 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8077 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8077) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8077.1, data_13_8077.2]

/-- Complete interval computation for depth 13, residue 8078. -/
theorem bounds_13_8078 : exactInterval 13 8078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8078 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8078) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8078 : oddCount 8078 13 = 8 ∧ acceleratedOrbit 13 8078 = 6473 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8078 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8078) = 3 ^ 8 * m + 6473 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8078.1, data_13_8078.2]

/-- Complete interval computation for depth 13, residue 8079. -/
theorem bounds_13_8079 : exactInterval 13 8079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8079 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8079) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8079 : oddCount 8079 13 = 8 ∧ acceleratedOrbit 13 8079 = 6473 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8079 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8079) = 3 ^ 8 * m + 6473 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8079.1, data_13_8079.2]

/-- Complete interval computation for depth 13, residue 8080. -/
theorem bounds_13_8080 : exactInterval 13 8080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8080 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8080) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8080 : oddCount 8080 13 = 6 ∧ acceleratedOrbit 13 8080 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8080 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8080) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8080.1, data_13_8080.2]

/-- Complete interval computation for depth 13, residue 8081. -/
theorem bounds_13_8081 : exactInterval 13 8081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8081 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8081) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8081 : oddCount 8081 13 = 8 ∧ acceleratedOrbit 13 8081 = 6479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8081 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8081) = 3 ^ 8 * m + 6479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8081.1, data_13_8081.2]

/-- Complete interval computation for depth 13, residue 8082. -/
theorem bounds_13_8082 : exactInterval 13 8082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8082 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8082) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8082 : oddCount 8082 13 = 8 ∧ acceleratedOrbit 13 8082 = 6479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8082 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8082) = 3 ^ 8 * m + 6479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8082.1, data_13_8082.2]

/-- Complete interval computation for depth 13, residue 8083. -/
theorem bounds_13_8083 : exactInterval 13 8083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8083 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8083) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8083 : oddCount 8083 13 = 8 ∧ acceleratedOrbit 13 8083 = 6479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8083 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8083) = 3 ^ 8 * m + 6479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8083.1, data_13_8083.2]

end Collatz.Research.StoppingAtlas.Batch0993
