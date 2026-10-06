import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0928

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7070. -/
theorem bounds_13_7070 : exactInterval 13 7070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7070 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7070) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7070 : oddCount 7070 13 = 8 ∧ acceleratedOrbit 13 7070 = 5665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7070 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7070) = 3 ^ 8 * m + 5665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7070.1, data_13_7070.2]

/-- Complete interval computation for depth 13, residue 7071. -/
theorem bounds_13_7071 : exactInterval 13 7071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7071 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7071) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7071 : oddCount 7071 13 = 7 ∧ acceleratedOrbit 13 7071 = 1888 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7071 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7071) = 3 ^ 7 * m + 1888 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7071.1, data_13_7071.2]

/-- Complete interval computation for depth 13, residue 7072. -/
theorem bounds_13_7072 : exactInterval 13 7072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7072 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7072) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7072 : oddCount 7072 13 = 4 ∧ acceleratedOrbit 13 7072 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7072 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7072) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7072.1, data_13_7072.2]

/-- Complete interval computation for depth 13, residue 7073. -/
theorem bounds_13_7073 : exactInterval 13 7073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7073 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7073) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7073 : oddCount 7073 13 = 8 ∧ acceleratedOrbit 13 7073 = 5669 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7073 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7073) = 3 ^ 8 * m + 5669 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7073.1, data_13_7073.2]

/-- Complete interval computation for depth 13, residue 7074. -/
theorem bounds_13_7074 : exactInterval 13 7074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7074 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7074) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7074 : oddCount 7074 13 = 4 ∧ acceleratedOrbit 13 7074 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7074 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7074) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7074.1, data_13_7074.2]

/-- Complete interval computation for depth 13, residue 7075. -/
theorem bounds_13_7075 : exactInterval 13 7075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7075 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7075) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7075 : oddCount 7075 13 = 4 ∧ acceleratedOrbit 13 7075 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7075 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7075) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7075.1, data_13_7075.2]

/-- Complete interval computation for depth 13, residue 7076. -/
theorem bounds_13_7076 : exactInterval 13 7076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7076 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7076) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7076 : oddCount 7076 13 = 7 ∧ acceleratedOrbit 13 7076 = 1891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7076 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7076) = 3 ^ 7 * m + 1891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7076.1, data_13_7076.2]

/-- Complete interval computation for depth 13, residue 7077. -/
theorem bounds_13_7077 : exactInterval 13 7077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7077 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7077) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7077 : oddCount 7077 13 = 7 ∧ acceleratedOrbit 13 7077 = 1891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7077 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7077) = 3 ^ 7 * m + 1891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7077.1, data_13_7077.2]

/-- Complete interval computation for depth 13, residue 7078. -/
theorem bounds_13_7078 : exactInterval 13 7078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7078 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7078) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7078 : oddCount 7078 13 = 7 ∧ acceleratedOrbit 13 7078 = 1891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7078 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7078) = 3 ^ 7 * m + 1891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7078.1, data_13_7078.2]

/-- Complete interval computation for depth 13, residue 7079. -/
theorem bounds_13_7079 : exactInterval 13 7079 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7079 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7079) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7079 : oddCount 7079 13 = 8 ∧ acceleratedOrbit 13 7079 = 5671 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7079 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7079) = 3 ^ 8 * m + 5671 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7079.1, data_13_7079.2]

/-- Complete interval computation for depth 13, residue 7080. -/
theorem bounds_13_7080 : exactInterval 13 7080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7080 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7080) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7080 : oddCount 7080 13 = 4 ∧ acceleratedOrbit 13 7080 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7080 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7080) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7080.1, data_13_7080.2]

/-- Complete interval computation for depth 13, residue 7081. -/
theorem bounds_13_7081 : exactInterval 13 7081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7081 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7081) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7081 : oddCount 7081 13 = 9 ∧ acceleratedOrbit 13 7081 = 17018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7081 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7081) = 3 ^ 9 * m + 17018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7081.1, data_13_7081.2]

/-- Complete interval computation for depth 13, residue 7082. -/
theorem bounds_13_7082 : exactInterval 13 7082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7082 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7082) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7082 : oddCount 7082 13 = 4 ∧ acceleratedOrbit 13 7082 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7082 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7082) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7082.1, data_13_7082.2]

/-- Complete interval computation for depth 13, residue 7083. -/
theorem bounds_13_7083 : exactInterval 13 7083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7083 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7083) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7083 : oddCount 7083 13 = 7 ∧ acceleratedOrbit 13 7083 = 1892 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7083 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7083) = 3 ^ 7 * m + 1892 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7083.1, data_13_7083.2]

/-- Complete interval computation for depth 13, residue 7084. -/
theorem bounds_13_7084 : exactInterval 13 7084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7084 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7084) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7084 : oddCount 7084 13 = 6 ∧ acceleratedOrbit 13 7084 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7084 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7084) = 3 ^ 6 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7084.1, data_13_7084.2]

/-- Complete interval computation for depth 13, residue 7085. -/
theorem bounds_13_7085 : exactInterval 13 7085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7085 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7085) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7085 : oddCount 7085 13 = 6 ∧ acceleratedOrbit 13 7085 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7085 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7085) = 3 ^ 6 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7085.1, data_13_7085.2]

end Collatz.Research.StoppingAtlas.Batch0928
