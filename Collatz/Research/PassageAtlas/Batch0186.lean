import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0186

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6062. -/
theorem bounds_15_6062 : exactInterval 15 6062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6062 : oddCount 6062 15 = 11 ∧ acceleratedOrbit 15 6062 = 32804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6062) = 3 ^ 11 * m + 32804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6062.1, data_15_6062.2]

/-- Complete interval computation for depth 15, residue 6063. -/
theorem bounds_15_6063 : exactInterval 15 6063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6063 : oddCount 6063 15 = 10 ∧ acceleratedOrbit 15 6063 = 10934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6063) = 3 ^ 10 * m + 10934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6063.1, data_15_6063.2]

/-- Complete interval computation for depth 15, residue 6064. -/
theorem bounds_15_6064 : exactInterval 15 6064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6064 : oddCount 6064 15 = 7 ∧ acceleratedOrbit 15 6064 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6064) = 3 ^ 7 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6064.1, data_15_6064.2]

/-- Complete interval computation for depth 15, residue 6065. -/
theorem bounds_15_6065 : exactInterval 15 6065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6065 : oddCount 6065 15 = 3 ∧ acceleratedOrbit 15 6065 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6065) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6065.1, data_15_6065.2]

/-- Complete interval computation for depth 15, residue 6066. -/
theorem bounds_15_6066 : exactInterval 15 6066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6066 : oddCount 6066 15 = 3 ∧ acceleratedOrbit 15 6066 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6066) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6066.1, data_15_6066.2]

/-- Complete interval computation for depth 15, residue 6067. -/
theorem bounds_15_6067 : exactInterval 15 6067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6067 : oddCount 6067 15 = 3 ∧ acceleratedOrbit 15 6067 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6067) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6067.1, data_15_6067.2]

/-- Complete interval computation for depth 15, residue 6068. -/
theorem bounds_15_6068 : exactInterval 15 6068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6068 : oddCount 6068 15 = 7 ∧ acceleratedOrbit 15 6068 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6068) = 3 ^ 7 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6068.1, data_15_6068.2]

/-- Complete interval computation for depth 15, residue 6069. -/
theorem bounds_15_6069 : exactInterval 15 6069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6069 : oddCount 6069 15 = 7 ∧ acceleratedOrbit 15 6069 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6069) = 3 ^ 7 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6069.1, data_15_6069.2]

/-- Complete interval computation for depth 15, residue 6070. -/
theorem bounds_15_6070 : exactInterval 15 6070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6070 : oddCount 6070 15 = 8 ∧ acceleratedOrbit 15 6070 = 1217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6070) = 3 ^ 8 * m + 1217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6070.1, data_15_6070.2]

/-- Complete interval computation for depth 15, residue 6071. -/
theorem bounds_15_6071 : exactInterval 15 6071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6071 : oddCount 6071 15 = 8 ∧ acceleratedOrbit 15 6071 = 1217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6071) = 3 ^ 8 * m + 1217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6071.1, data_15_6071.2]

/-- Complete interval computation for depth 15, residue 6072. -/
theorem bounds_15_6072 : exactInterval 15 6072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6072 : oddCount 6072 15 = 7 ∧ acceleratedOrbit 15 6072 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6072) = 3 ^ 7 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6072.1, data_15_6072.2]

/-- Complete interval computation for depth 15, residue 6073. -/
theorem bounds_15_6073 : exactInterval 15 6073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6073 : oddCount 6073 15 = 7 ∧ acceleratedOrbit 15 6073 = 406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6073) = 3 ^ 7 * m + 406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6073.1, data_15_6073.2]

/-- Complete interval computation for depth 15, residue 6074. -/
theorem bounds_15_6074 : exactInterval 15 6074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6074 : oddCount 6074 15 = 7 ∧ acceleratedOrbit 15 6074 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6074) = 3 ^ 7 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6074.1, data_15_6074.2]

/-- Complete interval computation for depth 15, residue 6075. -/
theorem bounds_15_6075 : exactInterval 15 6075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6075 : oddCount 6075 15 = 7 ∧ acceleratedOrbit 15 6075 = 406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6075) = 3 ^ 7 * m + 406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6075.1, data_15_6075.2]

/-- Complete interval computation for depth 15, residue 6076. -/
theorem bounds_15_6076 : exactInterval 15 6076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6076 : oddCount 6076 15 = 9 ∧ acceleratedOrbit 15 6076 = 3653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6076) = 3 ^ 9 * m + 3653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6076.1, data_15_6076.2]

/-- Complete interval computation for depth 15, residue 6077. -/
theorem bounds_15_6077 : exactInterval 15 6077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6077 : oddCount 6077 15 = 9 ∧ acceleratedOrbit 15 6077 = 3653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6077) = 3 ^ 9 * m + 3653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6077.1, data_15_6077.2]

/-- Complete interval computation for depth 15, residue 6078. -/
theorem bounds_15_6078 : exactInterval 15 6078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6078 : oddCount 6078 15 = 9 ∧ acceleratedOrbit 15 6078 = 3653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6078) = 3 ^ 9 * m + 3653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6078.1, data_15_6078.2]

/-- Complete interval computation for depth 15, residue 6079. -/
theorem bounds_15_6079 : exactInterval 15 6079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6079 : oddCount 6079 15 = 10 ∧ acceleratedOrbit 15 6079 = 10957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6079) = 3 ^ 10 * m + 10957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6079.1, data_15_6079.2]

/-- Complete interval computation for depth 15, residue 6080. -/
theorem bounds_15_6080 : exactInterval 15 6080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6080 : oddCount 6080 15 = 6 ∧ acceleratedOrbit 15 6080 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6080) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6080.1, data_15_6080.2]

/-- Complete interval computation for depth 15, residue 6081. -/
theorem bounds_15_6081 : exactInterval 15 6081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6081 : oddCount 6081 15 = 7 ∧ acceleratedOrbit 15 6081 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6081) = 3 ^ 7 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6081.1, data_15_6081.2]

/-- Complete interval computation for depth 15, residue 6082. -/
theorem bounds_15_6082 : exactInterval 15 6082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6082 : oddCount 6082 15 = 8 ∧ acceleratedOrbit 15 6082 = 1219 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6082) = 3 ^ 8 * m + 1219 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6082.1, data_15_6082.2]

/-- Complete interval computation for depth 15, residue 6083. -/
theorem bounds_15_6083 : exactInterval 15 6083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6083 : oddCount 6083 15 = 8 ∧ acceleratedOrbit 15 6083 = 1219 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6083) = 3 ^ 8 * m + 1219 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6083.1, data_15_6083.2]

/-- Complete interval computation for depth 15, residue 6084. -/
theorem bounds_15_6084 : exactInterval 15 6084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6084 : oddCount 6084 15 = 6 ∧ acceleratedOrbit 15 6084 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6084) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6084.1, data_15_6084.2]

/-- Complete interval computation for depth 15, residue 6085. -/
theorem bounds_15_6085 : exactInterval 15 6085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6085 : oddCount 6085 15 = 6 ∧ acceleratedOrbit 15 6085 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6085) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6085.1, data_15_6085.2]

/-- Complete interval computation for depth 15, residue 6086. -/
theorem bounds_15_6086 : exactInterval 15 6086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6086 : oddCount 6086 15 = 6 ∧ acceleratedOrbit 15 6086 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6086) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6086.1, data_15_6086.2]

/-- Complete interval computation for depth 15, residue 6087. -/
theorem bounds_15_6087 : exactInterval 15 6087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6087 : oddCount 6087 15 = 9 ∧ acceleratedOrbit 15 6087 = 3658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6087) = 3 ^ 9 * m + 3658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6087.1, data_15_6087.2]

/-- Complete interval computation for depth 15, residue 6088. -/
theorem bounds_15_6088 : exactInterval 15 6088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6088 : oddCount 6088 15 = 6 ∧ acceleratedOrbit 15 6088 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6088) = 3 ^ 6 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6088.1, data_15_6088.2]

/-- Complete interval computation for depth 15, residue 6089. -/
theorem bounds_15_6089 : exactInterval 15 6089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6089 : oddCount 6089 15 = 8 ∧ acceleratedOrbit 15 6089 = 1220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6089) = 3 ^ 8 * m + 1220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6089.1, data_15_6089.2]

/-- Complete interval computation for depth 15, residue 6090. -/
theorem bounds_15_6090 : exactInterval 15 6090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6090 : oddCount 6090 15 = 6 ∧ acceleratedOrbit 15 6090 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6090) = 3 ^ 6 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6090.1, data_15_6090.2]

/-- Complete interval computation for depth 15, residue 6091. -/
theorem bounds_15_6091 : exactInterval 15 6091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6091 : oddCount 6091 15 = 6 ∧ acceleratedOrbit 15 6091 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6091) = 3 ^ 6 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6091.1, data_15_6091.2]

/-- Complete interval computation for depth 15, residue 6092. -/
theorem bounds_15_6092 : exactInterval 15 6092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6092 : oddCount 6092 15 = 6 ∧ acceleratedOrbit 15 6092 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6092) = 3 ^ 6 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6092.1, data_15_6092.2]

/-- Complete interval computation for depth 15, residue 6093. -/
theorem bounds_15_6093 : exactInterval 15 6093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6093 : oddCount 6093 15 = 6 ∧ acceleratedOrbit 15 6093 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6093) = 3 ^ 6 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6093.1, data_15_6093.2]

end Collatz.Research.PassageAtlas.Batch0186
