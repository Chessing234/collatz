import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0888

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29065. -/
theorem bounds_15_29065 : exactInterval 15 29065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29065 : oddCount 29065 15 = 7 ∧ acceleratedOrbit 15 29065 = 1940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29065) = 3 ^ 7 * m + 1940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29065.1, data_15_29065.2]

/-- Complete interval computation for depth 15, residue 29066. -/
theorem bounds_15_29066 : exactInterval 15 29066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29066 : oddCount 29066 15 = 8 ∧ acceleratedOrbit 15 29066 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29066) = 3 ^ 8 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29066.1, data_15_29066.2]

/-- Complete interval computation for depth 15, residue 29067. -/
theorem bounds_15_29067 : exactInterval 15 29067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29067 : oddCount 29067 15 = 9 ∧ acceleratedOrbit 15 29067 = 17462 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29067) = 3 ^ 9 * m + 17462 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29067.1, data_15_29067.2]

/-- Complete interval computation for depth 15, residue 29068. -/
theorem bounds_15_29068 : exactInterval 15 29068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29068 : oddCount 29068 15 = 8 ∧ acceleratedOrbit 15 29068 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29068) = 3 ^ 8 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29068.1, data_15_29068.2]

/-- Complete interval computation for depth 15, residue 29069. -/
theorem bounds_15_29069 : exactInterval 15 29069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29069 : oddCount 29069 15 = 8 ∧ acceleratedOrbit 15 29069 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29069) = 3 ^ 8 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29069.1, data_15_29069.2]

/-- Complete interval computation for depth 15, residue 29070. -/
theorem bounds_15_29070 : exactInterval 15 29070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29070 : oddCount 29070 15 = 8 ∧ acceleratedOrbit 15 29070 = 5822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29070) = 3 ^ 8 * m + 5822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29070.1, data_15_29070.2]

/-- Complete interval computation for depth 15, residue 29071. -/
theorem bounds_15_29071 : exactInterval 15 29071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29071 : oddCount 29071 15 = 8 ∧ acceleratedOrbit 15 29071 = 5822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29071) = 3 ^ 8 * m + 5822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29071.1, data_15_29071.2]

/-- Complete interval computation for depth 15, residue 29072. -/
theorem bounds_15_29072 : exactInterval 15 29072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29072 : oddCount 29072 15 = 8 ∧ acceleratedOrbit 15 29072 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29072) = 3 ^ 8 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29072.1, data_15_29072.2]

/-- Complete interval computation for depth 15, residue 29073. -/
theorem bounds_15_29073 : exactInterval 15 29073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29073 : oddCount 29073 15 = 7 ∧ acceleratedOrbit 15 29073 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29073) = 3 ^ 7 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29073.1, data_15_29073.2]

/-- Complete interval computation for depth 15, residue 29074. -/
theorem bounds_15_29074 : exactInterval 15 29074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29074 : oddCount 29074 15 = 7 ∧ acceleratedOrbit 15 29074 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29074) = 3 ^ 7 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29074.1, data_15_29074.2]

/-- Complete interval computation for depth 15, residue 29075. -/
theorem bounds_15_29075 : exactInterval 15 29075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29075 : oddCount 29075 15 = 7 ∧ acceleratedOrbit 15 29075 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29075) = 3 ^ 7 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29075.1, data_15_29075.2]

/-- Complete interval computation for depth 15, residue 29076. -/
theorem bounds_15_29076 : exactInterval 15 29076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29076 : oddCount 29076 15 = 8 ∧ acceleratedOrbit 15 29076 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29076) = 3 ^ 8 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29076.1, data_15_29076.2]

/-- Complete interval computation for depth 15, residue 29077. -/
theorem bounds_15_29077 : exactInterval 15 29077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29077 : oddCount 29077 15 = 8 ∧ acceleratedOrbit 15 29077 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29077) = 3 ^ 8 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29077.1, data_15_29077.2]

/-- Complete interval computation for depth 15, residue 29078. -/
theorem bounds_15_29078 : exactInterval 15 29078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29078 : oddCount 29078 15 = 8 ∧ acceleratedOrbit 15 29078 = 5825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29078) = 3 ^ 8 * m + 5825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29078.1, data_15_29078.2]

/-- Complete interval computation for depth 15, residue 29079. -/
theorem bounds_15_29079 : exactInterval 15 29079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29079 : oddCount 29079 15 = 8 ∧ acceleratedOrbit 15 29079 = 5825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29079) = 3 ^ 8 * m + 5825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29079.1, data_15_29079.2]

/-- Complete interval computation for depth 15, residue 29080. -/
theorem bounds_15_29080 : exactInterval 15 29080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29080 : oddCount 29080 15 = 8 ∧ acceleratedOrbit 15 29080 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29080) = 3 ^ 8 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29080.1, data_15_29080.2]

/-- Complete interval computation for depth 15, residue 29081. -/
theorem bounds_15_29081 : exactInterval 15 29081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29081 : oddCount 29081 15 = 8 ∧ acceleratedOrbit 15 29081 = 5825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29081) = 3 ^ 8 * m + 5825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29081.1, data_15_29081.2]

/-- Complete interval computation for depth 15, residue 29082. -/
theorem bounds_15_29082 : exactInterval 15 29082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29082 : oddCount 29082 15 = 8 ∧ acceleratedOrbit 15 29082 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29082) = 3 ^ 8 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29082.1, data_15_29082.2]

/-- Complete interval computation for depth 15, residue 29083. -/
theorem bounds_15_29083 : exactInterval 15 29083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29083 : oddCount 29083 15 = 9 ∧ acceleratedOrbit 15 29083 = 17471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29083) = 3 ^ 9 * m + 17471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29083.1, data_15_29083.2]

/-- Complete interval computation for depth 15, residue 29084. -/
theorem bounds_15_29084 : exactInterval 15 29084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29084 : oddCount 29084 15 = 10 ∧ acceleratedOrbit 15 29084 = 52420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29084) = 3 ^ 10 * m + 52420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29084.1, data_15_29084.2]

/-- Complete interval computation for depth 15, residue 29085. -/
theorem bounds_15_29085 : exactInterval 15 29085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29085 : oddCount 29085 15 = 10 ∧ acceleratedOrbit 15 29085 = 52420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29085) = 3 ^ 10 * m + 52420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29085.1, data_15_29085.2]

/-- Complete interval computation for depth 15, residue 29086. -/
theorem bounds_15_29086 : exactInterval 15 29086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29086 : oddCount 29086 15 = 10 ∧ acceleratedOrbit 15 29086 = 52420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29086) = 3 ^ 10 * m + 52420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29086.1, data_15_29086.2]

/-- Complete interval computation for depth 15, residue 29087. -/
theorem bounds_15_29087 : exactInterval 15 29087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29087 : oddCount 29087 15 = 10 ∧ acceleratedOrbit 15 29087 = 52418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29087) = 3 ^ 10 * m + 52418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29087.1, data_15_29087.2]

/-- Complete interval computation for depth 15, residue 29088. -/
theorem bounds_15_29088 : exactInterval 15 29088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29088 : oddCount 29088 15 = 2 ∧ acceleratedOrbit 15 29088 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29088) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29088.1, data_15_29088.2]

/-- Complete interval computation for depth 15, residue 29089. -/
theorem bounds_15_29089 : exactInterval 15 29089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29089 : oddCount 29089 15 = 10 ∧ acceleratedOrbit 15 29089 = 52427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29089) = 3 ^ 10 * m + 52427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29089.1, data_15_29089.2]

/-- Complete interval computation for depth 15, residue 29090. -/
theorem bounds_15_29090 : exactInterval 15 29090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29090 : oddCount 29090 15 = 8 ∧ acceleratedOrbit 15 29090 = 5827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29090) = 3 ^ 8 * m + 5827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29090.1, data_15_29090.2]

/-- Complete interval computation for depth 15, residue 29091. -/
theorem bounds_15_29091 : exactInterval 15 29091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29091 : oddCount 29091 15 = 8 ∧ acceleratedOrbit 15 29091 = 5827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29091) = 3 ^ 8 * m + 5827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29091.1, data_15_29091.2]

/-- Complete interval computation for depth 15, residue 29092. -/
theorem bounds_15_29092 : exactInterval 15 29092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29092 : oddCount 29092 15 = 8 ∧ acceleratedOrbit 15 29092 = 5827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29092) = 3 ^ 8 * m + 5827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29092.1, data_15_29092.2]

/-- Complete interval computation for depth 15, residue 29093. -/
theorem bounds_15_29093 : exactInterval 15 29093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29093 : oddCount 29093 15 = 8 ∧ acceleratedOrbit 15 29093 = 5827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29093) = 3 ^ 8 * m + 5827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29093.1, data_15_29093.2]

/-- Complete interval computation for depth 15, residue 29094. -/
theorem bounds_15_29094 : exactInterval 15 29094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29094 : oddCount 29094 15 = 8 ∧ acceleratedOrbit 15 29094 = 5827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29094) = 3 ^ 8 * m + 5827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29094.1, data_15_29094.2]

/-- Complete interval computation for depth 15, residue 29095. -/
theorem bounds_15_29095 : exactInterval 15 29095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29095 : oddCount 29095 15 = 7 ∧ acceleratedOrbit 15 29095 = 1942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29095) = 3 ^ 7 * m + 1942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29095.1, data_15_29095.2]

/-- Complete interval computation for depth 15, residue 29096. -/
theorem bounds_15_29096 : exactInterval 15 29096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29096 : oddCount 29096 15 = 2 ∧ acceleratedOrbit 15 29096 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29096) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29096.1, data_15_29096.2]

end Collatz.Research.PassageAtlas.Batch0888
