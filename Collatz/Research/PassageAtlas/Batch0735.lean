import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0735

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24051. -/
theorem bounds_15_24051 : exactInterval 15 24051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24051 : oddCount 24051 15 = 7 ∧ acceleratedOrbit 15 24051 = 1606 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24051) = 3 ^ 7 * m + 1606 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24051.1, data_15_24051.2]

/-- Complete interval computation for depth 15, residue 24052. -/
theorem bounds_15_24052 : exactInterval 15 24052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24052 : oddCount 24052 15 = 8 ∧ acceleratedOrbit 15 24052 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24052) = 3 ^ 8 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24052.1, data_15_24052.2]

/-- Complete interval computation for depth 15, residue 24053. -/
theorem bounds_15_24053 : exactInterval 15 24053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24053 : oddCount 24053 15 = 8 ∧ acceleratedOrbit 15 24053 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24053) = 3 ^ 8 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24053.1, data_15_24053.2]

/-- Complete interval computation for depth 15, residue 24054. -/
theorem bounds_15_24054 : exactInterval 15 24054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24054 : oddCount 24054 15 = 8 ∧ acceleratedOrbit 15 24054 = 4817 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24054) = 3 ^ 8 * m + 4817 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24054.1, data_15_24054.2]

/-- Complete interval computation for depth 15, residue 24055. -/
theorem bounds_15_24055 : exactInterval 15 24055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24055 : oddCount 24055 15 = 8 ∧ acceleratedOrbit 15 24055 = 4817 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24055) = 3 ^ 8 * m + 4817 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24055.1, data_15_24055.2]

/-- Complete interval computation for depth 15, residue 24056. -/
theorem bounds_15_24056 : exactInterval 15 24056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24056 : oddCount 24056 15 = 9 ∧ acceleratedOrbit 15 24056 = 14455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24056) = 3 ^ 9 * m + 14455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24056.1, data_15_24056.2]

/-- Complete interval computation for depth 15, residue 24057. -/
theorem bounds_15_24057 : exactInterval 15 24057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24057 : oddCount 24057 15 = 7 ∧ acceleratedOrbit 15 24057 = 1606 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24057) = 3 ^ 7 * m + 1606 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24057.1, data_15_24057.2]

/-- Complete interval computation for depth 15, residue 24058. -/
theorem bounds_15_24058 : exactInterval 15 24058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24058 : oddCount 24058 15 = 9 ∧ acceleratedOrbit 15 24058 = 14455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24058) = 3 ^ 9 * m + 14455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24058.1, data_15_24058.2]

/-- Complete interval computation for depth 15, residue 24059. -/
theorem bounds_15_24059 : exactInterval 15 24059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24059 : oddCount 24059 15 = 10 ∧ acceleratedOrbit 15 24059 = 43361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24059) = 3 ^ 10 * m + 43361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24059.1, data_15_24059.2]

/-- Complete interval computation for depth 15, residue 24060. -/
theorem bounds_15_24060 : exactInterval 15 24060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24060 : oddCount 24060 15 = 9 ∧ acceleratedOrbit 15 24060 = 14455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24060) = 3 ^ 9 * m + 14455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24060.1, data_15_24060.2]

/-- Complete interval computation for depth 15, residue 24061. -/
theorem bounds_15_24061 : exactInterval 15 24061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24061 : oddCount 24061 15 = 9 ∧ acceleratedOrbit 15 24061 = 14455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24061) = 3 ^ 9 * m + 14455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24061.1, data_15_24061.2]

/-- Complete interval computation for depth 15, residue 24062. -/
theorem bounds_15_24062 : exactInterval 15 24062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24062 : oddCount 24062 15 = 12 ∧ acceleratedOrbit 15 24062 = 390278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24062) = 3 ^ 12 * m + 390278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24062.1, data_15_24062.2]

/-- Complete interval computation for depth 15, residue 24063. -/
theorem bounds_15_24063 : exactInterval 15 24063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24063 : oddCount 24063 15 = 12 ∧ acceleratedOrbit 15 24063 = 390278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24063) = 3 ^ 12 * m + 390278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24063.1, data_15_24063.2]

/-- Complete interval computation for depth 15, residue 24064. -/
theorem bounds_15_24064 : exactInterval 15 24064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24064 : oddCount 24064 15 = 5 ∧ acceleratedOrbit 15 24064 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24064) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24064.1, data_15_24064.2]

/-- Complete interval computation for depth 15, residue 24065. -/
theorem bounds_15_24065 : exactInterval 15 24065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24065 : oddCount 24065 15 = 10 ∧ acceleratedOrbit 15 24065 = 43375 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24065) = 3 ^ 10 * m + 43375 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24065.1, data_15_24065.2]

/-- Complete interval computation for depth 15, residue 24066. -/
theorem bounds_15_24066 : exactInterval 15 24066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24066 : oddCount 24066 15 = 5 ∧ acceleratedOrbit 15 24066 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24066) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24066.1, data_15_24066.2]

/-- Complete interval computation for depth 15, residue 24067. -/
theorem bounds_15_24067 : exactInterval 15 24067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24067 : oddCount 24067 15 = 5 ∧ acceleratedOrbit 15 24067 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24067) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24067.1, data_15_24067.2]

/-- Complete interval computation for depth 15, residue 24068. -/
theorem bounds_15_24068 : exactInterval 15 24068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24068 : oddCount 24068 15 = 8 ∧ acceleratedOrbit 15 24068 = 4823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24068) = 3 ^ 8 * m + 4823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24068.1, data_15_24068.2]

/-- Complete interval computation for depth 15, residue 24069. -/
theorem bounds_15_24069 : exactInterval 15 24069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24069 : oddCount 24069 15 = 8 ∧ acceleratedOrbit 15 24069 = 4823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24069) = 3 ^ 8 * m + 4823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24069.1, data_15_24069.2]

/-- Complete interval computation for depth 15, residue 24070. -/
theorem bounds_15_24070 : exactInterval 15 24070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24070 : oddCount 24070 15 = 8 ∧ acceleratedOrbit 15 24070 = 4823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24070) = 3 ^ 8 * m + 4823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24070.1, data_15_24070.2]

/-- Complete interval computation for depth 15, residue 24071. -/
theorem bounds_15_24071 : exactInterval 15 24071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24071 : oddCount 24071 15 = 9 ∧ acceleratedOrbit 15 24071 = 14462 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24071) = 3 ^ 9 * m + 14462 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24071.1, data_15_24071.2]

/-- Complete interval computation for depth 15, residue 24072. -/
theorem bounds_15_24072 : exactInterval 15 24072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24072 : oddCount 24072 15 = 7 ∧ acceleratedOrbit 15 24072 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24072) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24072.1, data_15_24072.2]

/-- Complete interval computation for depth 15, residue 24073. -/
theorem bounds_15_24073 : exactInterval 15 24073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24073 : oddCount 24073 15 = 7 ∧ acceleratedOrbit 15 24073 = 1607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24073) = 3 ^ 7 * m + 1607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24073.1, data_15_24073.2]

/-- Complete interval computation for depth 15, residue 24074. -/
theorem bounds_15_24074 : exactInterval 15 24074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24074 : oddCount 24074 15 = 7 ∧ acceleratedOrbit 15 24074 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24074) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24074.1, data_15_24074.2]

/-- Complete interval computation for depth 15, residue 24075. -/
theorem bounds_15_24075 : exactInterval 15 24075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24075 : oddCount 24075 15 = 8 ∧ acceleratedOrbit 15 24075 = 4823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24075) = 3 ^ 8 * m + 4823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24075.1, data_15_24075.2]

/-- Complete interval computation for depth 15, residue 24076. -/
theorem bounds_15_24076 : exactInterval 15 24076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24076 : oddCount 24076 15 = 7 ∧ acceleratedOrbit 15 24076 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24076) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24076.1, data_15_24076.2]

/-- Complete interval computation for depth 15, residue 24077. -/
theorem bounds_15_24077 : exactInterval 15 24077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24077 : oddCount 24077 15 = 7 ∧ acceleratedOrbit 15 24077 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24077) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24077.1, data_15_24077.2]

/-- Complete interval computation for depth 15, residue 24078. -/
theorem bounds_15_24078 : exactInterval 15 24078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24078 : oddCount 24078 15 = 8 ∧ acceleratedOrbit 15 24078 = 4823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24078) = 3 ^ 8 * m + 4823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24078.1, data_15_24078.2]

/-- Complete interval computation for depth 15, residue 24079. -/
theorem bounds_15_24079 : exactInterval 15 24079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24079 : oddCount 24079 15 = 8 ∧ acceleratedOrbit 15 24079 = 4823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24079) = 3 ^ 8 * m + 4823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24079.1, data_15_24079.2]

/-- Complete interval computation for depth 15, residue 24080. -/
theorem bounds_15_24080 : exactInterval 15 24080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24080 : oddCount 24080 15 = 7 ∧ acceleratedOrbit 15 24080 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24080) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24080.1, data_15_24080.2]

/-- Complete interval computation for depth 15, residue 24081. -/
theorem bounds_15_24081 : exactInterval 15 24081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24081 : oddCount 24081 15 = 7 ∧ acceleratedOrbit 15 24081 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24081) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24081.1, data_15_24081.2]

/-- Complete interval computation for depth 15, residue 24082. -/
theorem bounds_15_24082 : exactInterval 15 24082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24082 : oddCount 24082 15 = 10 ∧ acceleratedOrbit 15 24082 = 43406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24082) = 3 ^ 10 * m + 43406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24082.1, data_15_24082.2]

/-- Complete interval computation for depth 15, residue 24083. -/
theorem bounds_15_24083 : exactInterval 15 24083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24083 : oddCount 24083 15 = 10 ∧ acceleratedOrbit 15 24083 = 43406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24083) = 3 ^ 10 * m + 43406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24083.1, data_15_24083.2]

end Collatz.Research.PassageAtlas.Batch0735
