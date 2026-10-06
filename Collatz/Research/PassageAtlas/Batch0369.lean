import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0369

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12058. -/
theorem bounds_15_12058 : exactInterval 15 12058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12058 : oddCount 12058 15 = 3 ∧ acceleratedOrbit 15 12058 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12058) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12058.1, data_15_12058.2]

/-- Complete interval computation for depth 15, residue 12059. -/
theorem bounds_15_12059 : exactInterval 15 12059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12059 : oddCount 12059 15 = 11 ∧ acceleratedOrbit 15 12059 = 65200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12059) = 3 ^ 11 * m + 65200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12059.1, data_15_12059.2]

/-- Complete interval computation for depth 15, residue 12060. -/
theorem bounds_15_12060 : exactInterval 15 12060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12060 : oddCount 12060 15 = 9 ∧ acceleratedOrbit 15 12060 = 7249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12060) = 3 ^ 9 * m + 7249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12060.1, data_15_12060.2]

/-- Complete interval computation for depth 15, residue 12061. -/
theorem bounds_15_12061 : exactInterval 15 12061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12061 : oddCount 12061 15 = 9 ∧ acceleratedOrbit 15 12061 = 7249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12061) = 3 ^ 9 * m + 7249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12061.1, data_15_12061.2]

/-- Complete interval computation for depth 15, residue 12062. -/
theorem bounds_15_12062 : exactInterval 15 12062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12062 : oddCount 12062 15 = 9 ∧ acceleratedOrbit 15 12062 = 7249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12062) = 3 ^ 9 * m + 7249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12062.1, data_15_12062.2]

/-- Complete interval computation for depth 15, residue 12063. -/
theorem bounds_15_12063 : exactInterval 15 12063 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12063) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12063 : oddCount 12063 15 = 9 ∧ acceleratedOrbit 15 12063 = 7247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12063) = 3 ^ 9 * m + 7247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12063.1, data_15_12063.2]

/-- Complete interval computation for depth 15, residue 12064. -/
theorem bounds_15_12064 : exactInterval 15 12064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12064 : oddCount 12064 15 = 8 ∧ acceleratedOrbit 15 12064 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12064) = 3 ^ 8 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12064.1, data_15_12064.2]

/-- Complete interval computation for depth 15, residue 12065. -/
theorem bounds_15_12065 : exactInterval 15 12065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12065 : oddCount 12065 15 = 6 ∧ acceleratedOrbit 15 12065 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12065) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12065.1, data_15_12065.2]

/-- Complete interval computation for depth 15, residue 12066. -/
theorem bounds_15_12066 : exactInterval 15 12066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12066 : oddCount 12066 15 = 8 ∧ acceleratedOrbit 15 12066 = 2420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12066) = 3 ^ 8 * m + 2420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12066.1, data_15_12066.2]

/-- Complete interval computation for depth 15, residue 12067. -/
theorem bounds_15_12067 : exactInterval 15 12067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12067 : oddCount 12067 15 = 8 ∧ acceleratedOrbit 15 12067 = 2420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12067) = 3 ^ 8 * m + 2420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12067.1, data_15_12067.2]

/-- Complete interval computation for depth 15, residue 12068. -/
theorem bounds_15_12068 : exactInterval 15 12068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12068 : oddCount 12068 15 = 8 ∧ acceleratedOrbit 15 12068 = 2420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12068) = 3 ^ 8 * m + 2420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12068.1, data_15_12068.2]

/-- Complete interval computation for depth 15, residue 12069. -/
theorem bounds_15_12069 : exactInterval 15 12069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12069 : oddCount 12069 15 = 8 ∧ acceleratedOrbit 15 12069 = 2420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12069) = 3 ^ 8 * m + 2420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12069.1, data_15_12069.2]

/-- Complete interval computation for depth 15, residue 12070. -/
theorem bounds_15_12070 : exactInterval 15 12070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12070 : oddCount 12070 15 = 8 ∧ acceleratedOrbit 15 12070 = 2420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12070) = 3 ^ 8 * m + 2420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12070.1, data_15_12070.2]

/-- Complete interval computation for depth 15, residue 12071. -/
theorem bounds_15_12071 : exactInterval 15 12071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12071 : oddCount 12071 15 = 9 ∧ acceleratedOrbit 15 12071 = 7253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12071) = 3 ^ 9 * m + 7253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12071.1, data_15_12071.2]

/-- Complete interval computation for depth 15, residue 12072. -/
theorem bounds_15_12072 : exactInterval 15 12072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12072 : oddCount 12072 15 = 8 ∧ acceleratedOrbit 15 12072 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12072) = 3 ^ 8 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12072.1, data_15_12072.2]

/-- Complete interval computation for depth 15, residue 12073. -/
theorem bounds_15_12073 : exactInterval 15 12073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12073 : oddCount 12073 15 = 7 ∧ acceleratedOrbit 15 12073 = 806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12073) = 3 ^ 7 * m + 806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12073.1, data_15_12073.2]

/-- Complete interval computation for depth 15, residue 12074. -/
theorem bounds_15_12074 : exactInterval 15 12074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12074 : oddCount 12074 15 = 8 ∧ acceleratedOrbit 15 12074 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12074) = 3 ^ 8 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12074.1, data_15_12074.2]

/-- Complete interval computation for depth 15, residue 12075. -/
theorem bounds_15_12075 : exactInterval 15 12075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12075 : oddCount 12075 15 = 8 ∧ acceleratedOrbit 15 12075 = 2420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12075) = 3 ^ 8 * m + 2420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12075.1, data_15_12075.2]

/-- Complete interval computation for depth 15, residue 12076. -/
theorem bounds_15_12076 : exactInterval 15 12076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12076 : oddCount 12076 15 = 7 ∧ acceleratedOrbit 15 12076 = 809 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12076) = 3 ^ 7 * m + 809 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12076.1, data_15_12076.2]

/-- Complete interval computation for depth 15, residue 12077. -/
theorem bounds_15_12077 : exactInterval 15 12077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12077 : oddCount 12077 15 = 7 ∧ acceleratedOrbit 15 12077 = 809 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12077) = 3 ^ 7 * m + 809 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12077.1, data_15_12077.2]

/-- Complete interval computation for depth 15, residue 12078. -/
theorem bounds_15_12078 : exactInterval 15 12078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12078 : oddCount 12078 15 = 7 ∧ acceleratedOrbit 15 12078 = 809 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12078) = 3 ^ 7 * m + 809 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12078.1, data_15_12078.2]

/-- Complete interval computation for depth 15, residue 12079. -/
theorem bounds_15_12079 : exactInterval 15 12079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12079 : oddCount 12079 15 = 8 ∧ acceleratedOrbit 15 12079 = 2420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12079) = 3 ^ 8 * m + 2420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12079.1, data_15_12079.2]

/-- Complete interval computation for depth 15, residue 12080. -/
theorem bounds_15_12080 : exactInterval 15 12080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12080 : oddCount 12080 15 = 8 ∧ acceleratedOrbit 15 12080 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12080) = 3 ^ 8 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12080.1, data_15_12080.2]

/-- Complete interval computation for depth 15, residue 12081. -/
theorem bounds_15_12081 : exactInterval 15 12081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12081 : oddCount 12081 15 = 7 ∧ acceleratedOrbit 15 12081 = 809 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12081) = 3 ^ 7 * m + 809 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12081.1, data_15_12081.2]

/-- Complete interval computation for depth 15, residue 12082. -/
theorem bounds_15_12082 : exactInterval 15 12082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12082 : oddCount 12082 15 = 7 ∧ acceleratedOrbit 15 12082 = 809 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12082) = 3 ^ 7 * m + 809 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12082.1, data_15_12082.2]

/-- Complete interval computation for depth 15, residue 12083. -/
theorem bounds_15_12083 : exactInterval 15 12083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12083 : oddCount 12083 15 = 7 ∧ acceleratedOrbit 15 12083 = 809 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12083) = 3 ^ 7 * m + 809 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12083.1, data_15_12083.2]

/-- Complete interval computation for depth 15, residue 12084. -/
theorem bounds_15_12084 : exactInterval 15 12084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12084 : oddCount 12084 15 = 8 ∧ acceleratedOrbit 15 12084 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12084) = 3 ^ 8 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12084.1, data_15_12084.2]

/-- Complete interval computation for depth 15, residue 12085. -/
theorem bounds_15_12085 : exactInterval 15 12085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12085 : oddCount 12085 15 = 8 ∧ acceleratedOrbit 15 12085 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12085) = 3 ^ 8 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12085.1, data_15_12085.2]

/-- Complete interval computation for depth 15, residue 12086. -/
theorem bounds_15_12086 : exactInterval 15 12086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12086 : oddCount 12086 15 = 10 ∧ acceleratedOrbit 15 12086 = 21788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12086) = 3 ^ 10 * m + 21788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12086.1, data_15_12086.2]

/-- Complete interval computation for depth 15, residue 12087. -/
theorem bounds_15_12087 : exactInterval 15 12087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12087 : oddCount 12087 15 = 10 ∧ acceleratedOrbit 15 12087 = 21788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12087) = 3 ^ 10 * m + 21788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12087.1, data_15_12087.2]

/-- Complete interval computation for depth 15, residue 12088. -/
theorem bounds_15_12088 : exactInterval 15 12088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12088 : oddCount 12088 15 = 8 ∧ acceleratedOrbit 15 12088 = 2423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12088) = 3 ^ 8 * m + 2423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12088.1, data_15_12088.2]

/-- Complete interval computation for depth 15, residue 12089. -/
theorem bounds_15_12089 : exactInterval 15 12089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12089 : oddCount 12089 15 = 6 ∧ acceleratedOrbit 15 12089 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12089) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12089.1, data_15_12089.2]

/-- Complete interval computation for depth 15, residue 12090. -/
theorem bounds_15_12090 : exactInterval 15 12090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12090 : oddCount 12090 15 = 8 ∧ acceleratedOrbit 15 12090 = 2423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12090) = 3 ^ 8 * m + 2423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12090.1, data_15_12090.2]

end Collatz.Research.PassageAtlas.Batch0369
