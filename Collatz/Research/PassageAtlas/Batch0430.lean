import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0430

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14057. -/
theorem bounds_15_14057 : exactInterval 15 14057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14057 : oddCount 14057 15 = 8 ∧ acceleratedOrbit 15 14057 = 2815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14057) = 3 ^ 8 * m + 2815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14057.1, data_15_14057.2]

/-- Complete interval computation for depth 15, residue 14058. -/
theorem bounds_15_14058 : exactInterval 15 14058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14058 : oddCount 14058 15 = 6 ∧ acceleratedOrbit 15 14058 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14058) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14058.1, data_15_14058.2]

/-- Complete interval computation for depth 15, residue 14059. -/
theorem bounds_15_14059 : exactInterval 15 14059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14059 : oddCount 14059 15 = 8 ∧ acceleratedOrbit 15 14059 = 2816 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14059) = 3 ^ 8 * m + 2816 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14059.1, data_15_14059.2]

/-- Complete interval computation for depth 15, residue 14060. -/
theorem bounds_15_14060 : exactInterval 15 14060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14060 : oddCount 14060 15 = 6 ∧ acceleratedOrbit 15 14060 = 313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14060) = 3 ^ 6 * m + 313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14060.1, data_15_14060.2]

/-- Complete interval computation for depth 15, residue 14061. -/
theorem bounds_15_14061 : exactInterval 15 14061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14061 : oddCount 14061 15 = 6 ∧ acceleratedOrbit 15 14061 = 313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14061) = 3 ^ 6 * m + 313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14061.1, data_15_14061.2]

/-- Complete interval computation for depth 15, residue 14062. -/
theorem bounds_15_14062 : exactInterval 15 14062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14062 : oddCount 14062 15 = 6 ∧ acceleratedOrbit 15 14062 = 313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14062) = 3 ^ 6 * m + 313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14062.1, data_15_14062.2]

/-- Complete interval computation for depth 15, residue 14063. -/
theorem bounds_15_14063 : exactInterval 15 14063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14063 : oddCount 14063 15 = 8 ∧ acceleratedOrbit 15 14063 = 2816 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14063) = 3 ^ 8 * m + 2816 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14063.1, data_15_14063.2]

/-- Complete interval computation for depth 15, residue 14064. -/
theorem bounds_15_14064 : exactInterval 15 14064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14064 : oddCount 14064 15 = 7 ∧ acceleratedOrbit 15 14064 = 940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14064) = 3 ^ 7 * m + 940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14064.1, data_15_14064.2]

/-- Complete interval computation for depth 15, residue 14065. -/
theorem bounds_15_14065 : exactInterval 15 14065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14065 : oddCount 14065 15 = 6 ∧ acceleratedOrbit 15 14065 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14065) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14065.1, data_15_14065.2]

/-- Complete interval computation for depth 15, residue 14066. -/
theorem bounds_15_14066 : exactInterval 15 14066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14066 : oddCount 14066 15 = 9 ∧ acceleratedOrbit 15 14066 = 8452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14066) = 3 ^ 9 * m + 8452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14066.1, data_15_14066.2]

/-- Complete interval computation for depth 15, residue 14067. -/
theorem bounds_15_14067 : exactInterval 15 14067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14067 : oddCount 14067 15 = 9 ∧ acceleratedOrbit 15 14067 = 8452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14067) = 3 ^ 9 * m + 8452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14067.1, data_15_14067.2]

/-- Complete interval computation for depth 15, residue 14068. -/
theorem bounds_15_14068 : exactInterval 15 14068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14068 : oddCount 14068 15 = 7 ∧ acceleratedOrbit 15 14068 = 940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14068) = 3 ^ 7 * m + 940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14068.1, data_15_14068.2]

/-- Complete interval computation for depth 15, residue 14069. -/
theorem bounds_15_14069 : exactInterval 15 14069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14069 : oddCount 14069 15 = 7 ∧ acceleratedOrbit 15 14069 = 940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14069) = 3 ^ 7 * m + 940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14069.1, data_15_14069.2]

/-- Complete interval computation for depth 15, residue 14070. -/
theorem bounds_15_14070 : exactInterval 15 14070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14070 : oddCount 14070 15 = 8 ∧ acceleratedOrbit 15 14070 = 2818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14070) = 3 ^ 8 * m + 2818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14070.1, data_15_14070.2]

/-- Complete interval computation for depth 15, residue 14071. -/
theorem bounds_15_14071 : exactInterval 15 14071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14071 : oddCount 14071 15 = 8 ∧ acceleratedOrbit 15 14071 = 2818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14071) = 3 ^ 8 * m + 2818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14071.1, data_15_14071.2]

/-- Complete interval computation for depth 15, residue 14072. -/
theorem bounds_15_14072 : exactInterval 15 14072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14072 : oddCount 14072 15 = 7 ∧ acceleratedOrbit 15 14072 = 940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14072) = 3 ^ 7 * m + 940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14072.1, data_15_14072.2]

/-- Complete interval computation for depth 15, residue 14073. -/
theorem bounds_15_14073 : exactInterval 15 14073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14073 : oddCount 14073 15 = 7 ∧ acceleratedOrbit 15 14073 = 940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14073) = 3 ^ 7 * m + 940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14073.1, data_15_14073.2]

/-- Complete interval computation for depth 15, residue 14074. -/
theorem bounds_15_14074 : exactInterval 15 14074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14074 : oddCount 14074 15 = 7 ∧ acceleratedOrbit 15 14074 = 940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14074) = 3 ^ 7 * m + 940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14074.1, data_15_14074.2]

/-- Complete interval computation for depth 15, residue 14075. -/
theorem bounds_15_14075 : exactInterval 15 14075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14075 : oddCount 14075 15 = 8 ∧ acceleratedOrbit 15 14075 = 2819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14075) = 3 ^ 8 * m + 2819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14075.1, data_15_14075.2]

/-- Complete interval computation for depth 15, residue 14076. -/
theorem bounds_15_14076 : exactInterval 15 14076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14076 : oddCount 14076 15 = 10 ∧ acceleratedOrbit 15 14076 = 25373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14076) = 3 ^ 10 * m + 25373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14076.1, data_15_14076.2]

/-- Complete interval computation for depth 15, residue 14077. -/
theorem bounds_15_14077 : exactInterval 15 14077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14077 : oddCount 14077 15 = 10 ∧ acceleratedOrbit 15 14077 = 25373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14077) = 3 ^ 10 * m + 25373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14077.1, data_15_14077.2]

/-- Complete interval computation for depth 15, residue 14078. -/
theorem bounds_15_14078 : exactInterval 15 14078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14078 : oddCount 14078 15 = 10 ∧ acceleratedOrbit 15 14078 = 25373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14078) = 3 ^ 10 * m + 25373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14078.1, data_15_14078.2]

/-- Complete interval computation for depth 15, residue 14079. -/
theorem bounds_15_14079 : exactInterval 15 14079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14079 : oddCount 14079 15 = 11 ∧ acceleratedOrbit 15 14079 = 76118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14079) = 3 ^ 11 * m + 76118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14079.1, data_15_14079.2]

/-- Complete interval computation for depth 15, residue 14080. -/
theorem bounds_15_14080 : exactInterval 15 14080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14080 : oddCount 14080 15 = 5 ∧ acceleratedOrbit 15 14080 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14080) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14080.1, data_15_14080.2]

/-- Complete interval computation for depth 15, residue 14081. -/
theorem bounds_15_14081 : exactInterval 15 14081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14081 : oddCount 14081 15 = 6 ∧ acceleratedOrbit 15 14081 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14081) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14081.1, data_15_14081.2]

/-- Complete interval computation for depth 15, residue 14082. -/
theorem bounds_15_14082 : exactInterval 15 14082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14082 : oddCount 14082 15 = 9 ∧ acceleratedOrbit 15 14082 = 8464 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14082) = 3 ^ 9 * m + 8464 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14082.1, data_15_14082.2]

/-- Complete interval computation for depth 15, residue 14083. -/
theorem bounds_15_14083 : exactInterval 15 14083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14083 : oddCount 14083 15 = 9 ∧ acceleratedOrbit 15 14083 = 8464 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14083) = 3 ^ 9 * m + 8464 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14083.1, data_15_14083.2]

/-- Complete interval computation for depth 15, residue 14084. -/
theorem bounds_15_14084 : exactInterval 15 14084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14084 : oddCount 14084 15 = 8 ∧ acceleratedOrbit 15 14084 = 2825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14084) = 3 ^ 8 * m + 2825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14084.1, data_15_14084.2]

/-- Complete interval computation for depth 15, residue 14085. -/
theorem bounds_15_14085 : exactInterval 15 14085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14085 : oddCount 14085 15 = 8 ∧ acceleratedOrbit 15 14085 = 2825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14085) = 3 ^ 8 * m + 2825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14085.1, data_15_14085.2]

/-- Complete interval computation for depth 15, residue 14086. -/
theorem bounds_15_14086 : exactInterval 15 14086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14086 : oddCount 14086 15 = 8 ∧ acceleratedOrbit 15 14086 = 2825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14086) = 3 ^ 8 * m + 2825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14086.1, data_15_14086.2]

/-- Complete interval computation for depth 15, residue 14087. -/
theorem bounds_15_14087 : exactInterval 15 14087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14087 : oddCount 14087 15 = 9 ∧ acceleratedOrbit 15 14087 = 8464 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14087) = 3 ^ 9 * m + 8464 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14087.1, data_15_14087.2]

/-- Complete interval computation for depth 15, residue 14088. -/
theorem bounds_15_14088 : exactInterval 15 14088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14088 : oddCount 14088 15 = 8 ∧ acceleratedOrbit 15 14088 = 2825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14088) = 3 ^ 8 * m + 2825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14088.1, data_15_14088.2]

/-- Complete interval computation for depth 15, residue 14089. -/
theorem bounds_15_14089 : exactInterval 15 14089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14089 : oddCount 14089 15 = 11 ∧ acceleratedOrbit 15 14089 = 76180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14089) = 3 ^ 11 * m + 76180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14089.1, data_15_14089.2]

end Collatz.Research.PassageAtlas.Batch0430
