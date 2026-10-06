import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0339

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11075. -/
theorem bounds_15_11075 : exactInterval 15 11075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11075 : oddCount 11075 15 = 7 ∧ acceleratedOrbit 15 11075 = 740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11075) = 3 ^ 7 * m + 740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11075.1, data_15_11075.2]

/-- Complete interval computation for depth 15, residue 11076. -/
theorem bounds_15_11076 : exactInterval 15 11076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11076 : oddCount 11076 15 = 6 ∧ acceleratedOrbit 15 11076 = 247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11076) = 3 ^ 6 * m + 247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11076.1, data_15_11076.2]

/-- Complete interval computation for depth 15, residue 11077. -/
theorem bounds_15_11077 : exactInterval 15 11077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11077 : oddCount 11077 15 = 6 ∧ acceleratedOrbit 15 11077 = 247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11077) = 3 ^ 6 * m + 247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11077.1, data_15_11077.2]

/-- Complete interval computation for depth 15, residue 11078. -/
theorem bounds_15_11078 : exactInterval 15 11078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11078 : oddCount 11078 15 = 6 ∧ acceleratedOrbit 15 11078 = 247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11078) = 3 ^ 6 * m + 247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11078.1, data_15_11078.2]

/-- Complete interval computation for depth 15, residue 11079. -/
theorem bounds_15_11079 : exactInterval 15 11079 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11079) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11079 : oddCount 11079 15 = 9 ∧ acceleratedOrbit 15 11079 = 6656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11079) = 3 ^ 9 * m + 6656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11079.1, data_15_11079.2]

/-- Complete interval computation for depth 15, residue 11080. -/
theorem bounds_15_11080 : exactInterval 15 11080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11080 : oddCount 11080 15 = 6 ∧ acceleratedOrbit 15 11080 = 247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11080) = 3 ^ 6 * m + 247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11080.1, data_15_11080.2]

/-- Complete interval computation for depth 15, residue 11081. -/
theorem bounds_15_11081 : exactInterval 15 11081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11081 : oddCount 11081 15 = 7 ∧ acceleratedOrbit 15 11081 = 740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11081) = 3 ^ 7 * m + 740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11081.1, data_15_11081.2]

/-- Complete interval computation for depth 15, residue 11082. -/
theorem bounds_15_11082 : exactInterval 15 11082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11082 : oddCount 11082 15 = 6 ∧ acceleratedOrbit 15 11082 = 247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11082) = 3 ^ 6 * m + 247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11082.1, data_15_11082.2]

/-- Complete interval computation for depth 15, residue 11083. -/
theorem bounds_15_11083 : exactInterval 15 11083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11083 : oddCount 11083 15 = 6 ∧ acceleratedOrbit 15 11083 = 247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11083) = 3 ^ 6 * m + 247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11083.1, data_15_11083.2]

/-- Complete interval computation for depth 15, residue 11084. -/
theorem bounds_15_11084 : exactInterval 15 11084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11084 : oddCount 11084 15 = 6 ∧ acceleratedOrbit 15 11084 = 247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11084) = 3 ^ 6 * m + 247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11084.1, data_15_11084.2]

/-- Complete interval computation for depth 15, residue 11085. -/
theorem bounds_15_11085 : exactInterval 15 11085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11085 : oddCount 11085 15 = 6 ∧ acceleratedOrbit 15 11085 = 247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11085) = 3 ^ 6 * m + 247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11085.1, data_15_11085.2]

/-- Complete interval computation for depth 15, residue 11086. -/
theorem bounds_15_11086 : exactInterval 15 11086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11086 : oddCount 11086 15 = 9 ∧ acceleratedOrbit 15 11086 = 6662 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11086) = 3 ^ 9 * m + 6662 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11086.1, data_15_11086.2]

/-- Complete interval computation for depth 15, residue 11087. -/
theorem bounds_15_11087 : exactInterval 15 11087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11087 : oddCount 11087 15 = 9 ∧ acceleratedOrbit 15 11087 = 6662 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11087) = 3 ^ 9 * m + 6662 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11087.1, data_15_11087.2]

/-- Complete interval computation for depth 15, residue 11088. -/
theorem bounds_15_11088 : exactInterval 15 11088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11088 : oddCount 11088 15 = 4 ∧ acceleratedOrbit 15 11088 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11088) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11088.1, data_15_11088.2]

/-- Complete interval computation for depth 15, residue 11089. -/
theorem bounds_15_11089 : exactInterval 15 11089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11089 : oddCount 11089 15 = 9 ∧ acceleratedOrbit 15 11089 = 6664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11089) = 3 ^ 9 * m + 6664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11089.1, data_15_11089.2]

/-- Complete interval computation for depth 15, residue 11090. -/
theorem bounds_15_11090 : exactInterval 15 11090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11090 : oddCount 11090 15 = 9 ∧ acceleratedOrbit 15 11090 = 6664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11090) = 3 ^ 9 * m + 6664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11090.1, data_15_11090.2]

/-- Complete interval computation for depth 15, residue 11091. -/
theorem bounds_15_11091 : exactInterval 15 11091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11091 : oddCount 11091 15 = 9 ∧ acceleratedOrbit 15 11091 = 6664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11091) = 3 ^ 9 * m + 6664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11091.1, data_15_11091.2]

/-- Complete interval computation for depth 15, residue 11092. -/
theorem bounds_15_11092 : exactInterval 15 11092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11092 : oddCount 11092 15 = 4 ∧ acceleratedOrbit 15 11092 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11092) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11092.1, data_15_11092.2]

/-- Complete interval computation for depth 15, residue 11093. -/
theorem bounds_15_11093 : exactInterval 15 11093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11093 : oddCount 11093 15 = 4 ∧ acceleratedOrbit 15 11093 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11093) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11093.1, data_15_11093.2]

/-- Complete interval computation for depth 15, residue 11094. -/
theorem bounds_15_11094 : exactInterval 15 11094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11094 : oddCount 11094 15 = 9 ∧ acceleratedOrbit 15 11094 = 6668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11094) = 3 ^ 9 * m + 6668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11094.1, data_15_11094.2]

/-- Complete interval computation for depth 15, residue 11095. -/
theorem bounds_15_11095 : exactInterval 15 11095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11095 : oddCount 11095 15 = 9 ∧ acceleratedOrbit 15 11095 = 6668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11095) = 3 ^ 9 * m + 6668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11095.1, data_15_11095.2]

/-- Complete interval computation for depth 15, residue 11096. -/
theorem bounds_15_11096 : exactInterval 15 11096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11096 : oddCount 11096 15 = 7 ∧ acceleratedOrbit 15 11096 = 742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11096) = 3 ^ 7 * m + 742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11096.1, data_15_11096.2]

/-- Complete interval computation for depth 15, residue 11097. -/
theorem bounds_15_11097 : exactInterval 15 11097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11097 : oddCount 11097 15 = 7 ∧ acceleratedOrbit 15 11097 = 742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11097) = 3 ^ 7 * m + 742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11097.1, data_15_11097.2]

/-- Complete interval computation for depth 15, residue 11098. -/
theorem bounds_15_11098 : exactInterval 15 11098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11098 : oddCount 11098 15 = 7 ∧ acceleratedOrbit 15 11098 = 742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11098) = 3 ^ 7 * m + 742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11098.1, data_15_11098.2]

/-- Complete interval computation for depth 15, residue 11099. -/
theorem bounds_15_11099 : exactInterval 15 11099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11099 : oddCount 11099 15 = 10 ∧ acceleratedOrbit 15 11099 = 20006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11099) = 3 ^ 10 * m + 20006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11099.1, data_15_11099.2]

/-- Complete interval computation for depth 15, residue 11100. -/
theorem bounds_15_11100 : exactInterval 15 11100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11100 : oddCount 11100 15 = 7 ∧ acceleratedOrbit 15 11100 = 742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11100) = 3 ^ 7 * m + 742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11100.1, data_15_11100.2]

/-- Complete interval computation for depth 15, residue 11101. -/
theorem bounds_15_11101 : exactInterval 15 11101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11101 : oddCount 11101 15 = 7 ∧ acceleratedOrbit 15 11101 = 742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11101) = 3 ^ 7 * m + 742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11101.1, data_15_11101.2]

/-- Complete interval computation for depth 15, residue 11102. -/
theorem bounds_15_11102 : exactInterval 15 11102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11102 : oddCount 11102 15 = 8 ∧ acceleratedOrbit 15 11102 = 2224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11102) = 3 ^ 8 * m + 2224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11102.1, data_15_11102.2]

/-- Complete interval computation for depth 15, residue 11103. -/
theorem bounds_15_11103 : exactInterval 15 11103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11103 : oddCount 11103 15 = 8 ∧ acceleratedOrbit 15 11103 = 2224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11103) = 3 ^ 8 * m + 2224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11103.1, data_15_11103.2]

/-- Complete interval computation for depth 15, residue 11104. -/
theorem bounds_15_11104 : exactInterval 15 11104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11104 : oddCount 11104 15 = 6 ∧ acceleratedOrbit 15 11104 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11104) = 3 ^ 6 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11104.1, data_15_11104.2]

/-- Complete interval computation for depth 15, residue 11105. -/
theorem bounds_15_11105 : exactInterval 15 11105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11105 : oddCount 11105 15 = 10 ∧ acceleratedOrbit 15 11105 = 20017 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11105) = 3 ^ 10 * m + 20017 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11105.1, data_15_11105.2]

/-- Complete interval computation for depth 15, residue 11106. -/
theorem bounds_15_11106 : exactInterval 15 11106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11106 : oddCount 11106 15 = 5 ∧ acceleratedOrbit 15 11106 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11106) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11106.1, data_15_11106.2]

/-- Complete interval computation for depth 15, residue 11107. -/
theorem bounds_15_11107 : exactInterval 15 11107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11107 : oddCount 11107 15 = 5 ∧ acceleratedOrbit 15 11107 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11107) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11107.1, data_15_11107.2]

end Collatz.Research.PassageAtlas.Batch0339
