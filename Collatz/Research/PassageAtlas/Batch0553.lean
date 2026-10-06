import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0553

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18087. -/
theorem bounds_15_18087 : exactInterval 15 18087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18087 : oddCount 18087 15 = 8 ∧ acceleratedOrbit 15 18087 = 3622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18087) = 3 ^ 8 * m + 3622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18087.1, data_15_18087.2]

/-- Complete interval computation for depth 15, residue 18088. -/
theorem bounds_15_18088 : exactInterval 15 18088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18088 : oddCount 18088 15 = 2 ∧ acceleratedOrbit 15 18088 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18088) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18088.1, data_15_18088.2]

/-- Complete interval computation for depth 15, residue 18089. -/
theorem bounds_15_18089 : exactInterval 15 18089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18089 : oddCount 18089 15 = 10 ∧ acceleratedOrbit 15 18089 = 32600 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18089) = 3 ^ 10 * m + 32600 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18089.1, data_15_18089.2]

/-- Complete interval computation for depth 15, residue 18090. -/
theorem bounds_15_18090 : exactInterval 15 18090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18090 : oddCount 18090 15 = 2 ∧ acceleratedOrbit 15 18090 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18090) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18090.1, data_15_18090.2]

/-- Complete interval computation for depth 15, residue 18091. -/
theorem bounds_15_18091 : exactInterval 15 18091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18091 : oddCount 18091 15 = 8 ∧ acceleratedOrbit 15 18091 = 3623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18091) = 3 ^ 8 * m + 3623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18091.1, data_15_18091.2]

/-- Complete interval computation for depth 15, residue 18092. -/
theorem bounds_15_18092 : exactInterval 15 18092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18092 : oddCount 18092 15 = 9 ∧ acceleratedOrbit 15 18092 = 10874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18092) = 3 ^ 9 * m + 10874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18092.1, data_15_18092.2]

/-- Complete interval computation for depth 15, residue 18093. -/
theorem bounds_15_18093 : exactInterval 15 18093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18093 : oddCount 18093 15 = 9 ∧ acceleratedOrbit 15 18093 = 10874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18093) = 3 ^ 9 * m + 10874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18093.1, data_15_18093.2]

/-- Complete interval computation for depth 15, residue 18094. -/
theorem bounds_15_18094 : exactInterval 15 18094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18094 : oddCount 18094 15 = 9 ∧ acceleratedOrbit 15 18094 = 10874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18094) = 3 ^ 9 * m + 10874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18094.1, data_15_18094.2]

/-- Complete interval computation for depth 15, residue 18095. -/
theorem bounds_15_18095 : exactInterval 15 18095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18095 : oddCount 18095 15 = 9 ∧ acceleratedOrbit 15 18095 = 10871 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18095) = 3 ^ 9 * m + 10871 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18095.1, data_15_18095.2]

/-- Complete interval computation for depth 15, residue 18096. -/
theorem bounds_15_18096 : exactInterval 15 18096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18096 : oddCount 18096 15 = 7 ∧ acceleratedOrbit 15 18096 = 1210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18096) = 3 ^ 7 * m + 1210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18096.1, data_15_18096.2]

/-- Complete interval computation for depth 15, residue 18097. -/
theorem bounds_15_18097 : exactInterval 15 18097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18097 : oddCount 18097 15 = 6 ∧ acceleratedOrbit 15 18097 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18097) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18097.1, data_15_18097.2]

/-- Complete interval computation for depth 15, residue 18098. -/
theorem bounds_15_18098 : exactInterval 15 18098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18098 : oddCount 18098 15 = 6 ∧ acceleratedOrbit 15 18098 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18098) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18098.1, data_15_18098.2]

/-- Complete interval computation for depth 15, residue 18099. -/
theorem bounds_15_18099 : exactInterval 15 18099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18099 : oddCount 18099 15 = 6 ∧ acceleratedOrbit 15 18099 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18099) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18099.1, data_15_18099.2]

/-- Complete interval computation for depth 15, residue 18100. -/
theorem bounds_15_18100 : exactInterval 15 18100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18100 : oddCount 18100 15 = 7 ∧ acceleratedOrbit 15 18100 = 1210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18100) = 3 ^ 7 * m + 1210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18100.1, data_15_18100.2]

/-- Complete interval computation for depth 15, residue 18101. -/
theorem bounds_15_18101 : exactInterval 15 18101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18101 : oddCount 18101 15 = 7 ∧ acceleratedOrbit 15 18101 = 1210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18101) = 3 ^ 7 * m + 1210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18101.1, data_15_18101.2]

/-- Complete interval computation for depth 15, residue 18102. -/
theorem bounds_15_18102 : exactInterval 15 18102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18102 : oddCount 18102 15 = 9 ∧ acceleratedOrbit 15 18102 = 10876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18102) = 3 ^ 9 * m + 10876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18102.1, data_15_18102.2]

/-- Complete interval computation for depth 15, residue 18103. -/
theorem bounds_15_18103 : exactInterval 15 18103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18103 : oddCount 18103 15 = 9 ∧ acceleratedOrbit 15 18103 = 10876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18103) = 3 ^ 9 * m + 10876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18103.1, data_15_18103.2]

/-- Complete interval computation for depth 15, residue 18104. -/
theorem bounds_15_18104 : exactInterval 15 18104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18104 : oddCount 18104 15 = 7 ∧ acceleratedOrbit 15 18104 = 1210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18104) = 3 ^ 7 * m + 1210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18104.1, data_15_18104.2]

/-- Complete interval computation for depth 15, residue 18105. -/
theorem bounds_15_18105 : exactInterval 15 18105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18105 : oddCount 18105 15 = 9 ∧ acceleratedOrbit 15 18105 = 10880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18105) = 3 ^ 9 * m + 10880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18105.1, data_15_18105.2]

/-- Complete interval computation for depth 15, residue 18106. -/
theorem bounds_15_18106 : exactInterval 15 18106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18106 : oddCount 18106 15 = 7 ∧ acceleratedOrbit 15 18106 = 1210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18106) = 3 ^ 7 * m + 1210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18106.1, data_15_18106.2]

/-- Complete interval computation for depth 15, residue 18107. -/
theorem bounds_15_18107 : exactInterval 15 18107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18107 : oddCount 18107 15 = 9 ∧ acceleratedOrbit 15 18107 = 10880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18107) = 3 ^ 9 * m + 10880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18107.1, data_15_18107.2]

/-- Complete interval computation for depth 15, residue 18108. -/
theorem bounds_15_18108 : exactInterval 15 18108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18108 : oddCount 18108 15 = 6 ∧ acceleratedOrbit 15 18108 = 403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18108) = 3 ^ 6 * m + 403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18108.1, data_15_18108.2]

/-- Complete interval computation for depth 15, residue 18109. -/
theorem bounds_15_18109 : exactInterval 15 18109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18109 : oddCount 18109 15 = 6 ∧ acceleratedOrbit 15 18109 = 403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18109) = 3 ^ 6 * m + 403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18109.1, data_15_18109.2]

/-- Complete interval computation for depth 15, residue 18110. -/
theorem bounds_15_18110 : exactInterval 15 18110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18110 : oddCount 18110 15 = 6 ∧ acceleratedOrbit 15 18110 = 403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18110) = 3 ^ 6 * m + 403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18110.1, data_15_18110.2]

/-- Complete interval computation for depth 15, residue 18111. -/
theorem bounds_15_18111 : exactInterval 15 18111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18111 : oddCount 18111 15 = 9 ∧ acceleratedOrbit 15 18111 = 10880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18111) = 3 ^ 9 * m + 10880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18111.1, data_15_18111.2]

/-- Complete interval computation for depth 15, residue 18112. -/
theorem bounds_15_18112 : exactInterval 15 18112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18112 : oddCount 18112 15 = 8 ∧ acceleratedOrbit 15 18112 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18112) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18112.1, data_15_18112.2]

/-- Complete interval computation for depth 15, residue 18113. -/
theorem bounds_15_18113 : exactInterval 15 18113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18113 : oddCount 18113 15 = 7 ∧ acceleratedOrbit 15 18113 = 1210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18113) = 3 ^ 7 * m + 1210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18113.1, data_15_18113.2]

/-- Complete interval computation for depth 15, residue 18114. -/
theorem bounds_15_18114 : exactInterval 15 18114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18114 : oddCount 18114 15 = 8 ∧ acceleratedOrbit 15 18114 = 3628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18114) = 3 ^ 8 * m + 3628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18114.1, data_15_18114.2]

/-- Complete interval computation for depth 15, residue 18115. -/
theorem bounds_15_18115 : exactInterval 15 18115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18115 : oddCount 18115 15 = 8 ∧ acceleratedOrbit 15 18115 = 3628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18115) = 3 ^ 8 * m + 3628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18115.1, data_15_18115.2]

/-- Complete interval computation for depth 15, residue 18116. -/
theorem bounds_15_18116 : exactInterval 15 18116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18116 : oddCount 18116 15 = 7 ∧ acceleratedOrbit 15 18116 = 1214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18116) = 3 ^ 7 * m + 1214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18116.1, data_15_18116.2]

/-- Complete interval computation for depth 15, residue 18117. -/
theorem bounds_15_18117 : exactInterval 15 18117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18117 : oddCount 18117 15 = 7 ∧ acceleratedOrbit 15 18117 = 1214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18117) = 3 ^ 7 * m + 1214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18117.1, data_15_18117.2]

/-- Complete interval computation for depth 15, residue 18118. -/
theorem bounds_15_18118 : exactInterval 15 18118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18118 : oddCount 18118 15 = 7 ∧ acceleratedOrbit 15 18118 = 1214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18118) = 3 ^ 7 * m + 1214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18118.1, data_15_18118.2]

/-- Complete interval computation for depth 15, residue 18119. -/
theorem bounds_15_18119 : exactInterval 15 18119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18119 : oddCount 18119 15 = 7 ∧ acceleratedOrbit 15 18119 = 1210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18119) = 3 ^ 7 * m + 1210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18119.1, data_15_18119.2]

end Collatz.Research.PassageAtlas.Batch0553
