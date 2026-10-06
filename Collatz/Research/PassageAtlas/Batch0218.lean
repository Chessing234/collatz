import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0218

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7110. -/
theorem bounds_15_7110 : exactInterval 15 7110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7110 : oddCount 7110 15 = 6 ∧ acceleratedOrbit 15 7110 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7110) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7110.1, data_15_7110.2]

/-- Complete interval computation for depth 15, residue 7111. -/
theorem bounds_15_7111 : exactInterval 15 7111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7111 : oddCount 7111 15 = 10 ∧ acceleratedOrbit 15 7111 = 12818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7111) = 3 ^ 10 * m + 12818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7111.1, data_15_7111.2]

/-- Complete interval computation for depth 15, residue 7112. -/
theorem bounds_15_7112 : exactInterval 15 7112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7112 : oddCount 7112 15 = 9 ∧ acceleratedOrbit 15 7112 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7112) = 3 ^ 9 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7112.1, data_15_7112.2]

/-- Complete interval computation for depth 15, residue 7113. -/
theorem bounds_15_7113 : exactInterval 15 7113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7113 : oddCount 7113 15 = 7 ∧ acceleratedOrbit 15 7113 = 475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7113) = 3 ^ 7 * m + 475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7113.1, data_15_7113.2]

/-- Complete interval computation for depth 15, residue 7114. -/
theorem bounds_15_7114 : exactInterval 15 7114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7114 : oddCount 7114 15 = 9 ∧ acceleratedOrbit 15 7114 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7114) = 3 ^ 9 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7114.1, data_15_7114.2]

/-- Complete interval computation for depth 15, residue 7115. -/
theorem bounds_15_7115 : exactInterval 15 7115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7115 : oddCount 7115 15 = 7 ∧ acceleratedOrbit 15 7115 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7115) = 3 ^ 7 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7115.1, data_15_7115.2]

/-- Complete interval computation for depth 15, residue 7116. -/
theorem bounds_15_7116 : exactInterval 15 7116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7116 : oddCount 7116 15 = 9 ∧ acceleratedOrbit 15 7116 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7116) = 3 ^ 9 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7116.1, data_15_7116.2]

/-- Complete interval computation for depth 15, residue 7117. -/
theorem bounds_15_7117 : exactInterval 15 7117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7117 : oddCount 7117 15 = 9 ∧ acceleratedOrbit 15 7117 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7117) = 3 ^ 9 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7117.1, data_15_7117.2]

/-- Complete interval computation for depth 15, residue 7118. -/
theorem bounds_15_7118 : exactInterval 15 7118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7118 : oddCount 7118 15 = 8 ∧ acceleratedOrbit 15 7118 = 1426 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7118) = 3 ^ 8 * m + 1426 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7118.1, data_15_7118.2]

/-- Complete interval computation for depth 15, residue 7119. -/
theorem bounds_15_7119 : exactInterval 15 7119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7119 : oddCount 7119 15 = 8 ∧ acceleratedOrbit 15 7119 = 1426 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7119) = 3 ^ 8 * m + 1426 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7119.1, data_15_7119.2]

/-- Complete interval computation for depth 15, residue 7120. -/
theorem bounds_15_7120 : exactInterval 15 7120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7120 : oddCount 7120 15 = 7 ∧ acceleratedOrbit 15 7120 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7120) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7120.1, data_15_7120.2]

/-- Complete interval computation for depth 15, residue 7121. -/
theorem bounds_15_7121 : exactInterval 15 7121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7121 : oddCount 7121 15 = 9 ∧ acceleratedOrbit 15 7121 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7121) = 3 ^ 9 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7121.1, data_15_7121.2]

/-- Complete interval computation for depth 15, residue 7122. -/
theorem bounds_15_7122 : exactInterval 15 7122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7122 : oddCount 7122 15 = 10 ∧ acceleratedOrbit 15 7122 = 12842 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7122) = 3 ^ 10 * m + 12842 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7122.1, data_15_7122.2]

/-- Complete interval computation for depth 15, residue 7123. -/
theorem bounds_15_7123 : exactInterval 15 7123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7123 : oddCount 7123 15 = 10 ∧ acceleratedOrbit 15 7123 = 12842 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7123) = 3 ^ 10 * m + 12842 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7123.1, data_15_7123.2]

/-- Complete interval computation for depth 15, residue 7124. -/
theorem bounds_15_7124 : exactInterval 15 7124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7124 : oddCount 7124 15 = 7 ∧ acceleratedOrbit 15 7124 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7124) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7124.1, data_15_7124.2]

/-- Complete interval computation for depth 15, residue 7125. -/
theorem bounds_15_7125 : exactInterval 15 7125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7125 : oddCount 7125 15 = 7 ∧ acceleratedOrbit 15 7125 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7125) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7125.1, data_15_7125.2]

/-- Complete interval computation for depth 15, residue 7126. -/
theorem bounds_15_7126 : exactInterval 15 7126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7126 : oddCount 7126 15 = 11 ∧ acceleratedOrbit 15 7126 = 38546 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7126) = 3 ^ 11 * m + 38546 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7126.1, data_15_7126.2]

/-- Complete interval computation for depth 15, residue 7127. -/
theorem bounds_15_7127 : exactInterval 15 7127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7127 : oddCount 7127 15 = 11 ∧ acceleratedOrbit 15 7127 = 38546 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7127) = 3 ^ 11 * m + 38546 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7127.1, data_15_7127.2]

/-- Complete interval computation for depth 15, residue 7128. -/
theorem bounds_15_7128 : exactInterval 15 7128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7128 : oddCount 7128 15 = 9 ∧ acceleratedOrbit 15 7128 = 4292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7128) = 3 ^ 9 * m + 4292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7128.1, data_15_7128.2]

/-- Complete interval computation for depth 15, residue 7129. -/
theorem bounds_15_7129 : exactInterval 15 7129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7129 : oddCount 7129 15 = 6 ∧ acceleratedOrbit 15 7129 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7129) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7129.1, data_15_7129.2]

/-- Complete interval computation for depth 15, residue 7130. -/
theorem bounds_15_7130 : exactInterval 15 7130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7130 : oddCount 7130 15 = 9 ∧ acceleratedOrbit 15 7130 = 4292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7130) = 3 ^ 9 * m + 4292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7130.1, data_15_7130.2]

/-- Complete interval computation for depth 15, residue 7131. -/
theorem bounds_15_7131 : exactInterval 15 7131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7131 : oddCount 7131 15 = 9 ∧ acceleratedOrbit 15 7131 = 4286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7131) = 3 ^ 9 * m + 4286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7131.1, data_15_7131.2]

/-- Complete interval computation for depth 15, residue 7132. -/
theorem bounds_15_7132 : exactInterval 15 7132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7132 : oddCount 7132 15 = 9 ∧ acceleratedOrbit 15 7132 = 4292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7132) = 3 ^ 9 * m + 4292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7132.1, data_15_7132.2]

/-- Complete interval computation for depth 15, residue 7133. -/
theorem bounds_15_7133 : exactInterval 15 7133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7133 : oddCount 7133 15 = 9 ∧ acceleratedOrbit 15 7133 = 4292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7133) = 3 ^ 9 * m + 4292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7133.1, data_15_7133.2]

/-- Complete interval computation for depth 15, residue 7134. -/
theorem bounds_15_7134 : exactInterval 15 7134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7134 : oddCount 7134 15 = 11 ∧ acceleratedOrbit 15 7134 = 38582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7134) = 3 ^ 11 * m + 38582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7134.1, data_15_7134.2]

/-- Complete interval computation for depth 15, residue 7135. -/
theorem bounds_15_7135 : exactInterval 15 7135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7135 : oddCount 7135 15 = 11 ∧ acceleratedOrbit 15 7135 = 38582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7135) = 3 ^ 11 * m + 38582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7135.1, data_15_7135.2]

/-- Complete interval computation for depth 15, residue 7136. -/
theorem bounds_15_7136 : exactInterval 15 7136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7136 : oddCount 7136 15 = 7 ∧ acceleratedOrbit 15 7136 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7136) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7136.1, data_15_7136.2]

/-- Complete interval computation for depth 15, residue 7137. -/
theorem bounds_15_7137 : exactInterval 15 7137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7137 : oddCount 7137 15 = 8 ∧ acceleratedOrbit 15 7137 = 1430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7137) = 3 ^ 8 * m + 1430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7137.1, data_15_7137.2]

/-- Complete interval computation for depth 15, residue 7138. -/
theorem bounds_15_7138 : exactInterval 15 7138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7138 : oddCount 7138 15 = 7 ∧ acceleratedOrbit 15 7138 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7138) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7138.1, data_15_7138.2]

/-- Complete interval computation for depth 15, residue 7139. -/
theorem bounds_15_7139 : exactInterval 15 7139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7139 : oddCount 7139 15 = 7 ∧ acceleratedOrbit 15 7139 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7139) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7139.1, data_15_7139.2]

/-- Complete interval computation for depth 15, residue 7140. -/
theorem bounds_15_7140 : exactInterval 15 7140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7140 : oddCount 7140 15 = 5 ∧ acceleratedOrbit 15 7140 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7140) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7140.1, data_15_7140.2]

/-- Complete interval computation for depth 15, residue 7141. -/
theorem bounds_15_7141 : exactInterval 15 7141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7141 : oddCount 7141 15 = 5 ∧ acceleratedOrbit 15 7141 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7141) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7141.1, data_15_7141.2]

/-- Complete interval computation for depth 15, residue 7142. -/
theorem bounds_15_7142 : exactInterval 15 7142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7142 : oddCount 7142 15 = 5 ∧ acceleratedOrbit 15 7142 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7142) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7142.1, data_15_7142.2]

end Collatz.Research.PassageAtlas.Batch0218
