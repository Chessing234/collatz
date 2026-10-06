import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0931

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7116. -/
theorem bounds_13_7116 : exactInterval 13 7116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7116 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7116) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7116 : oddCount 7116 13 = 7 ∧ acceleratedOrbit 13 7116 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7116 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7116) = 3 ^ 7 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7116.1, data_13_7116.2]

/-- Complete interval computation for depth 13, residue 7117. -/
theorem bounds_13_7117 : exactInterval 13 7117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7117 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7117) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7117 : oddCount 7117 13 = 7 ∧ acceleratedOrbit 13 7117 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7117 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7117) = 3 ^ 7 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7117.1, data_13_7117.2]

/-- Complete interval computation for depth 13, residue 7118. -/
theorem bounds_13_7118 : exactInterval 13 7118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7118 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7118) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7118 : oddCount 7118 13 = 7 ∧ acceleratedOrbit 13 7118 = 1901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7118 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7118) = 3 ^ 7 * m + 1901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7118.1, data_13_7118.2]

/-- Complete interval computation for depth 13, residue 7119. -/
theorem bounds_13_7119 : exactInterval 13 7119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7119 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7119) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7119 : oddCount 7119 13 = 7 ∧ acceleratedOrbit 13 7119 = 1901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7119 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7119) = 3 ^ 7 * m + 1901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7119.1, data_13_7119.2]

/-- Complete interval computation for depth 13, residue 7120. -/
theorem bounds_13_7120 : exactInterval 13 7120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7120 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7120) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7120 : oddCount 7120 13 = 6 ∧ acceleratedOrbit 13 7120 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7120 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7120) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7120.1, data_13_7120.2]

/-- Complete interval computation for depth 13, residue 7121. -/
theorem bounds_13_7121 : exactInterval 13 7121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7121 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7121) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7121 : oddCount 7121 13 = 7 ∧ acceleratedOrbit 13 7121 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7121 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7121) = 3 ^ 7 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7121.1, data_13_7121.2]

/-- Complete interval computation for depth 13, residue 7122. -/
theorem bounds_13_7122 : exactInterval 13 7122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7122 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7122) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7122 : oddCount 7122 13 = 8 ∧ acceleratedOrbit 13 7122 = 5707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7122 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7122) = 3 ^ 8 * m + 5707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7122.1, data_13_7122.2]

/-- Complete interval computation for depth 13, residue 7123. -/
theorem bounds_13_7123 : exactInterval 13 7123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7123 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7123) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7123 : oddCount 7123 13 = 8 ∧ acceleratedOrbit 13 7123 = 5707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7123 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7123) = 3 ^ 8 * m + 5707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7123.1, data_13_7123.2]

/-- Complete interval computation for depth 13, residue 7124. -/
theorem bounds_13_7124 : exactInterval 13 7124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7124 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7124) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7124 : oddCount 7124 13 = 6 ∧ acceleratedOrbit 13 7124 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7124 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7124) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7124.1, data_13_7124.2]

/-- Complete interval computation for depth 13, residue 7125. -/
theorem bounds_13_7125 : exactInterval 13 7125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7125 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7125) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7125 : oddCount 7125 13 = 6 ∧ acceleratedOrbit 13 7125 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7125 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7125) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7125.1, data_13_7125.2]

/-- Complete interval computation for depth 13, residue 7126. -/
theorem bounds_13_7126 : exactInterval 13 7126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7126 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7126) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7126 : oddCount 7126 13 = 9 ∧ acceleratedOrbit 13 7126 = 17131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7126 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7126) = 3 ^ 9 * m + 17131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7126.1, data_13_7126.2]

/-- Complete interval computation for depth 13, residue 7127. -/
theorem bounds_13_7127 : exactInterval 13 7127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7127 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7127) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7127 : oddCount 7127 13 = 9 ∧ acceleratedOrbit 13 7127 = 17131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7127 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7127) = 3 ^ 9 * m + 17131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7127.1, data_13_7127.2]

/-- Complete interval computation for depth 13, residue 7128. -/
theorem bounds_13_7128 : exactInterval 13 7128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7128 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7128) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7128 : oddCount 7128 13 = 7 ∧ acceleratedOrbit 13 7128 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7128 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7128) = 3 ^ 7 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7128.1, data_13_7128.2]

/-- Complete interval computation for depth 13, residue 7129. -/
theorem bounds_13_7129 : exactInterval 13 7129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7129 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7129) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7129 : oddCount 7129 13 = 4 ∧ acceleratedOrbit 13 7129 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7129 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7129) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7129.1, data_13_7129.2]

/-- Complete interval computation for depth 13, residue 7130. -/
theorem bounds_13_7130 : exactInterval 13 7130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7130 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7130) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7130 : oddCount 7130 13 = 7 ∧ acceleratedOrbit 13 7130 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7130 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7130) = 3 ^ 7 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7130.1, data_13_7130.2]

/-- Complete interval computation for depth 13, residue 7131. -/
theorem bounds_13_7131 : exactInterval 13 7131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7131 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7131) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7131 : oddCount 7131 13 = 8 ∧ acceleratedOrbit 13 7131 = 5714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7131 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7131) = 3 ^ 8 * m + 5714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7131.1, data_13_7131.2]

end Collatz.Research.StoppingAtlas.Batch0931
