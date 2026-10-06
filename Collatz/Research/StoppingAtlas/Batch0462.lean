import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0462

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 4008. -/
theorem bounds_12_4008 : exactInterval 12 4008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4008 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4008) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4008 : oddCount 4008 12 = 5 ∧ acceleratedOrbit 12 4008 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4008 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4008) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4008.1, data_12_4008.2]

/-- Complete interval computation for depth 12, residue 4009. -/
theorem bounds_12_4009 : exactInterval 12 4009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4009 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4009) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4009 : oddCount 4009 12 = 9 ∧ acceleratedOrbit 12 4009 = 19273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4009 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4009) = 3 ^ 9 * m + 19273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4009.1, data_12_4009.2]

/-- Complete interval computation for depth 12, residue 4010. -/
theorem bounds_12_4010 : exactInterval 12 4010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4010 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4010) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4010 : oddCount 4010 12 = 5 ∧ acceleratedOrbit 12 4010 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4010 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4010) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4010.1, data_12_4010.2]

/-- Complete interval computation for depth 12, residue 4011. -/
theorem bounds_12_4011 : exactInterval 12 4011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4011 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4011) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4011 : oddCount 4011 12 = 7 ∧ acceleratedOrbit 12 4011 = 2143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4011 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4011) = 3 ^ 7 * m + 2143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4011.1, data_12_4011.2]

/-- Complete interval computation for depth 12, residue 4012. -/
theorem bounds_12_4012 : exactInterval 12 4012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4012 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4012) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4012 : oddCount 4012 12 = 7 ∧ acceleratedOrbit 12 4012 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4012 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4012) = 3 ^ 7 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4012.1, data_12_4012.2]

/-- Complete interval computation for depth 12, residue 4013. -/
theorem bounds_12_4013 : exactInterval 12 4013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4013 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4013) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4013 : oddCount 4013 12 = 7 ∧ acceleratedOrbit 12 4013 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4013 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4013) = 3 ^ 7 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4013.1, data_12_4013.2]

/-- Complete interval computation for depth 12, residue 4014. -/
theorem bounds_12_4014 : exactInterval 12 4014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4014 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4014) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4014 : oddCount 4014 12 = 7 ∧ acceleratedOrbit 12 4014 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4014 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4014) = 3 ^ 7 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4014.1, data_12_4014.2]

/-- Complete interval computation for depth 12, residue 4015. -/
theorem bounds_12_4015 : exactInterval 12 4015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4015 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4015) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4015 : oddCount 4015 12 = 6 ∧ acceleratedOrbit 12 4015 = 715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4015 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4015) = 3 ^ 6 * m + 715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4015.1, data_12_4015.2]

/-- Complete interval computation for depth 12, residue 4016. -/
theorem bounds_12_4016 : exactInterval 12 4016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4016 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4016) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4016 : oddCount 4016 12 = 6 ∧ acceleratedOrbit 12 4016 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4016 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4016) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4016.1, data_12_4016.2]

/-- Complete interval computation for depth 12, residue 4017. -/
theorem bounds_12_4017 : exactInterval 12 4017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4017 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4017) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4017 : oddCount 4017 12 = 4 ∧ acceleratedOrbit 12 4017 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4017 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4017) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4017.1, data_12_4017.2]

/-- Complete interval computation for depth 12, residue 4018. -/
theorem bounds_12_4018 : exactInterval 12 4018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4018 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4018) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4018 : oddCount 4018 12 = 4 ∧ acceleratedOrbit 12 4018 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4018 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4018) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4018.1, data_12_4018.2]

/-- Complete interval computation for depth 12, residue 4019. -/
theorem bounds_12_4019 : exactInterval 12 4019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4019 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4019) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4019 : oddCount 4019 12 = 4 ∧ acceleratedOrbit 12 4019 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4019 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4019) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4019.1, data_12_4019.2]

/-- Complete interval computation for depth 12, residue 4020. -/
theorem bounds_12_4020 : exactInterval 12 4020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4020 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4020) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4020 : oddCount 4020 12 = 6 ∧ acceleratedOrbit 12 4020 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4020 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4020) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4020.1, data_12_4020.2]

/-- Complete interval computation for depth 12, residue 4021. -/
theorem bounds_12_4021 : exactInterval 12 4021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4021 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4021) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4021 : oddCount 4021 12 = 6 ∧ acceleratedOrbit 12 4021 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4021 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4021) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4021.1, data_12_4021.2]

/-- Complete interval computation for depth 12, residue 4022. -/
theorem bounds_12_4022 : exactInterval 12 4022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4022 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4022) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4022 : oddCount 4022 12 = 7 ∧ acceleratedOrbit 12 4022 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4022 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4022) = 3 ^ 7 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4022.1, data_12_4022.2]

/-- Complete interval computation for depth 12, residue 4023. -/
theorem bounds_12_4023 : exactInterval 12 4023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4023 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4023) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4023 : oddCount 4023 12 = 7 ∧ acceleratedOrbit 12 4023 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4023 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4023) = 3 ^ 7 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4023.1, data_12_4023.2]

end Collatz.Research.StoppingAtlas.Batch0462
