import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0123

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3997. -/
theorem bounds_15_3997 : exactInterval 15 3997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3997 : oddCount 3997 15 = 6 ∧ acceleratedOrbit 15 3997 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3997) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3997.1, data_15_3997.2]

/-- Complete interval computation for depth 15, residue 3998. -/
theorem bounds_15_3998 : exactInterval 15 3998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3998 : oddCount 3998 15 = 6 ∧ acceleratedOrbit 15 3998 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3998) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3998.1, data_15_3998.2]

/-- Complete interval computation for depth 15, residue 3999. -/
theorem bounds_15_3999 : exactInterval 15 3999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3999 : oddCount 3999 15 = 12 ∧ acceleratedOrbit 15 3999 = 64880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3999) = 3 ^ 12 * m + 64880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3999.1, data_15_3999.2]

/-- Complete interval computation for depth 15, residue 4000. -/
theorem bounds_15_4000 : exactInterval 15 4000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4000 : oddCount 4000 15 = 6 ∧ acceleratedOrbit 15 4000 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4000) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4000.1, data_15_4000.2]

/-- Complete interval computation for depth 15, residue 4001. -/
theorem bounds_15_4001 : exactInterval 15 4001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4001 : oddCount 4001 15 = 8 ∧ acceleratedOrbit 15 4001 = 803 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4001) = 3 ^ 8 * m + 803 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4001.1, data_15_4001.2]

/-- Complete interval computation for depth 15, residue 4002. -/
theorem bounds_15_4002 : exactInterval 15 4002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4002 : oddCount 4002 15 = 7 ∧ acceleratedOrbit 15 4002 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4002) = 3 ^ 7 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4002.1, data_15_4002.2]

/-- Complete interval computation for depth 15, residue 4003. -/
theorem bounds_15_4003 : exactInterval 15 4003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4003 : oddCount 4003 15 = 7 ∧ acceleratedOrbit 15 4003 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4003) = 3 ^ 7 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4003.1, data_15_4003.2]

/-- Complete interval computation for depth 15, residue 4004. -/
theorem bounds_15_4004 : exactInterval 15 4004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4004 : oddCount 4004 15 = 10 ∧ acceleratedOrbit 15 4004 = 7229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4004) = 3 ^ 10 * m + 7229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4004.1, data_15_4004.2]

/-- Complete interval computation for depth 15, residue 4005. -/
theorem bounds_15_4005 : exactInterval 15 4005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4005 : oddCount 4005 15 = 10 ∧ acceleratedOrbit 15 4005 = 7229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4005) = 3 ^ 10 * m + 7229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4005.1, data_15_4005.2]

/-- Complete interval computation for depth 15, residue 4006. -/
theorem bounds_15_4006 : exactInterval 15 4006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4006 : oddCount 4006 15 = 10 ∧ acceleratedOrbit 15 4006 = 7229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4006) = 3 ^ 10 * m + 7229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4006.1, data_15_4006.2]

/-- Complete interval computation for depth 15, residue 4007. -/
theorem bounds_15_4007 : exactInterval 15 4007 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4007) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4007 : oddCount 4007 15 = 9 ∧ acceleratedOrbit 15 4007 = 2408 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4007) = 3 ^ 9 * m + 2408 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4007.1, data_15_4007.2]

/-- Complete interval computation for depth 15, residue 4008. -/
theorem bounds_15_4008 : exactInterval 15 4008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4008 : oddCount 4008 15 = 6 ∧ acceleratedOrbit 15 4008 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4008) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4008.1, data_15_4008.2]

/-- Complete interval computation for depth 15, residue 4009. -/
theorem bounds_15_4009 : exactInterval 15 4009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4009 : oddCount 4009 15 = 11 ∧ acceleratedOrbit 15 4009 = 21683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4009) = 3 ^ 11 * m + 21683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4009.1, data_15_4009.2]

/-- Complete interval computation for depth 15, residue 4010. -/
theorem bounds_15_4010 : exactInterval 15 4010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4010 : oddCount 4010 15 = 6 ∧ acceleratedOrbit 15 4010 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4010) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4010.1, data_15_4010.2]

/-- Complete interval computation for depth 15, residue 4011. -/
theorem bounds_15_4011 : exactInterval 15 4011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4011 : oddCount 4011 15 = 10 ∧ acceleratedOrbit 15 4011 = 7235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4011) = 3 ^ 10 * m + 7235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4011.1, data_15_4011.2]

/-- Complete interval computation for depth 15, residue 4012. -/
theorem bounds_15_4012 : exactInterval 15 4012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4012 : oddCount 4012 15 = 8 ∧ acceleratedOrbit 15 4012 = 805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4012) = 3 ^ 8 * m + 805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4012.1, data_15_4012.2]

/-- Complete interval computation for depth 15, residue 4013. -/
theorem bounds_15_4013 : exactInterval 15 4013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4013 : oddCount 4013 15 = 8 ∧ acceleratedOrbit 15 4013 = 805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4013) = 3 ^ 8 * m + 805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4013.1, data_15_4013.2]

/-- Complete interval computation for depth 15, residue 4014. -/
theorem bounds_15_4014 : exactInterval 15 4014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4014 : oddCount 4014 15 = 8 ∧ acceleratedOrbit 15 4014 = 805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4014) = 3 ^ 8 * m + 805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4014.1, data_15_4014.2]

/-- Complete interval computation for depth 15, residue 4015. -/
theorem bounds_15_4015 : exactInterval 15 4015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4015 : oddCount 4015 15 = 8 ∧ acceleratedOrbit 15 4015 = 805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4015) = 3 ^ 8 * m + 805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4015.1, data_15_4015.2]

/-- Complete interval computation for depth 15, residue 4016. -/
theorem bounds_15_4016 : exactInterval 15 4016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4016 : oddCount 4016 15 = 9 ∧ acceleratedOrbit 15 4016 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4016) = 3 ^ 9 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4016.1, data_15_4016.2]

/-- Complete interval computation for depth 15, residue 4017. -/
theorem bounds_15_4017 : exactInterval 15 4017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4017 : oddCount 4017 15 = 4 ∧ acceleratedOrbit 15 4017 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4017) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4017.1, data_15_4017.2]

/-- Complete interval computation for depth 15, residue 4018. -/
theorem bounds_15_4018 : exactInterval 15 4018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4018 : oddCount 4018 15 = 4 ∧ acceleratedOrbit 15 4018 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4018) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4018.1, data_15_4018.2]

/-- Complete interval computation for depth 15, residue 4019. -/
theorem bounds_15_4019 : exactInterval 15 4019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4019 : oddCount 4019 15 = 4 ∧ acceleratedOrbit 15 4019 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4019) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4019.1, data_15_4019.2]

/-- Complete interval computation for depth 15, residue 4020. -/
theorem bounds_15_4020 : exactInterval 15 4020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4020 : oddCount 4020 15 = 9 ∧ acceleratedOrbit 15 4020 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4020) = 3 ^ 9 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4020.1, data_15_4020.2]

/-- Complete interval computation for depth 15, residue 4021. -/
theorem bounds_15_4021 : exactInterval 15 4021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4021 : oddCount 4021 15 = 9 ∧ acceleratedOrbit 15 4021 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4021) = 3 ^ 9 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4021.1, data_15_4021.2]

/-- Complete interval computation for depth 15, residue 4022. -/
theorem bounds_15_4022 : exactInterval 15 4022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4022 : oddCount 4022 15 = 9 ∧ acceleratedOrbit 15 4022 = 2420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4022) = 3 ^ 9 * m + 2420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4022.1, data_15_4022.2]

/-- Complete interval computation for depth 15, residue 4023. -/
theorem bounds_15_4023 : exactInterval 15 4023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4023 : oddCount 4023 15 = 9 ∧ acceleratedOrbit 15 4023 = 2420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4023) = 3 ^ 9 * m + 2420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4023.1, data_15_4023.2]

/-- Complete interval computation for depth 15, residue 4024. -/
theorem bounds_15_4024 : exactInterval 15 4024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4024 : oddCount 4024 15 = 9 ∧ acceleratedOrbit 15 4024 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4024) = 3 ^ 9 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4024.1, data_15_4024.2]

/-- Complete interval computation for depth 15, residue 4025. -/
theorem bounds_15_4025 : exactInterval 15 4025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4025 : oddCount 4025 15 = 8 ∧ acceleratedOrbit 15 4025 = 809 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4025) = 3 ^ 8 * m + 809 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4025.1, data_15_4025.2]

/-- Complete interval computation for depth 15, residue 4026. -/
theorem bounds_15_4026 : exactInterval 15 4026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4026 : oddCount 4026 15 = 9 ∧ acceleratedOrbit 15 4026 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4026) = 3 ^ 9 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4026.1, data_15_4026.2]

/-- Complete interval computation for depth 15, residue 4027. -/
theorem bounds_15_4027 : exactInterval 15 4027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4027 : oddCount 4027 15 = 8 ∧ acceleratedOrbit 15 4027 = 809 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4027) = 3 ^ 8 * m + 809 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4027.1, data_15_4027.2]

/-- Complete interval computation for depth 15, residue 4028. -/
theorem bounds_15_4028 : exactInterval 15 4028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4028 : oddCount 4028 15 = 9 ∧ acceleratedOrbit 15 4028 = 2423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4028) = 3 ^ 9 * m + 2423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4028.1, data_15_4028.2]

/-- Complete interval computation for depth 15, residue 4029. -/
theorem bounds_15_4029 : exactInterval 15 4029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4029 : oddCount 4029 15 = 9 ∧ acceleratedOrbit 15 4029 = 2423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4029) = 3 ^ 9 * m + 2423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4029.1, data_15_4029.2]

end Collatz.Research.PassageAtlas.Batch0123
