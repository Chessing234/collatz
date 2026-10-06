import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0947

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30998. -/
theorem bounds_15_30998 : exactInterval 15 30998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30998 : oddCount 30998 15 = 8 ∧ acceleratedOrbit 15 30998 = 6209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30998) = 3 ^ 8 * m + 6209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30998.1, data_15_30998.2]

/-- Complete interval computation for depth 15, residue 30999. -/
theorem bounds_15_30999 : exactInterval 15 30999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30999 : oddCount 30999 15 = 8 ∧ acceleratedOrbit 15 30999 = 6209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30999) = 3 ^ 8 * m + 6209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30999.1, data_15_30999.2]

/-- Complete interval computation for depth 15, residue 31000. -/
theorem bounds_15_31000 : exactInterval 15 31000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31000 : oddCount 31000 15 = 6 ∧ acceleratedOrbit 15 31000 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31000) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31000.1, data_15_31000.2]

/-- Complete interval computation for depth 15, residue 31001. -/
theorem bounds_15_31001 : exactInterval 15 31001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31001 : oddCount 31001 15 = 8 ∧ acceleratedOrbit 15 31001 = 6209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31001) = 3 ^ 8 * m + 6209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31001.1, data_15_31001.2]

/-- Complete interval computation for depth 15, residue 31002. -/
theorem bounds_15_31002 : exactInterval 15 31002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31002 : oddCount 31002 15 = 6 ∧ acceleratedOrbit 15 31002 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31002) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31002.1, data_15_31002.2]

/-- Complete interval computation for depth 15, residue 31003. -/
theorem bounds_15_31003 : exactInterval 15 31003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31003 : oddCount 31003 15 = 11 ∧ acceleratedOrbit 15 31003 = 167615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31003) = 3 ^ 11 * m + 167615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31003.1, data_15_31003.2]

/-- Complete interval computation for depth 15, residue 31004. -/
theorem bounds_15_31004 : exactInterval 15 31004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31004 : oddCount 31004 15 = 9 ∧ acceleratedOrbit 15 31004 = 18629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31004) = 3 ^ 9 * m + 18629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31004.1, data_15_31004.2]

/-- Complete interval computation for depth 15, residue 31005. -/
theorem bounds_15_31005 : exactInterval 15 31005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31005 : oddCount 31005 15 = 9 ∧ acceleratedOrbit 15 31005 = 18629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31005) = 3 ^ 9 * m + 18629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31005.1, data_15_31005.2]

/-- Complete interval computation for depth 15, residue 31006. -/
theorem bounds_15_31006 : exactInterval 15 31006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31006 : oddCount 31006 15 = 9 ∧ acceleratedOrbit 15 31006 = 18629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31006) = 3 ^ 9 * m + 18629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31006.1, data_15_31006.2]

/-- Complete interval computation for depth 15, residue 31007. -/
theorem bounds_15_31007 : exactInterval 15 31007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31007 : oddCount 31007 15 = 10 ∧ acceleratedOrbit 15 31007 = 55880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31007) = 3 ^ 10 * m + 55880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31007.1, data_15_31007.2]

/-- Complete interval computation for depth 15, residue 31008. -/
theorem bounds_15_31008 : exactInterval 15 31008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31008 : oddCount 31008 15 = 6 ∧ acceleratedOrbit 15 31008 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31008) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31008.1, data_15_31008.2]

/-- Complete interval computation for depth 15, residue 31009. -/
theorem bounds_15_31009 : exactInterval 15 31009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31009 : oddCount 31009 15 = 5 ∧ acceleratedOrbit 15 31009 = 230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31009) = 3 ^ 5 * m + 230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31009.1, data_15_31009.2]

/-- Complete interval computation for depth 15, residue 31010. -/
theorem bounds_15_31010 : exactInterval 15 31010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31010 : oddCount 31010 15 = 8 ∧ acceleratedOrbit 15 31010 = 6212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31010) = 3 ^ 8 * m + 6212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31010.1, data_15_31010.2]

/-- Complete interval computation for depth 15, residue 31011. -/
theorem bounds_15_31011 : exactInterval 15 31011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31011 : oddCount 31011 15 = 8 ∧ acceleratedOrbit 15 31011 = 6212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31011) = 3 ^ 8 * m + 6212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31011.1, data_15_31011.2]

/-- Complete interval computation for depth 15, residue 31012. -/
theorem bounds_15_31012 : exactInterval 15 31012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31012 : oddCount 31012 15 = 8 ∧ acceleratedOrbit 15 31012 = 6212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31012) = 3 ^ 8 * m + 6212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31012.1, data_15_31012.2]

/-- Complete interval computation for depth 15, residue 31013. -/
theorem bounds_15_31013 : exactInterval 15 31013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31013 : oddCount 31013 15 = 8 ∧ acceleratedOrbit 15 31013 = 6212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31013) = 3 ^ 8 * m + 6212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31013.1, data_15_31013.2]

/-- Complete interval computation for depth 15, residue 31014. -/
theorem bounds_15_31014 : exactInterval 15 31014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31014 : oddCount 31014 15 = 8 ∧ acceleratedOrbit 15 31014 = 6212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31014) = 3 ^ 8 * m + 6212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31014.1, data_15_31014.2]

/-- Complete interval computation for depth 15, residue 31015. -/
theorem bounds_15_31015 : exactInterval 15 31015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31015 : oddCount 31015 15 = 9 ∧ acceleratedOrbit 15 31015 = 18632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31015) = 3 ^ 9 * m + 18632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31015.1, data_15_31015.2]

/-- Complete interval computation for depth 15, residue 31016. -/
theorem bounds_15_31016 : exactInterval 15 31016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31016 : oddCount 31016 15 = 6 ∧ acceleratedOrbit 15 31016 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31016) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31016.1, data_15_31016.2]

/-- Complete interval computation for depth 15, residue 31017. -/
theorem bounds_15_31017 : exactInterval 15 31017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31017 : oddCount 31017 15 = 8 ∧ acceleratedOrbit 15 31017 = 6211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31017) = 3 ^ 8 * m + 6211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31017.1, data_15_31017.2]

/-- Complete interval computation for depth 15, residue 31018. -/
theorem bounds_15_31018 : exactInterval 15 31018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31018 : oddCount 31018 15 = 6 ∧ acceleratedOrbit 15 31018 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31018) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31018.1, data_15_31018.2]

/-- Complete interval computation for depth 15, residue 31019. -/
theorem bounds_15_31019 : exactInterval 15 31019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31019 : oddCount 31019 15 = 8 ∧ acceleratedOrbit 15 31019 = 6212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31019) = 3 ^ 8 * m + 6212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31019.1, data_15_31019.2]

/-- Complete interval computation for depth 15, residue 31020. -/
theorem bounds_15_31020 : exactInterval 15 31020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31020 : oddCount 31020 15 = 6 ∧ acceleratedOrbit 15 31020 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31020) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31020.1, data_15_31020.2]

/-- Complete interval computation for depth 15, residue 31021. -/
theorem bounds_15_31021 : exactInterval 15 31021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31021 : oddCount 31021 15 = 6 ∧ acceleratedOrbit 15 31021 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31021) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31021.1, data_15_31021.2]

/-- Complete interval computation for depth 15, residue 31022. -/
theorem bounds_15_31022 : exactInterval 15 31022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31022 : oddCount 31022 15 = 6 ∧ acceleratedOrbit 15 31022 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31022) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31022.1, data_15_31022.2]

/-- Complete interval computation for depth 15, residue 31023. -/
theorem bounds_15_31023 : exactInterval 15 31023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31023 : oddCount 31023 15 = 8 ∧ acceleratedOrbit 15 31023 = 6212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31023) = 3 ^ 8 * m + 6212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31023.1, data_15_31023.2]

/-- Complete interval computation for depth 15, residue 31024. -/
theorem bounds_15_31024 : exactInterval 15 31024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31024 : oddCount 31024 15 = 6 ∧ acceleratedOrbit 15 31024 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31024) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31024.1, data_15_31024.2]

/-- Complete interval computation for depth 15, residue 31025. -/
theorem bounds_15_31025 : exactInterval 15 31025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31025 : oddCount 31025 15 = 7 ∧ acceleratedOrbit 15 31025 = 2072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31025) = 3 ^ 7 * m + 2072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31025.1, data_15_31025.2]

/-- Complete interval computation for depth 15, residue 31026. -/
theorem bounds_15_31026 : exactInterval 15 31026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31026 : oddCount 31026 15 = 7 ∧ acceleratedOrbit 15 31026 = 2072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31026) = 3 ^ 7 * m + 2072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31026.1, data_15_31026.2]

/-- Complete interval computation for depth 15, residue 31027. -/
theorem bounds_15_31027 : exactInterval 15 31027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31027 : oddCount 31027 15 = 7 ∧ acceleratedOrbit 15 31027 = 2072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31027) = 3 ^ 7 * m + 2072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31027.1, data_15_31027.2]

/-- Complete interval computation for depth 15, residue 31028. -/
theorem bounds_15_31028 : exactInterval 15 31028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31028 : oddCount 31028 15 = 6 ∧ acceleratedOrbit 15 31028 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31028) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31028.1, data_15_31028.2]

/-- Complete interval computation for depth 15, residue 31029. -/
theorem bounds_15_31029 : exactInterval 15 31029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31029 : oddCount 31029 15 = 6 ∧ acceleratedOrbit 15 31029 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31029) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31029.1, data_15_31029.2]

/-- Complete interval computation for depth 15, residue 31030. -/
theorem bounds_15_31030 : exactInterval 15 31030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31030 : oddCount 31030 15 = 9 ∧ acceleratedOrbit 15 31030 = 18641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31030) = 3 ^ 9 * m + 18641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31030.1, data_15_31030.2]

end Collatz.Research.PassageAtlas.Batch0947
