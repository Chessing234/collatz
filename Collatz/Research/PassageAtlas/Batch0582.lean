import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0582

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19038. -/
theorem bounds_15_19038 : exactInterval 15 19038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19038 : oddCount 19038 15 = 9 ∧ acceleratedOrbit 15 19038 = 11438 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19038) = 3 ^ 9 * m + 11438 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19038.1, data_15_19038.2]

/-- Complete interval computation for depth 15, residue 19039. -/
theorem bounds_15_19039 : exactInterval 15 19039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19039 : oddCount 19039 15 = 9 ∧ acceleratedOrbit 15 19039 = 11438 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19039) = 3 ^ 9 * m + 11438 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19039.1, data_15_19039.2]

/-- Complete interval computation for depth 15, residue 19040. -/
theorem bounds_15_19040 : exactInterval 15 19040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19040 : oddCount 19040 15 = 6 ∧ acceleratedOrbit 15 19040 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19040) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19040.1, data_15_19040.2]

/-- Complete interval computation for depth 15, residue 19041. -/
theorem bounds_15_19041 : exactInterval 15 19041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19041 : oddCount 19041 15 = 9 ∧ acceleratedOrbit 15 19041 = 11441 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19041) = 3 ^ 9 * m + 11441 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19041.1, data_15_19041.2]

/-- Complete interval computation for depth 15, residue 19042. -/
theorem bounds_15_19042 : exactInterval 15 19042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19042 : oddCount 19042 15 = 6 ∧ acceleratedOrbit 15 19042 = 424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19042) = 3 ^ 6 * m + 424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19042.1, data_15_19042.2]

/-- Complete interval computation for depth 15, residue 19043. -/
theorem bounds_15_19043 : exactInterval 15 19043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19043 : oddCount 19043 15 = 6 ∧ acceleratedOrbit 15 19043 = 424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19043) = 3 ^ 6 * m + 424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19043.1, data_15_19043.2]

/-- Complete interval computation for depth 15, residue 19044. -/
theorem bounds_15_19044 : exactInterval 15 19044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19044 : oddCount 19044 15 = 6 ∧ acceleratedOrbit 15 19044 = 424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19044) = 3 ^ 6 * m + 424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19044.1, data_15_19044.2]

/-- Complete interval computation for depth 15, residue 19045. -/
theorem bounds_15_19045 : exactInterval 15 19045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19045 : oddCount 19045 15 = 6 ∧ acceleratedOrbit 15 19045 = 424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19045) = 3 ^ 6 * m + 424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19045.1, data_15_19045.2]

/-- Complete interval computation for depth 15, residue 19046. -/
theorem bounds_15_19046 : exactInterval 15 19046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19046 : oddCount 19046 15 = 6 ∧ acceleratedOrbit 15 19046 = 424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19046) = 3 ^ 6 * m + 424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19046.1, data_15_19046.2]

/-- Complete interval computation for depth 15, residue 19047. -/
theorem bounds_15_19047 : exactInterval 15 19047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19047 : oddCount 19047 15 = 8 ∧ acceleratedOrbit 15 19047 = 3814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19047) = 3 ^ 8 * m + 3814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19047.1, data_15_19047.2]

/-- Complete interval computation for depth 15, residue 19048. -/
theorem bounds_15_19048 : exactInterval 15 19048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19048 : oddCount 19048 15 = 6 ∧ acceleratedOrbit 15 19048 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19048) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19048.1, data_15_19048.2]

/-- Complete interval computation for depth 15, residue 19049. -/
theorem bounds_15_19049 : exactInterval 15 19049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19049 : oddCount 19049 15 = 8 ∧ acceleratedOrbit 15 19049 = 3815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19049) = 3 ^ 8 * m + 3815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19049.1, data_15_19049.2]

/-- Complete interval computation for depth 15, residue 19050. -/
theorem bounds_15_19050 : exactInterval 15 19050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19050 : oddCount 19050 15 = 6 ∧ acceleratedOrbit 15 19050 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19050) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19050.1, data_15_19050.2]

/-- Complete interval computation for depth 15, residue 19051. -/
theorem bounds_15_19051 : exactInterval 15 19051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19051 : oddCount 19051 15 = 9 ∧ acceleratedOrbit 15 19051 = 11447 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19051) = 3 ^ 9 * m + 11447 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19051.1, data_15_19051.2]

/-- Complete interval computation for depth 15, residue 19052. -/
theorem bounds_15_19052 : exactInterval 15 19052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19052 : oddCount 19052 15 = 11 ∧ acceleratedOrbit 15 19052 = 103031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19052) = 3 ^ 11 * m + 103031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19052.1, data_15_19052.2]

/-- Complete interval computation for depth 15, residue 19053. -/
theorem bounds_15_19053 : exactInterval 15 19053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19053 : oddCount 19053 15 = 11 ∧ acceleratedOrbit 15 19053 = 103031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19053) = 3 ^ 11 * m + 103031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19053.1, data_15_19053.2]

/-- Complete interval computation for depth 15, residue 19054. -/
theorem bounds_15_19054 : exactInterval 15 19054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19054 : oddCount 19054 15 = 11 ∧ acceleratedOrbit 15 19054 = 103031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19054) = 3 ^ 11 * m + 103031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19054.1, data_15_19054.2]

/-- Complete interval computation for depth 15, residue 19055. -/
theorem bounds_15_19055 : exactInterval 15 19055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19055 : oddCount 19055 15 = 11 ∧ acceleratedOrbit 15 19055 = 103022 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19055) = 3 ^ 11 * m + 103022 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19055.1, data_15_19055.2]

/-- Complete interval computation for depth 15, residue 19056. -/
theorem bounds_15_19056 : exactInterval 15 19056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19056 : oddCount 19056 15 = 8 ∧ acceleratedOrbit 15 19056 = 3820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19056) = 3 ^ 8 * m + 3820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19056.1, data_15_19056.2]

/-- Complete interval computation for depth 15, residue 19057. -/
theorem bounds_15_19057 : exactInterval 15 19057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19057 : oddCount 19057 15 = 6 ∧ acceleratedOrbit 15 19057 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19057) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19057.1, data_15_19057.2]

/-- Complete interval computation for depth 15, residue 19058. -/
theorem bounds_15_19058 : exactInterval 15 19058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19058 : oddCount 19058 15 = 8 ∧ acceleratedOrbit 15 19058 = 3817 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19058) = 3 ^ 8 * m + 3817 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19058.1, data_15_19058.2]

/-- Complete interval computation for depth 15, residue 19059. -/
theorem bounds_15_19059 : exactInterval 15 19059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19059 : oddCount 19059 15 = 8 ∧ acceleratedOrbit 15 19059 = 3817 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19059) = 3 ^ 8 * m + 3817 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19059.1, data_15_19059.2]

/-- Complete interval computation for depth 15, residue 19060. -/
theorem bounds_15_19060 : exactInterval 15 19060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19060 : oddCount 19060 15 = 8 ∧ acceleratedOrbit 15 19060 = 3820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19060) = 3 ^ 8 * m + 3820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19060.1, data_15_19060.2]

/-- Complete interval computation for depth 15, residue 19061. -/
theorem bounds_15_19061 : exactInterval 15 19061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19061 : oddCount 19061 15 = 8 ∧ acceleratedOrbit 15 19061 = 3820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19061) = 3 ^ 8 * m + 3820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19061.1, data_15_19061.2]

/-- Complete interval computation for depth 15, residue 19062. -/
theorem bounds_15_19062 : exactInterval 15 19062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19062 : oddCount 19062 15 = 6 ∧ acceleratedOrbit 15 19062 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19062) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19062.1, data_15_19062.2]

/-- Complete interval computation for depth 15, residue 19063. -/
theorem bounds_15_19063 : exactInterval 15 19063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19063 : oddCount 19063 15 = 6 ∧ acceleratedOrbit 15 19063 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19063) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19063.1, data_15_19063.2]

/-- Complete interval computation for depth 15, residue 19064. -/
theorem bounds_15_19064 : exactInterval 15 19064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19064 : oddCount 19064 15 = 8 ∧ acceleratedOrbit 15 19064 = 3820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19064) = 3 ^ 8 * m + 3820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19064.1, data_15_19064.2]

/-- Complete interval computation for depth 15, residue 19065. -/
theorem bounds_15_19065 : exactInterval 15 19065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19065 : oddCount 19065 15 = 8 ∧ acceleratedOrbit 15 19065 = 3818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19065) = 3 ^ 8 * m + 3818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19065.1, data_15_19065.2]

/-- Complete interval computation for depth 15, residue 19066. -/
theorem bounds_15_19066 : exactInterval 15 19066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19066 : oddCount 19066 15 = 8 ∧ acceleratedOrbit 15 19066 = 3820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19066) = 3 ^ 8 * m + 3820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19066.1, data_15_19066.2]

/-- Complete interval computation for depth 15, residue 19067. -/
theorem bounds_15_19067 : exactInterval 15 19067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19067 : oddCount 19067 15 = 7 ∧ acceleratedOrbit 15 19067 = 1273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19067) = 3 ^ 7 * m + 1273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19067.1, data_15_19067.2]

/-- Complete interval computation for depth 15, residue 19068. -/
theorem bounds_15_19068 : exactInterval 15 19068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19068 : oddCount 19068 15 = 10 ∧ acceleratedOrbit 15 19068 = 34370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19068) = 3 ^ 10 * m + 34370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19068.1, data_15_19068.2]

/-- Complete interval computation for depth 15, residue 19069. -/
theorem bounds_15_19069 : exactInterval 15 19069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19069 : oddCount 19069 15 = 10 ∧ acceleratedOrbit 15 19069 = 34370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19069) = 3 ^ 10 * m + 34370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19069.1, data_15_19069.2]

end Collatz.Research.PassageAtlas.Batch0582
