import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0332

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10846. -/
theorem bounds_15_10846 : exactInterval 15 10846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10846 : oddCount 10846 15 = 9 ∧ acceleratedOrbit 15 10846 = 6517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10846) = 3 ^ 9 * m + 6517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10846.1, data_15_10846.2]

/-- Complete interval computation for depth 15, residue 10847. -/
theorem bounds_15_10847 : exactInterval 15 10847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10847 : oddCount 10847 15 = 9 ∧ acceleratedOrbit 15 10847 = 6517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10847) = 3 ^ 9 * m + 6517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10847.1, data_15_10847.2]

/-- Complete interval computation for depth 15, residue 10848. -/
theorem bounds_15_10848 : exactInterval 15 10848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10848 : oddCount 10848 15 = 8 ∧ acceleratedOrbit 15 10848 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10848) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10848.1, data_15_10848.2]

/-- Complete interval computation for depth 15, residue 10849. -/
theorem bounds_15_10849 : exactInterval 15 10849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10849 : oddCount 10849 15 = 9 ∧ acceleratedOrbit 15 10849 = 6520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10849) = 3 ^ 9 * m + 6520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10849.1, data_15_10849.2]

/-- Complete interval computation for depth 15, residue 10850. -/
theorem bounds_15_10850 : exactInterval 15 10850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10850 : oddCount 10850 15 = 8 ∧ acceleratedOrbit 15 10850 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10850) = 3 ^ 8 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10850.1, data_15_10850.2]

/-- Complete interval computation for depth 15, residue 10851. -/
theorem bounds_15_10851 : exactInterval 15 10851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10851 : oddCount 10851 15 = 8 ∧ acceleratedOrbit 15 10851 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10851) = 3 ^ 8 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10851.1, data_15_10851.2]

/-- Complete interval computation for depth 15, residue 10852. -/
theorem bounds_15_10852 : exactInterval 15 10852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10852 : oddCount 10852 15 = 8 ∧ acceleratedOrbit 15 10852 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10852) = 3 ^ 8 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10852.1, data_15_10852.2]

/-- Complete interval computation for depth 15, residue 10853. -/
theorem bounds_15_10853 : exactInterval 15 10853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10853 : oddCount 10853 15 = 8 ∧ acceleratedOrbit 15 10853 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10853) = 3 ^ 8 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10853.1, data_15_10853.2]

/-- Complete interval computation for depth 15, residue 10854. -/
theorem bounds_15_10854 : exactInterval 15 10854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10854 : oddCount 10854 15 = 8 ∧ acceleratedOrbit 15 10854 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10854) = 3 ^ 8 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10854.1, data_15_10854.2]

/-- Complete interval computation for depth 15, residue 10855. -/
theorem bounds_15_10855 : exactInterval 15 10855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10855 : oddCount 10855 15 = 10 ∧ acceleratedOrbit 15 10855 = 19565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10855) = 3 ^ 10 * m + 19565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10855.1, data_15_10855.2]

/-- Complete interval computation for depth 15, residue 10856. -/
theorem bounds_15_10856 : exactInterval 15 10856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10856 : oddCount 10856 15 = 8 ∧ acceleratedOrbit 15 10856 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10856) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10856.1, data_15_10856.2]

/-- Complete interval computation for depth 15, residue 10857. -/
theorem bounds_15_10857 : exactInterval 15 10857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10857 : oddCount 10857 15 = 9 ∧ acceleratedOrbit 15 10857 = 6524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10857) = 3 ^ 9 * m + 6524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10857.1, data_15_10857.2]

/-- Complete interval computation for depth 15, residue 10858. -/
theorem bounds_15_10858 : exactInterval 15 10858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10858 : oddCount 10858 15 = 8 ∧ acceleratedOrbit 15 10858 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10858) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10858.1, data_15_10858.2]

/-- Complete interval computation for depth 15, residue 10859. -/
theorem bounds_15_10859 : exactInterval 15 10859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10859 : oddCount 10859 15 = 7 ∧ acceleratedOrbit 15 10859 = 725 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10859) = 3 ^ 7 * m + 725 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10859.1, data_15_10859.2]

/-- Complete interval computation for depth 15, residue 10860. -/
theorem bounds_15_10860 : exactInterval 15 10860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10860 : oddCount 10860 15 = 9 ∧ acceleratedOrbit 15 10860 = 6527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10860) = 3 ^ 9 * m + 6527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10860.1, data_15_10860.2]

/-- Complete interval computation for depth 15, residue 10861. -/
theorem bounds_15_10861 : exactInterval 15 10861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10861 : oddCount 10861 15 = 9 ∧ acceleratedOrbit 15 10861 = 6527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10861) = 3 ^ 9 * m + 6527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10861.1, data_15_10861.2]

/-- Complete interval computation for depth 15, residue 10862. -/
theorem bounds_15_10862 : exactInterval 15 10862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10862 : oddCount 10862 15 = 9 ∧ acceleratedOrbit 15 10862 = 6527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10862) = 3 ^ 9 * m + 6527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10862.1, data_15_10862.2]

/-- Complete interval computation for depth 15, residue 10863. -/
theorem bounds_15_10863 : exactInterval 15 10863 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10863) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10863 : oddCount 10863 15 = 9 ∧ acceleratedOrbit 15 10863 = 6526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10863) = 3 ^ 9 * m + 6526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10863.1, data_15_10863.2]

/-- Complete interval computation for depth 15, residue 10864. -/
theorem bounds_15_10864 : exactInterval 15 10864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10864 : oddCount 10864 15 = 8 ∧ acceleratedOrbit 15 10864 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10864) = 3 ^ 8 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10864.1, data_15_10864.2]

/-- Complete interval computation for depth 15, residue 10865. -/
theorem bounds_15_10865 : exactInterval 15 10865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10865 : oddCount 10865 15 = 8 ∧ acceleratedOrbit 15 10865 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10865) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10865.1, data_15_10865.2]

/-- Complete interval computation for depth 15, residue 10866. -/
theorem bounds_15_10866 : exactInterval 15 10866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10866 : oddCount 10866 15 = 10 ∧ acceleratedOrbit 15 10866 = 19592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10866) = 3 ^ 10 * m + 19592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10866.1, data_15_10866.2]

/-- Complete interval computation for depth 15, residue 10867. -/
theorem bounds_15_10867 : exactInterval 15 10867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10867 : oddCount 10867 15 = 10 ∧ acceleratedOrbit 15 10867 = 19592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10867) = 3 ^ 10 * m + 19592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10867.1, data_15_10867.2]

/-- Complete interval computation for depth 15, residue 10868. -/
theorem bounds_15_10868 : exactInterval 15 10868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10868 : oddCount 10868 15 = 8 ∧ acceleratedOrbit 15 10868 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10868) = 3 ^ 8 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10868.1, data_15_10868.2]

/-- Complete interval computation for depth 15, residue 10869. -/
theorem bounds_15_10869 : exactInterval 15 10869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10869 : oddCount 10869 15 = 8 ∧ acceleratedOrbit 15 10869 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10869) = 3 ^ 8 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10869.1, data_15_10869.2]

/-- Complete interval computation for depth 15, residue 10870. -/
theorem bounds_15_10870 : exactInterval 15 10870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10870 : oddCount 10870 15 = 7 ∧ acceleratedOrbit 15 10870 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10870) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10870.1, data_15_10870.2]

/-- Complete interval computation for depth 15, residue 10871. -/
theorem bounds_15_10871 : exactInterval 15 10871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10871 : oddCount 10871 15 = 7 ∧ acceleratedOrbit 15 10871 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10871) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10871.1, data_15_10871.2]

/-- Complete interval computation for depth 15, residue 10872. -/
theorem bounds_15_10872 : exactInterval 15 10872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10872 : oddCount 10872 15 = 8 ∧ acceleratedOrbit 15 10872 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10872) = 3 ^ 8 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10872.1, data_15_10872.2]

/-- Complete interval computation for depth 15, residue 10873. -/
theorem bounds_15_10873 : exactInterval 15 10873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10873 : oddCount 10873 15 = 10 ∧ acceleratedOrbit 15 10873 = 19601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10873) = 3 ^ 10 * m + 19601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10873.1, data_15_10873.2]

/-- Complete interval computation for depth 15, residue 10874. -/
theorem bounds_15_10874 : exactInterval 15 10874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10874 : oddCount 10874 15 = 8 ∧ acceleratedOrbit 15 10874 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10874) = 3 ^ 8 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10874.1, data_15_10874.2]

/-- Complete interval computation for depth 15, residue 10875. -/
theorem bounds_15_10875 : exactInterval 15 10875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10875 : oddCount 10875 15 = 6 ∧ acceleratedOrbit 15 10875 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10875) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10875.1, data_15_10875.2]

/-- Complete interval computation for depth 15, residue 10876. -/
theorem bounds_15_10876 : exactInterval 15 10876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10876 : oddCount 10876 15 = 9 ∧ acceleratedOrbit 15 10876 = 6536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10876) = 3 ^ 9 * m + 6536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10876.1, data_15_10876.2]

/-- Complete interval computation for depth 15, residue 10877. -/
theorem bounds_15_10877 : exactInterval 15 10877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10877 : oddCount 10877 15 = 9 ∧ acceleratedOrbit 15 10877 = 6536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10877) = 3 ^ 9 * m + 6536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10877.1, data_15_10877.2]

end Collatz.Research.PassageAtlas.Batch0332
