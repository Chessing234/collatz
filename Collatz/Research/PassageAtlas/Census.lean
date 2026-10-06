import Collatz.Research.StoppingAtlas.Census

namespace Collatz.Research.PassageAtlas
open PeriodicCounting Collatz.Research.StoppingAtlas
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem census_prefix_0 : countBelow (firstEventB 15) 0 = 0 := rfl

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_0 : countBelow (fun n => firstEventB 15 (0 + n)) 128 = 1 := by decide

theorem census_prefix_1 : countBelow (firstEventB 15) 128 = 1 := by
  have h := count_shift_add (firstEventB 15) 0 128
  rw [census_prefix_0, census_chunk_0] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_1 : countBelow (fun n => firstEventB 15 (128 + n)) 128 = 0 := by decide

theorem census_prefix_2 : countBelow (firstEventB 15) 256 = 1 := by
  have h := count_shift_add (firstEventB 15) 128 128
  rw [census_prefix_1, census_chunk_1] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_2 : countBelow (fun n => firstEventB 15 (256 + n)) 128 = 0 := by decide

theorem census_prefix_3 : countBelow (firstEventB 15) 384 = 1 := by
  have h := count_shift_add (firstEventB 15) 256 128
  rw [census_prefix_2, census_chunk_2] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_3 : countBelow (fun n => firstEventB 15 (384 + n)) 128 = 2 := by decide

theorem census_prefix_4 : countBelow (firstEventB 15) 512 = 3 := by
  have h := count_shift_add (firstEventB 15) 384 128
  rw [census_prefix_3, census_chunk_3] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_4 : countBelow (fun n => firstEventB 15 (512 + n)) 128 = 0 := by decide

theorem census_prefix_5 : countBelow (firstEventB 15) 640 = 3 := by
  have h := count_shift_add (firstEventB 15) 512 128
  rw [census_prefix_4, census_chunk_4] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_5 : countBelow (fun n => firstEventB 15 (640 + n)) 128 = 0 := by decide

theorem census_prefix_6 : countBelow (firstEventB 15) 768 = 3 := by
  have h := count_shift_add (firstEventB 15) 640 128
  rw [census_prefix_5, census_chunk_5] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_6 : countBelow (fun n => firstEventB 15 (768 + n)) 128 = 2 := by decide

theorem census_prefix_7 : countBelow (firstEventB 15) 896 = 5 := by
  have h := count_shift_add (firstEventB 15) 768 128
  rw [census_prefix_6, census_chunk_6] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_7 : countBelow (fun n => firstEventB 15 (896 + n)) 128 = 0 := by decide

theorem census_prefix_8 : countBelow (firstEventB 15) 1024 = 5 := by
  have h := count_shift_add (firstEventB 15) 896 128
  rw [census_prefix_7, census_chunk_7] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_8 : countBelow (fun n => firstEventB 15 (1024 + n)) 128 = 2 := by decide

theorem census_prefix_9 : countBelow (firstEventB 15) 1152 = 7 := by
  have h := count_shift_add (firstEventB 15) 1024 128
  rw [census_prefix_8, census_chunk_8] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_9 : countBelow (fun n => firstEventB 15 (1152 + n)) 128 = 1 := by decide

theorem census_prefix_10 : countBelow (firstEventB 15) 1280 = 8 := by
  have h := count_shift_add (firstEventB 15) 1152 128
  rw [census_prefix_9, census_chunk_9] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_10 : countBelow (fun n => firstEventB 15 (1280 + n)) 128 = 0 := by decide

theorem census_prefix_11 : countBelow (firstEventB 15) 1408 = 8 := by
  have h := count_shift_add (firstEventB 15) 1280 128
  rw [census_prefix_10, census_chunk_10] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_11 : countBelow (fun n => firstEventB 15 (1408 + n)) 128 = 0 := by decide

theorem census_prefix_12 : countBelow (firstEventB 15) 1536 = 8 := by
  have h := count_shift_add (firstEventB 15) 1408 128
  rw [census_prefix_11, census_chunk_11] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_12 : countBelow (fun n => firstEventB 15 (1536 + n)) 128 = 0 := by decide

theorem census_prefix_13 : countBelow (firstEventB 15) 1664 = 8 := by
  have h := count_shift_add (firstEventB 15) 1536 128
  rw [census_prefix_12, census_chunk_12] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_13 : countBelow (fun n => firstEventB 15 (1664 + n)) 128 = 1 := by decide

theorem census_prefix_14 : countBelow (firstEventB 15) 1792 = 9 := by
  have h := count_shift_add (firstEventB 15) 1664 128
  rw [census_prefix_13, census_chunk_13] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_14 : countBelow (fun n => firstEventB 15 (1792 + n)) 128 = 1 := by decide

theorem census_prefix_15 : countBelow (firstEventB 15) 1920 = 10 := by
  have h := count_shift_add (firstEventB 15) 1792 128
  rw [census_prefix_14, census_chunk_14] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_15 : countBelow (fun n => firstEventB 15 (1920 + n)) 128 = 0 := by decide

theorem census_prefix_16 : countBelow (firstEventB 15) 2048 = 10 := by
  have h := count_shift_add (firstEventB 15) 1920 128
  rw [census_prefix_15, census_chunk_15] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_16 : countBelow (fun n => firstEventB 15 (2048 + n)) 128 = 1 := by decide

theorem census_prefix_17 : countBelow (firstEventB 15) 2176 = 11 := by
  have h := count_shift_add (firstEventB 15) 2048 128
  rw [census_prefix_16, census_chunk_16] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_17 : countBelow (fun n => firstEventB 15 (2176 + n)) 128 = 3 := by decide

theorem census_prefix_18 : countBelow (firstEventB 15) 2304 = 14 := by
  have h := count_shift_add (firstEventB 15) 2176 128
  rw [census_prefix_17, census_chunk_17] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_18 : countBelow (fun n => firstEventB 15 (2304 + n)) 128 = 0 := by decide

theorem census_prefix_19 : countBelow (firstEventB 15) 2432 = 14 := by
  have h := count_shift_add (firstEventB 15) 2304 128
  rw [census_prefix_18, census_chunk_18] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_19 : countBelow (fun n => firstEventB 15 (2432 + n)) 128 = 0 := by decide

theorem census_prefix_20 : countBelow (firstEventB 15) 2560 = 14 := by
  have h := count_shift_add (firstEventB 15) 2432 128
  rw [census_prefix_19, census_chunk_19] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_20 : countBelow (fun n => firstEventB 15 (2560 + n)) 128 = 0 := by decide

theorem census_prefix_21 : countBelow (firstEventB 15) 2688 = 14 := by
  have h := count_shift_add (firstEventB 15) 2560 128
  rw [census_prefix_20, census_chunk_20] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_21 : countBelow (fun n => firstEventB 15 (2688 + n)) 128 = 4 := by decide

theorem census_prefix_22 : countBelow (firstEventB 15) 2816 = 18 := by
  have h := count_shift_add (firstEventB 15) 2688 128
  rw [census_prefix_21, census_chunk_21] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_22 : countBelow (fun n => firstEventB 15 (2816 + n)) 128 = 1 := by decide

theorem census_prefix_23 : countBelow (firstEventB 15) 2944 = 19 := by
  have h := count_shift_add (firstEventB 15) 2816 128
  rw [census_prefix_22, census_chunk_22] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_23 : countBelow (fun n => firstEventB 15 (2944 + n)) 128 = 1 := by decide

theorem census_prefix_24 : countBelow (firstEventB 15) 3072 = 20 := by
  have h := count_shift_add (firstEventB 15) 2944 128
  rw [census_prefix_23, census_chunk_23] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_24 : countBelow (fun n => firstEventB 15 (3072 + n)) 128 = 1 := by decide

theorem census_prefix_25 : countBelow (firstEventB 15) 3200 = 21 := by
  have h := count_shift_add (firstEventB 15) 3072 128
  rw [census_prefix_24, census_chunk_24] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_25 : countBelow (fun n => firstEventB 15 (3200 + n)) 128 = 1 := by decide

theorem census_prefix_26 : countBelow (firstEventB 15) 3328 = 22 := by
  have h := count_shift_add (firstEventB 15) 3200 128
  rw [census_prefix_25, census_chunk_25] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_26 : countBelow (fun n => firstEventB 15 (3328 + n)) 128 = 0 := by decide

theorem census_prefix_27 : countBelow (firstEventB 15) 3456 = 22 := by
  have h := count_shift_add (firstEventB 15) 3328 128
  rw [census_prefix_26, census_chunk_26] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_27 : countBelow (fun n => firstEventB 15 (3456 + n)) 128 = 0 := by decide

theorem census_prefix_28 : countBelow (firstEventB 15) 3584 = 22 := by
  have h := count_shift_add (firstEventB 15) 3456 128
  rw [census_prefix_27, census_chunk_27] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_28 : countBelow (fun n => firstEventB 15 (3584 + n)) 128 = 1 := by decide

theorem census_prefix_29 : countBelow (firstEventB 15) 3712 = 23 := by
  have h := count_shift_add (firstEventB 15) 3584 128
  rw [census_prefix_28, census_chunk_28] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_29 : countBelow (fun n => firstEventB 15 (3712 + n)) 128 = 1 := by decide

theorem census_prefix_30 : countBelow (firstEventB 15) 3840 = 24 := by
  have h := count_shift_add (firstEventB 15) 3712 128
  rw [census_prefix_29, census_chunk_29] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_30 : countBelow (fun n => firstEventB 15 (3840 + n)) 128 = 0 := by decide

theorem census_prefix_31 : countBelow (firstEventB 15) 3968 = 24 := by
  have h := count_shift_add (firstEventB 15) 3840 128
  rw [census_prefix_30, census_chunk_30] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_31 : countBelow (fun n => firstEventB 15 (3968 + n)) 128 = 2 := by decide

theorem census_prefix_32 : countBelow (firstEventB 15) 4096 = 26 := by
  have h := count_shift_add (firstEventB 15) 3968 128
  rw [census_prefix_31, census_chunk_31] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_32 : countBelow (fun n => firstEventB 15 (4096 + n)) 128 = 1 := by decide

theorem census_prefix_33 : countBelow (firstEventB 15) 4224 = 27 := by
  have h := count_shift_add (firstEventB 15) 4096 128
  rw [census_prefix_32, census_chunk_32] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_33 : countBelow (fun n => firstEventB 15 (4224 + n)) 128 = 1 := by decide

theorem census_prefix_34 : countBelow (firstEventB 15) 4352 = 28 := by
  have h := count_shift_add (firstEventB 15) 4224 128
  rw [census_prefix_33, census_chunk_33] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_34 : countBelow (fun n => firstEventB 15 (4352 + n)) 128 = 0 := by decide

theorem census_prefix_35 : countBelow (firstEventB 15) 4480 = 28 := by
  have h := count_shift_add (firstEventB 15) 4352 128
  rw [census_prefix_34, census_chunk_34] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_35 : countBelow (fun n => firstEventB 15 (4480 + n)) 128 = 0 := by decide

theorem census_prefix_36 : countBelow (firstEventB 15) 4608 = 28 := by
  have h := count_shift_add (firstEventB 15) 4480 128
  rw [census_prefix_35, census_chunk_35] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_36 : countBelow (fun n => firstEventB 15 (4608 + n)) 128 = 1 := by decide

theorem census_prefix_37 : countBelow (firstEventB 15) 4736 = 29 := by
  have h := count_shift_add (firstEventB 15) 4608 128
  rw [census_prefix_36, census_chunk_36] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_37 : countBelow (fun n => firstEventB 15 (4736 + n)) 128 = 0 := by decide

theorem census_prefix_38 : countBelow (firstEventB 15) 4864 = 29 := by
  have h := count_shift_add (firstEventB 15) 4736 128
  rw [census_prefix_37, census_chunk_37] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_38 : countBelow (fun n => firstEventB 15 (4864 + n)) 128 = 0 := by decide

theorem census_prefix_39 : countBelow (firstEventB 15) 4992 = 29 := by
  have h := count_shift_add (firstEventB 15) 4864 128
  rw [census_prefix_38, census_chunk_38] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_39 : countBelow (fun n => firstEventB 15 (4992 + n)) 128 = 0 := by decide

theorem census_prefix_40 : countBelow (firstEventB 15) 5120 = 29 := by
  have h := count_shift_add (firstEventB 15) 4992 128
  rw [census_prefix_39, census_chunk_39] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_40 : countBelow (fun n => firstEventB 15 (5120 + n)) 128 = 1 := by decide

theorem census_prefix_41 : countBelow (firstEventB 15) 5248 = 30 := by
  have h := count_shift_add (firstEventB 15) 5120 128
  rw [census_prefix_40, census_chunk_40] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_41 : countBelow (fun n => firstEventB 15 (5248 + n)) 128 = 1 := by decide

theorem census_prefix_42 : countBelow (firstEventB 15) 5376 = 31 := by
  have h := count_shift_add (firstEventB 15) 5248 128
  rw [census_prefix_41, census_chunk_41] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_42 : countBelow (fun n => firstEventB 15 (5376 + n)) 128 = 0 := by decide

theorem census_prefix_43 : countBelow (firstEventB 15) 5504 = 31 := by
  have h := count_shift_add (firstEventB 15) 5376 128
  rw [census_prefix_42, census_chunk_42] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_43 : countBelow (fun n => firstEventB 15 (5504 + n)) 128 = 2 := by decide

theorem census_prefix_44 : countBelow (firstEventB 15) 5632 = 33 := by
  have h := count_shift_add (firstEventB 15) 5504 128
  rw [census_prefix_43, census_chunk_43] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_44 : countBelow (fun n => firstEventB 15 (5632 + n)) 128 = 0 := by decide

theorem census_prefix_45 : countBelow (firstEventB 15) 5760 = 33 := by
  have h := count_shift_add (firstEventB 15) 5632 128
  rw [census_prefix_44, census_chunk_44] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_45 : countBelow (fun n => firstEventB 15 (5760 + n)) 128 = 0 := by decide

theorem census_prefix_46 : countBelow (firstEventB 15) 5888 = 33 := by
  have h := count_shift_add (firstEventB 15) 5760 128
  rw [census_prefix_45, census_chunk_45] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_46 : countBelow (fun n => firstEventB 15 (5888 + n)) 128 = 0 := by decide

theorem census_prefix_47 : countBelow (firstEventB 15) 6016 = 33 := by
  have h := count_shift_add (firstEventB 15) 5888 128
  rw [census_prefix_46, census_chunk_46] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_47 : countBelow (fun n => firstEventB 15 (6016 + n)) 128 = 0 := by decide

theorem census_prefix_48 : countBelow (firstEventB 15) 6144 = 33 := by
  have h := count_shift_add (firstEventB 15) 6016 128
  rw [census_prefix_47, census_chunk_47] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_48 : countBelow (fun n => firstEventB 15 (6144 + n)) 128 = 2 := by decide

theorem census_prefix_49 : countBelow (firstEventB 15) 6272 = 35 := by
  have h := count_shift_add (firstEventB 15) 6144 128
  rw [census_prefix_48, census_chunk_48] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_49 : countBelow (fun n => firstEventB 15 (6272 + n)) 128 = 0 := by decide

theorem census_prefix_50 : countBelow (firstEventB 15) 6400 = 35 := by
  have h := count_shift_add (firstEventB 15) 6272 128
  rw [census_prefix_49, census_chunk_49] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_50 : countBelow (fun n => firstEventB 15 (6400 + n)) 128 = 1 := by decide

theorem census_prefix_51 : countBelow (firstEventB 15) 6528 = 36 := by
  have h := count_shift_add (firstEventB 15) 6400 128
  rw [census_prefix_50, census_chunk_50] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_51 : countBelow (fun n => firstEventB 15 (6528 + n)) 128 = 0 := by decide

theorem census_prefix_52 : countBelow (firstEventB 15) 6656 = 36 := by
  have h := count_shift_add (firstEventB 15) 6528 128
  rw [census_prefix_51, census_chunk_51] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_52 : countBelow (fun n => firstEventB 15 (6656 + n)) 128 = 2 := by decide

theorem census_prefix_53 : countBelow (firstEventB 15) 6784 = 38 := by
  have h := count_shift_add (firstEventB 15) 6656 128
  rw [census_prefix_52, census_chunk_52] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_53 : countBelow (fun n => firstEventB 15 (6784 + n)) 128 = 1 := by decide

theorem census_prefix_54 : countBelow (firstEventB 15) 6912 = 39 := by
  have h := count_shift_add (firstEventB 15) 6784 128
  rw [census_prefix_53, census_chunk_53] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_54 : countBelow (fun n => firstEventB 15 (6912 + n)) 128 = 0 := by decide

theorem census_prefix_55 : countBelow (firstEventB 15) 7040 = 39 := by
  have h := count_shift_add (firstEventB 15) 6912 128
  rw [census_prefix_54, census_chunk_54] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_55 : countBelow (fun n => firstEventB 15 (7040 + n)) 128 = 1 := by decide

theorem census_prefix_56 : countBelow (firstEventB 15) 7168 = 40 := by
  have h := count_shift_add (firstEventB 15) 7040 128
  rw [census_prefix_55, census_chunk_55] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_56 : countBelow (fun n => firstEventB 15 (7168 + n)) 128 = 1 := by decide

theorem census_prefix_57 : countBelow (firstEventB 15) 7296 = 41 := by
  have h := count_shift_add (firstEventB 15) 7168 128
  rw [census_prefix_56, census_chunk_56] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_57 : countBelow (fun n => firstEventB 15 (7296 + n)) 128 = 0 := by decide

theorem census_prefix_58 : countBelow (firstEventB 15) 7424 = 41 := by
  have h := count_shift_add (firstEventB 15) 7296 128
  rw [census_prefix_57, census_chunk_57] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_58 : countBelow (fun n => firstEventB 15 (7424 + n)) 128 = 1 := by decide

theorem census_prefix_59 : countBelow (firstEventB 15) 7552 = 42 := by
  have h := count_shift_add (firstEventB 15) 7424 128
  rw [census_prefix_58, census_chunk_58] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_59 : countBelow (fun n => firstEventB 15 (7552 + n)) 128 = 0 := by decide

theorem census_prefix_60 : countBelow (firstEventB 15) 7680 = 42 := by
  have h := count_shift_add (firstEventB 15) 7552 128
  rw [census_prefix_59, census_chunk_59] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_60 : countBelow (fun n => firstEventB 15 (7680 + n)) 128 = 1 := by decide

theorem census_prefix_61 : countBelow (firstEventB 15) 7808 = 43 := by
  have h := count_shift_add (firstEventB 15) 7680 128
  rw [census_prefix_60, census_chunk_60] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_61 : countBelow (fun n => firstEventB 15 (7808 + n)) 128 = 0 := by decide

theorem census_prefix_62 : countBelow (firstEventB 15) 7936 = 43 := by
  have h := count_shift_add (firstEventB 15) 7808 128
  rw [census_prefix_61, census_chunk_61] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_62 : countBelow (fun n => firstEventB 15 (7936 + n)) 128 = 1 := by decide

theorem census_prefix_63 : countBelow (firstEventB 15) 8064 = 44 := by
  have h := count_shift_add (firstEventB 15) 7936 128
  rw [census_prefix_62, census_chunk_62] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_63 : countBelow (fun n => firstEventB 15 (8064 + n)) 128 = 1 := by decide

theorem census_prefix_64 : countBelow (firstEventB 15) 8192 = 45 := by
  have h := count_shift_add (firstEventB 15) 8064 128
  rw [census_prefix_63, census_chunk_63] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_64 : countBelow (fun n => firstEventB 15 (8192 + n)) 128 = 0 := by decide

theorem census_prefix_65 : countBelow (firstEventB 15) 8320 = 45 := by
  have h := count_shift_add (firstEventB 15) 8192 128
  rw [census_prefix_64, census_chunk_64] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_65 : countBelow (fun n => firstEventB 15 (8320 + n)) 128 = 2 := by decide

theorem census_prefix_66 : countBelow (firstEventB 15) 8448 = 47 := by
  have h := count_shift_add (firstEventB 15) 8320 128
  rw [census_prefix_65, census_chunk_65] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_66 : countBelow (fun n => firstEventB 15 (8448 + n)) 128 = 0 := by decide

theorem census_prefix_67 : countBelow (firstEventB 15) 8576 = 47 := by
  have h := count_shift_add (firstEventB 15) 8448 128
  rw [census_prefix_66, census_chunk_66] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_67 : countBelow (fun n => firstEventB 15 (8576 + n)) 128 = 0 := by decide

theorem census_prefix_68 : countBelow (firstEventB 15) 8704 = 47 := by
  have h := count_shift_add (firstEventB 15) 8576 128
  rw [census_prefix_67, census_chunk_67] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_68 : countBelow (fun n => firstEventB 15 (8704 + n)) 128 = 1 := by decide

theorem census_prefix_69 : countBelow (firstEventB 15) 8832 = 48 := by
  have h := count_shift_add (firstEventB 15) 8704 128
  rw [census_prefix_68, census_chunk_68] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_69 : countBelow (fun n => firstEventB 15 (8832 + n)) 128 = 0 := by decide

theorem census_prefix_70 : countBelow (firstEventB 15) 8960 = 48 := by
  have h := count_shift_add (firstEventB 15) 8832 128
  rw [census_prefix_69, census_chunk_69] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_70 : countBelow (fun n => firstEventB 15 (8960 + n)) 128 = 2 := by decide

theorem census_prefix_71 : countBelow (firstEventB 15) 9088 = 50 := by
  have h := count_shift_add (firstEventB 15) 8960 128
  rw [census_prefix_70, census_chunk_70] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_71 : countBelow (fun n => firstEventB 15 (9088 + n)) 128 = 0 := by decide

theorem census_prefix_72 : countBelow (firstEventB 15) 9216 = 50 := by
  have h := count_shift_add (firstEventB 15) 9088 128
  rw [census_prefix_71, census_chunk_71] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_72 : countBelow (fun n => firstEventB 15 (9216 + n)) 128 = 0 := by decide

theorem census_prefix_73 : countBelow (firstEventB 15) 9344 = 50 := by
  have h := count_shift_add (firstEventB 15) 9216 128
  rw [census_prefix_72, census_chunk_72] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_73 : countBelow (fun n => firstEventB 15 (9344 + n)) 128 = 2 := by decide

theorem census_prefix_74 : countBelow (firstEventB 15) 9472 = 52 := by
  have h := count_shift_add (firstEventB 15) 9344 128
  rw [census_prefix_73, census_chunk_73] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_74 : countBelow (fun n => firstEventB 15 (9472 + n)) 128 = 0 := by decide

theorem census_prefix_75 : countBelow (firstEventB 15) 9600 = 52 := by
  have h := count_shift_add (firstEventB 15) 9472 128
  rw [census_prefix_74, census_chunk_74] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_75 : countBelow (fun n => firstEventB 15 (9600 + n)) 128 = 2 := by decide

theorem census_prefix_76 : countBelow (firstEventB 15) 9728 = 54 := by
  have h := count_shift_add (firstEventB 15) 9600 128
  rw [census_prefix_75, census_chunk_75] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_76 : countBelow (fun n => firstEventB 15 (9728 + n)) 128 = 0 := by decide

theorem census_prefix_77 : countBelow (firstEventB 15) 9856 = 54 := by
  have h := count_shift_add (firstEventB 15) 9728 128
  rw [census_prefix_76, census_chunk_76] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_77 : countBelow (fun n => firstEventB 15 (9856 + n)) 128 = 1 := by decide

theorem census_prefix_78 : countBelow (firstEventB 15) 9984 = 55 := by
  have h := count_shift_add (firstEventB 15) 9856 128
  rw [census_prefix_77, census_chunk_77] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_78 : countBelow (fun n => firstEventB 15 (9984 + n)) 128 = 2 := by decide

theorem census_prefix_79 : countBelow (firstEventB 15) 10112 = 57 := by
  have h := count_shift_add (firstEventB 15) 9984 128
  rw [census_prefix_78, census_chunk_78] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_79 : countBelow (fun n => firstEventB 15 (10112 + n)) 128 = 0 := by decide

theorem census_prefix_80 : countBelow (firstEventB 15) 10240 = 57 := by
  have h := count_shift_add (firstEventB 15) 10112 128
  rw [census_prefix_79, census_chunk_79] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_80 : countBelow (fun n => firstEventB 15 (10240 + n)) 128 = 0 := by decide

theorem census_prefix_81 : countBelow (firstEventB 15) 10368 = 57 := by
  have h := count_shift_add (firstEventB 15) 10240 128
  rw [census_prefix_80, census_chunk_80] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_81 : countBelow (fun n => firstEventB 15 (10368 + n)) 128 = 0 := by decide

theorem census_prefix_82 : countBelow (firstEventB 15) 10496 = 57 := by
  have h := count_shift_add (firstEventB 15) 10368 128
  rw [census_prefix_81, census_chunk_81] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_82 : countBelow (fun n => firstEventB 15 (10496 + n)) 128 = 0 := by decide

theorem census_prefix_83 : countBelow (firstEventB 15) 10624 = 57 := by
  have h := count_shift_add (firstEventB 15) 10496 128
  rw [census_prefix_82, census_chunk_82] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_83 : countBelow (fun n => firstEventB 15 (10624 + n)) 128 = 2 := by decide

theorem census_prefix_84 : countBelow (firstEventB 15) 10752 = 59 := by
  have h := count_shift_add (firstEventB 15) 10624 128
  rw [census_prefix_83, census_chunk_83] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_84 : countBelow (fun n => firstEventB 15 (10752 + n)) 128 = 1 := by decide

theorem census_prefix_85 : countBelow (firstEventB 15) 10880 = 60 := by
  have h := count_shift_add (firstEventB 15) 10752 128
  rw [census_prefix_84, census_chunk_84] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_85 : countBelow (fun n => firstEventB 15 (10880 + n)) 128 = 0 := by decide

theorem census_prefix_86 : countBelow (firstEventB 15) 11008 = 60 := by
  have h := count_shift_add (firstEventB 15) 10880 128
  rw [census_prefix_85, census_chunk_85] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_86 : countBelow (fun n => firstEventB 15 (11008 + n)) 128 = 2 := by decide

theorem census_prefix_87 : countBelow (firstEventB 15) 11136 = 62 := by
  have h := count_shift_add (firstEventB 15) 11008 128
  rw [census_prefix_86, census_chunk_86] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_87 : countBelow (fun n => firstEventB 15 (11136 + n)) 128 = 0 := by decide

theorem census_prefix_88 : countBelow (firstEventB 15) 11264 = 62 := by
  have h := count_shift_add (firstEventB 15) 11136 128
  rw [census_prefix_87, census_chunk_87] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_88 : countBelow (fun n => firstEventB 15 (11264 + n)) 128 = 0 := by decide

theorem census_prefix_89 : countBelow (firstEventB 15) 11392 = 62 := by
  have h := count_shift_add (firstEventB 15) 11264 128
  rw [census_prefix_88, census_chunk_88] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_89 : countBelow (fun n => firstEventB 15 (11392 + n)) 128 = 0 := by decide

theorem census_prefix_90 : countBelow (firstEventB 15) 11520 = 62 := by
  have h := count_shift_add (firstEventB 15) 11392 128
  rw [census_prefix_89, census_chunk_89] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_90 : countBelow (fun n => firstEventB 15 (11520 + n)) 128 = 1 := by decide

theorem census_prefix_91 : countBelow (firstEventB 15) 11648 = 63 := by
  have h := count_shift_add (firstEventB 15) 11520 128
  rw [census_prefix_90, census_chunk_90] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_91 : countBelow (fun n => firstEventB 15 (11648 + n)) 128 = 1 := by decide

theorem census_prefix_92 : countBelow (firstEventB 15) 11776 = 64 := by
  have h := count_shift_add (firstEventB 15) 11648 128
  rw [census_prefix_91, census_chunk_91] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_92 : countBelow (fun n => firstEventB 15 (11776 + n)) 128 = 1 := by decide

theorem census_prefix_93 : countBelow (firstEventB 15) 11904 = 65 := by
  have h := count_shift_add (firstEventB 15) 11776 128
  rw [census_prefix_92, census_chunk_92] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_93 : countBelow (fun n => firstEventB 15 (11904 + n)) 128 = 2 := by decide

theorem census_prefix_94 : countBelow (firstEventB 15) 12032 = 67 := by
  have h := count_shift_add (firstEventB 15) 11904 128
  rw [census_prefix_93, census_chunk_93] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_94 : countBelow (fun n => firstEventB 15 (12032 + n)) 128 = 2 := by decide

theorem census_prefix_95 : countBelow (firstEventB 15) 12160 = 69 := by
  have h := count_shift_add (firstEventB 15) 12032 128
  rw [census_prefix_94, census_chunk_94] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_95 : countBelow (fun n => firstEventB 15 (12160 + n)) 128 = 0 := by decide

theorem census_prefix_96 : countBelow (firstEventB 15) 12288 = 69 := by
  have h := count_shift_add (firstEventB 15) 12160 128
  rw [census_prefix_95, census_chunk_95] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_96 : countBelow (fun n => firstEventB 15 (12288 + n)) 128 = 0 := by decide

theorem census_prefix_97 : countBelow (firstEventB 15) 12416 = 69 := by
  have h := count_shift_add (firstEventB 15) 12288 128
  rw [census_prefix_96, census_chunk_96] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_97 : countBelow (fun n => firstEventB 15 (12416 + n)) 128 = 2 := by decide

theorem census_prefix_98 : countBelow (firstEventB 15) 12544 = 71 := by
  have h := count_shift_add (firstEventB 15) 12416 128
  rw [census_prefix_97, census_chunk_97] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_98 : countBelow (fun n => firstEventB 15 (12544 + n)) 128 = 1 := by decide

theorem census_prefix_99 : countBelow (firstEventB 15) 12672 = 72 := by
  have h := count_shift_add (firstEventB 15) 12544 128
  rw [census_prefix_98, census_chunk_98] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_99 : countBelow (fun n => firstEventB 15 (12672 + n)) 128 = 0 := by decide

theorem census_prefix_100 : countBelow (firstEventB 15) 12800 = 72 := by
  have h := count_shift_add (firstEventB 15) 12672 128
  rw [census_prefix_99, census_chunk_99] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_100 : countBelow (fun n => firstEventB 15 (12800 + n)) 128 = 1 := by decide

theorem census_prefix_101 : countBelow (firstEventB 15) 12928 = 73 := by
  have h := count_shift_add (firstEventB 15) 12800 128
  rw [census_prefix_100, census_chunk_100] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_101 : countBelow (fun n => firstEventB 15 (12928 + n)) 128 = 2 := by decide

theorem census_prefix_102 : countBelow (firstEventB 15) 13056 = 75 := by
  have h := count_shift_add (firstEventB 15) 12928 128
  rw [census_prefix_101, census_chunk_101] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_102 : countBelow (fun n => firstEventB 15 (13056 + n)) 128 = 1 := by decide

theorem census_prefix_103 : countBelow (firstEventB 15) 13184 = 76 := by
  have h := count_shift_add (firstEventB 15) 13056 128
  rw [census_prefix_102, census_chunk_102] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_103 : countBelow (fun n => firstEventB 15 (13184 + n)) 128 = 0 := by decide

theorem census_prefix_104 : countBelow (firstEventB 15) 13312 = 76 := by
  have h := count_shift_add (firstEventB 15) 13184 128
  rw [census_prefix_103, census_chunk_103] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_104 : countBelow (fun n => firstEventB 15 (13312 + n)) 128 = 0 := by decide

theorem census_prefix_105 : countBelow (firstEventB 15) 13440 = 76 := by
  have h := count_shift_add (firstEventB 15) 13312 128
  rw [census_prefix_104, census_chunk_104] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_105 : countBelow (fun n => firstEventB 15 (13440 + n)) 128 = 1 := by decide

theorem census_prefix_106 : countBelow (firstEventB 15) 13568 = 77 := by
  have h := count_shift_add (firstEventB 15) 13440 128
  rw [census_prefix_105, census_chunk_105] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_106 : countBelow (fun n => firstEventB 15 (13568 + n)) 128 = 1 := by decide

theorem census_prefix_107 : countBelow (firstEventB 15) 13696 = 78 := by
  have h := count_shift_add (firstEventB 15) 13568 128
  rw [census_prefix_106, census_chunk_106] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_107 : countBelow (fun n => firstEventB 15 (13696 + n)) 128 = 0 := by decide

theorem census_prefix_108 : countBelow (firstEventB 15) 13824 = 78 := by
  have h := count_shift_add (firstEventB 15) 13696 128
  rw [census_prefix_107, census_chunk_107] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_108 : countBelow (fun n => firstEventB 15 (13824 + n)) 128 = 1 := by decide

theorem census_prefix_109 : countBelow (firstEventB 15) 13952 = 79 := by
  have h := count_shift_add (firstEventB 15) 13824 128
  rw [census_prefix_108, census_chunk_108] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_109 : countBelow (fun n => firstEventB 15 (13952 + n)) 128 = 1 := by decide

theorem census_prefix_110 : countBelow (firstEventB 15) 14080 = 80 := by
  have h := count_shift_add (firstEventB 15) 13952 128
  rw [census_prefix_109, census_chunk_109] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_110 : countBelow (fun n => firstEventB 15 (14080 + n)) 128 = 0 := by decide

theorem census_prefix_111 : countBelow (firstEventB 15) 14208 = 80 := by
  have h := count_shift_add (firstEventB 15) 14080 128
  rw [census_prefix_110, census_chunk_110] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_111 : countBelow (fun n => firstEventB 15 (14208 + n)) 128 = 1 := by decide

theorem census_prefix_112 : countBelow (firstEventB 15) 14336 = 81 := by
  have h := count_shift_add (firstEventB 15) 14208 128
  rw [census_prefix_111, census_chunk_111] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_112 : countBelow (fun n => firstEventB 15 (14336 + n)) 128 = 2 := by decide

theorem census_prefix_113 : countBelow (firstEventB 15) 14464 = 83 := by
  have h := count_shift_add (firstEventB 15) 14336 128
  rw [census_prefix_112, census_chunk_112] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_113 : countBelow (fun n => firstEventB 15 (14464 + n)) 128 = 0 := by decide

theorem census_prefix_114 : countBelow (firstEventB 15) 14592 = 83 := by
  have h := count_shift_add (firstEventB 15) 14464 128
  rw [census_prefix_113, census_chunk_113] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_114 : countBelow (fun n => firstEventB 15 (14592 + n)) 128 = 0 := by decide

theorem census_prefix_115 : countBelow (firstEventB 15) 14720 = 83 := by
  have h := count_shift_add (firstEventB 15) 14592 128
  rw [census_prefix_114, census_chunk_114] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_115 : countBelow (fun n => firstEventB 15 (14720 + n)) 128 = 0 := by decide

theorem census_prefix_116 : countBelow (firstEventB 15) 14848 = 83 := by
  have h := count_shift_add (firstEventB 15) 14720 128
  rw [census_prefix_115, census_chunk_115] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_116 : countBelow (fun n => firstEventB 15 (14848 + n)) 128 = 1 := by decide

theorem census_prefix_117 : countBelow (firstEventB 15) 14976 = 84 := by
  have h := count_shift_add (firstEventB 15) 14848 128
  rw [census_prefix_116, census_chunk_116] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_117 : countBelow (fun n => firstEventB 15 (14976 + n)) 128 = 0 := by decide

theorem census_prefix_118 : countBelow (firstEventB 15) 15104 = 84 := by
  have h := count_shift_add (firstEventB 15) 14976 128
  rw [census_prefix_117, census_chunk_117] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_118 : countBelow (fun n => firstEventB 15 (15104 + n)) 128 = 0 := by decide

theorem census_prefix_119 : countBelow (firstEventB 15) 15232 = 84 := by
  have h := count_shift_add (firstEventB 15) 15104 128
  rw [census_prefix_118, census_chunk_118] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_119 : countBelow (fun n => firstEventB 15 (15232 + n)) 128 = 2 := by decide

theorem census_prefix_120 : countBelow (firstEventB 15) 15360 = 86 := by
  have h := count_shift_add (firstEventB 15) 15232 128
  rw [census_prefix_119, census_chunk_119] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_120 : countBelow (fun n => firstEventB 15 (15360 + n)) 128 = 0 := by decide

theorem census_prefix_121 : countBelow (firstEventB 15) 15488 = 86 := by
  have h := count_shift_add (firstEventB 15) 15360 128
  rw [census_prefix_120, census_chunk_120] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_121 : countBelow (fun n => firstEventB 15 (15488 + n)) 128 = 0 := by decide

theorem census_prefix_122 : countBelow (firstEventB 15) 15616 = 86 := by
  have h := count_shift_add (firstEventB 15) 15488 128
  rw [census_prefix_121, census_chunk_121] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_122 : countBelow (fun n => firstEventB 15 (15616 + n)) 128 = 0 := by decide

theorem census_prefix_123 : countBelow (firstEventB 15) 15744 = 86 := by
  have h := count_shift_add (firstEventB 15) 15616 128
  rw [census_prefix_122, census_chunk_122] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_123 : countBelow (fun n => firstEventB 15 (15744 + n)) 128 = 1 := by decide

theorem census_prefix_124 : countBelow (firstEventB 15) 15872 = 87 := by
  have h := count_shift_add (firstEventB 15) 15744 128
  rw [census_prefix_123, census_chunk_123] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_124 : countBelow (fun n => firstEventB 15 (15872 + n)) 128 = 1 := by decide

theorem census_prefix_125 : countBelow (firstEventB 15) 16000 = 88 := by
  have h := count_shift_add (firstEventB 15) 15872 128
  rw [census_prefix_124, census_chunk_124] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_125 : countBelow (fun n => firstEventB 15 (16000 + n)) 128 = 2 := by decide

theorem census_prefix_126 : countBelow (firstEventB 15) 16128 = 90 := by
  have h := count_shift_add (firstEventB 15) 16000 128
  rw [census_prefix_125, census_chunk_125] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_126 : countBelow (fun n => firstEventB 15 (16128 + n)) 128 = 0 := by decide

theorem census_prefix_127 : countBelow (firstEventB 15) 16256 = 90 := by
  have h := count_shift_add (firstEventB 15) 16128 128
  rw [census_prefix_126, census_chunk_126] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_127 : countBelow (fun n => firstEventB 15 (16256 + n)) 128 = 1 := by decide

theorem census_prefix_128 : countBelow (firstEventB 15) 16384 = 91 := by
  have h := count_shift_add (firstEventB 15) 16256 128
  rw [census_prefix_127, census_chunk_127] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_128 : countBelow (fun n => firstEventB 15 (16384 + n)) 128 = 0 := by decide

theorem census_prefix_129 : countBelow (firstEventB 15) 16512 = 91 := by
  have h := count_shift_add (firstEventB 15) 16384 128
  rw [census_prefix_128, census_chunk_128] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_129 : countBelow (fun n => firstEventB 15 (16512 + n)) 128 = 0 := by decide

theorem census_prefix_130 : countBelow (firstEventB 15) 16640 = 91 := by
  have h := count_shift_add (firstEventB 15) 16512 128
  rw [census_prefix_129, census_chunk_129] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_130 : countBelow (fun n => firstEventB 15 (16640 + n)) 128 = 1 := by decide

theorem census_prefix_131 : countBelow (firstEventB 15) 16768 = 92 := by
  have h := count_shift_add (firstEventB 15) 16640 128
  rw [census_prefix_130, census_chunk_130] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_131 : countBelow (fun n => firstEventB 15 (16768 + n)) 128 = 2 := by decide

theorem census_prefix_132 : countBelow (firstEventB 15) 16896 = 94 := by
  have h := count_shift_add (firstEventB 15) 16768 128
  rw [census_prefix_131, census_chunk_131] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_132 : countBelow (fun n => firstEventB 15 (16896 + n)) 128 = 0 := by decide

theorem census_prefix_133 : countBelow (firstEventB 15) 17024 = 94 := by
  have h := count_shift_add (firstEventB 15) 16896 128
  rw [census_prefix_132, census_chunk_132] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_133 : countBelow (fun n => firstEventB 15 (17024 + n)) 128 = 1 := by decide

theorem census_prefix_134 : countBelow (firstEventB 15) 17152 = 95 := by
  have h := count_shift_add (firstEventB 15) 17024 128
  rw [census_prefix_133, census_chunk_133] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_134 : countBelow (fun n => firstEventB 15 (17152 + n)) 128 = 0 := by decide

theorem census_prefix_135 : countBelow (firstEventB 15) 17280 = 95 := by
  have h := count_shift_add (firstEventB 15) 17152 128
  rw [census_prefix_134, census_chunk_134] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_135 : countBelow (fun n => firstEventB 15 (17280 + n)) 128 = 0 := by decide

theorem census_prefix_136 : countBelow (firstEventB 15) 17408 = 95 := by
  have h := count_shift_add (firstEventB 15) 17280 128
  rw [census_prefix_135, census_chunk_135] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_136 : countBelow (fun n => firstEventB 15 (17408 + n)) 128 = 0 := by decide

theorem census_prefix_137 : countBelow (firstEventB 15) 17536 = 95 := by
  have h := count_shift_add (firstEventB 15) 17408 128
  rw [census_prefix_136, census_chunk_136] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_137 : countBelow (fun n => firstEventB 15 (17536 + n)) 128 = 0 := by decide

theorem census_prefix_138 : countBelow (firstEventB 15) 17664 = 95 := by
  have h := count_shift_add (firstEventB 15) 17536 128
  rw [census_prefix_137, census_chunk_137] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_138 : countBelow (fun n => firstEventB 15 (17664 + n)) 128 = 3 := by decide

theorem census_prefix_139 : countBelow (firstEventB 15) 17792 = 98 := by
  have h := count_shift_add (firstEventB 15) 17664 128
  rw [census_prefix_138, census_chunk_138] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_139 : countBelow (fun n => firstEventB 15 (17792 + n)) 128 = 0 := by decide

theorem census_prefix_140 : countBelow (firstEventB 15) 17920 = 98 := by
  have h := count_shift_add (firstEventB 15) 17792 128
  rw [census_prefix_139, census_chunk_139] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_140 : countBelow (fun n => firstEventB 15 (17920 + n)) 128 = 1 := by decide

theorem census_prefix_141 : countBelow (firstEventB 15) 18048 = 99 := by
  have h := count_shift_add (firstEventB 15) 17920 128
  rw [census_prefix_140, census_chunk_140] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_141 : countBelow (fun n => firstEventB 15 (18048 + n)) 128 = 0 := by decide

theorem census_prefix_142 : countBelow (firstEventB 15) 18176 = 99 := by
  have h := count_shift_add (firstEventB 15) 18048 128
  rw [census_prefix_141, census_chunk_141] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_142 : countBelow (fun n => firstEventB 15 (18176 + n)) 128 = 0 := by decide

theorem census_prefix_143 : countBelow (firstEventB 15) 18304 = 99 := by
  have h := count_shift_add (firstEventB 15) 18176 128
  rw [census_prefix_142, census_chunk_142] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_143 : countBelow (fun n => firstEventB 15 (18304 + n)) 128 = 0 := by decide

theorem census_prefix_144 : countBelow (firstEventB 15) 18432 = 99 := by
  have h := count_shift_add (firstEventB 15) 18304 128
  rw [census_prefix_143, census_chunk_143] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_144 : countBelow (fun n => firstEventB 15 (18432 + n)) 128 = 0 := by decide

theorem census_prefix_145 : countBelow (firstEventB 15) 18560 = 99 := by
  have h := count_shift_add (firstEventB 15) 18432 128
  rw [census_prefix_144, census_chunk_144] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_145 : countBelow (fun n => firstEventB 15 (18560 + n)) 128 = 1 := by decide

theorem census_prefix_146 : countBelow (firstEventB 15) 18688 = 100 := by
  have h := count_shift_add (firstEventB 15) 18560 128
  rw [census_prefix_145, census_chunk_145] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_146 : countBelow (fun n => firstEventB 15 (18688 + n)) 128 = 1 := by decide

theorem census_prefix_147 : countBelow (firstEventB 15) 18816 = 101 := by
  have h := count_shift_add (firstEventB 15) 18688 128
  rw [census_prefix_146, census_chunk_146] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_147 : countBelow (fun n => firstEventB 15 (18816 + n)) 128 = 1 := by decide

theorem census_prefix_148 : countBelow (firstEventB 15) 18944 = 102 := by
  have h := count_shift_add (firstEventB 15) 18816 128
  rw [census_prefix_147, census_chunk_147] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_148 : countBelow (fun n => firstEventB 15 (18944 + n)) 128 = 1 := by decide

theorem census_prefix_149 : countBelow (firstEventB 15) 19072 = 103 := by
  have h := count_shift_add (firstEventB 15) 18944 128
  rw [census_prefix_148, census_chunk_148] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_149 : countBelow (fun n => firstEventB 15 (19072 + n)) 128 = 1 := by decide

theorem census_prefix_150 : countBelow (firstEventB 15) 19200 = 104 := by
  have h := count_shift_add (firstEventB 15) 19072 128
  rw [census_prefix_149, census_chunk_149] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_150 : countBelow (fun n => firstEventB 15 (19200 + n)) 128 = 0 := by decide

theorem census_prefix_151 : countBelow (firstEventB 15) 19328 = 104 := by
  have h := count_shift_add (firstEventB 15) 19200 128
  rw [census_prefix_150, census_chunk_150] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_151 : countBelow (fun n => firstEventB 15 (19328 + n)) 128 = 0 := by decide

theorem census_prefix_152 : countBelow (firstEventB 15) 19456 = 104 := by
  have h := count_shift_add (firstEventB 15) 19328 128
  rw [census_prefix_151, census_chunk_151] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_152 : countBelow (fun n => firstEventB 15 (19456 + n)) 128 = 0 := by decide

theorem census_prefix_153 : countBelow (firstEventB 15) 19584 = 104 := by
  have h := count_shift_add (firstEventB 15) 19456 128
  rw [census_prefix_152, census_chunk_152] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_153 : countBelow (fun n => firstEventB 15 (19584 + n)) 128 = 1 := by decide

theorem census_prefix_154 : countBelow (firstEventB 15) 19712 = 105 := by
  have h := count_shift_add (firstEventB 15) 19584 128
  rw [census_prefix_153, census_chunk_153] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_154 : countBelow (fun n => firstEventB 15 (19712 + n)) 128 = 0 := by decide

theorem census_prefix_155 : countBelow (firstEventB 15) 19840 = 105 := by
  have h := count_shift_add (firstEventB 15) 19712 128
  rw [census_prefix_154, census_chunk_154] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_155 : countBelow (fun n => firstEventB 15 (19840 + n)) 128 = 1 := by decide

theorem census_prefix_156 : countBelow (firstEventB 15) 19968 = 106 := by
  have h := count_shift_add (firstEventB 15) 19840 128
  rw [census_prefix_155, census_chunk_155] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_156 : countBelow (fun n => firstEventB 15 (19968 + n)) 128 = 1 := by decide

theorem census_prefix_157 : countBelow (firstEventB 15) 20096 = 107 := by
  have h := count_shift_add (firstEventB 15) 19968 128
  rw [census_prefix_156, census_chunk_156] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_157 : countBelow (fun n => firstEventB 15 (20096 + n)) 128 = 1 := by decide

theorem census_prefix_158 : countBelow (firstEventB 15) 20224 = 108 := by
  have h := count_shift_add (firstEventB 15) 20096 128
  rw [census_prefix_157, census_chunk_157] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_158 : countBelow (fun n => firstEventB 15 (20224 + n)) 128 = 0 := by decide

theorem census_prefix_159 : countBelow (firstEventB 15) 20352 = 108 := by
  have h := count_shift_add (firstEventB 15) 20224 128
  rw [census_prefix_158, census_chunk_158] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_159 : countBelow (fun n => firstEventB 15 (20352 + n)) 128 = 0 := by decide

theorem census_prefix_160 : countBelow (firstEventB 15) 20480 = 108 := by
  have h := count_shift_add (firstEventB 15) 20352 128
  rw [census_prefix_159, census_chunk_159] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_160 : countBelow (fun n => firstEventB 15 (20480 + n)) 128 = 2 := by decide

theorem census_prefix_161 : countBelow (firstEventB 15) 20608 = 110 := by
  have h := count_shift_add (firstEventB 15) 20480 128
  rw [census_prefix_160, census_chunk_160] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_161 : countBelow (fun n => firstEventB 15 (20608 + n)) 128 = 0 := by decide

theorem census_prefix_162 : countBelow (firstEventB 15) 20736 = 110 := by
  have h := count_shift_add (firstEventB 15) 20608 128
  rw [census_prefix_161, census_chunk_161] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_162 : countBelow (fun n => firstEventB 15 (20736 + n)) 128 = 1 := by decide

theorem census_prefix_163 : countBelow (firstEventB 15) 20864 = 111 := by
  have h := count_shift_add (firstEventB 15) 20736 128
  rw [census_prefix_162, census_chunk_162] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_163 : countBelow (fun n => firstEventB 15 (20864 + n)) 128 = 1 := by decide

theorem census_prefix_164 : countBelow (firstEventB 15) 20992 = 112 := by
  have h := count_shift_add (firstEventB 15) 20864 128
  rw [census_prefix_163, census_chunk_163] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_164 : countBelow (fun n => firstEventB 15 (20992 + n)) 128 = 2 := by decide

theorem census_prefix_165 : countBelow (firstEventB 15) 21120 = 114 := by
  have h := count_shift_add (firstEventB 15) 20992 128
  rw [census_prefix_164, census_chunk_164] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_165 : countBelow (fun n => firstEventB 15 (21120 + n)) 128 = 1 := by decide

theorem census_prefix_166 : countBelow (firstEventB 15) 21248 = 115 := by
  have h := count_shift_add (firstEventB 15) 21120 128
  rw [census_prefix_165, census_chunk_165] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_166 : countBelow (fun n => firstEventB 15 (21248 + n)) 128 = 0 := by decide

theorem census_prefix_167 : countBelow (firstEventB 15) 21376 = 115 := by
  have h := count_shift_add (firstEventB 15) 21248 128
  rw [census_prefix_166, census_chunk_166] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_167 : countBelow (fun n => firstEventB 15 (21376 + n)) 128 = 1 := by decide

theorem census_prefix_168 : countBelow (firstEventB 15) 21504 = 116 := by
  have h := count_shift_add (firstEventB 15) 21376 128
  rw [census_prefix_167, census_chunk_167] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_168 : countBelow (fun n => firstEventB 15 (21504 + n)) 128 = 0 := by decide

theorem census_prefix_169 : countBelow (firstEventB 15) 21632 = 116 := by
  have h := count_shift_add (firstEventB 15) 21504 128
  rw [census_prefix_168, census_chunk_168] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_169 : countBelow (fun n => firstEventB 15 (21632 + n)) 128 = 1 := by decide

theorem census_prefix_170 : countBelow (firstEventB 15) 21760 = 117 := by
  have h := count_shift_add (firstEventB 15) 21632 128
  rw [census_prefix_169, census_chunk_169] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_170 : countBelow (fun n => firstEventB 15 (21760 + n)) 128 = 1 := by decide

theorem census_prefix_171 : countBelow (firstEventB 15) 21888 = 118 := by
  have h := count_shift_add (firstEventB 15) 21760 128
  rw [census_prefix_170, census_chunk_170] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_171 : countBelow (fun n => firstEventB 15 (21888 + n)) 128 = 0 := by decide

theorem census_prefix_172 : countBelow (firstEventB 15) 22016 = 118 := by
  have h := count_shift_add (firstEventB 15) 21888 128
  rw [census_prefix_171, census_chunk_171] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_172 : countBelow (fun n => firstEventB 15 (22016 + n)) 128 = 1 := by decide

theorem census_prefix_173 : countBelow (firstEventB 15) 22144 = 119 := by
  have h := count_shift_add (firstEventB 15) 22016 128
  rw [census_prefix_172, census_chunk_172] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_173 : countBelow (fun n => firstEventB 15 (22144 + n)) 128 = 1 := by decide

theorem census_prefix_174 : countBelow (firstEventB 15) 22272 = 120 := by
  have h := count_shift_add (firstEventB 15) 22144 128
  rw [census_prefix_173, census_chunk_173] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_174 : countBelow (fun n => firstEventB 15 (22272 + n)) 128 = 0 := by decide

theorem census_prefix_175 : countBelow (firstEventB 15) 22400 = 120 := by
  have h := count_shift_add (firstEventB 15) 22272 128
  rw [census_prefix_174, census_chunk_174] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_175 : countBelow (fun n => firstEventB 15 (22400 + n)) 128 = 0 := by decide

theorem census_prefix_176 : countBelow (firstEventB 15) 22528 = 120 := by
  have h := count_shift_add (firstEventB 15) 22400 128
  rw [census_prefix_175, census_chunk_175] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_176 : countBelow (fun n => firstEventB 15 (22528 + n)) 128 = 1 := by decide

theorem census_prefix_177 : countBelow (firstEventB 15) 22656 = 121 := by
  have h := count_shift_add (firstEventB 15) 22528 128
  rw [census_prefix_176, census_chunk_176] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_177 : countBelow (fun n => firstEventB 15 (22656 + n)) 128 = 1 := by decide

theorem census_prefix_178 : countBelow (firstEventB 15) 22784 = 122 := by
  have h := count_shift_add (firstEventB 15) 22656 128
  rw [census_prefix_177, census_chunk_177] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_178 : countBelow (fun n => firstEventB 15 (22784 + n)) 128 = 2 := by decide

theorem census_prefix_179 : countBelow (firstEventB 15) 22912 = 124 := by
  have h := count_shift_add (firstEventB 15) 22784 128
  rw [census_prefix_178, census_chunk_178] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_179 : countBelow (fun n => firstEventB 15 (22912 + n)) 128 = 1 := by decide

theorem census_prefix_180 : countBelow (firstEventB 15) 23040 = 125 := by
  have h := count_shift_add (firstEventB 15) 22912 128
  rw [census_prefix_179, census_chunk_179] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_180 : countBelow (fun n => firstEventB 15 (23040 + n)) 128 = 0 := by decide

theorem census_prefix_181 : countBelow (firstEventB 15) 23168 = 125 := by
  have h := count_shift_add (firstEventB 15) 23040 128
  rw [census_prefix_180, census_chunk_180] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_181 : countBelow (fun n => firstEventB 15 (23168 + n)) 128 = 1 := by decide

theorem census_prefix_182 : countBelow (firstEventB 15) 23296 = 126 := by
  have h := count_shift_add (firstEventB 15) 23168 128
  rw [census_prefix_181, census_chunk_181] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_182 : countBelow (fun n => firstEventB 15 (23296 + n)) 128 = 2 := by decide

theorem census_prefix_183 : countBelow (firstEventB 15) 23424 = 128 := by
  have h := count_shift_add (firstEventB 15) 23296 128
  rw [census_prefix_182, census_chunk_182] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_183 : countBelow (fun n => firstEventB 15 (23424 + n)) 128 = 0 := by decide

theorem census_prefix_184 : countBelow (firstEventB 15) 23552 = 128 := by
  have h := count_shift_add (firstEventB 15) 23424 128
  rw [census_prefix_183, census_chunk_183] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_184 : countBelow (fun n => firstEventB 15 (23552 + n)) 128 = 1 := by decide

theorem census_prefix_185 : countBelow (firstEventB 15) 23680 = 129 := by
  have h := count_shift_add (firstEventB 15) 23552 128
  rw [census_prefix_184, census_chunk_184] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_185 : countBelow (fun n => firstEventB 15 (23680 + n)) 128 = 1 := by decide

theorem census_prefix_186 : countBelow (firstEventB 15) 23808 = 130 := by
  have h := count_shift_add (firstEventB 15) 23680 128
  rw [census_prefix_185, census_chunk_185] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_186 : countBelow (fun n => firstEventB 15 (23808 + n)) 128 = 2 := by decide

theorem census_prefix_187 : countBelow (firstEventB 15) 23936 = 132 := by
  have h := count_shift_add (firstEventB 15) 23808 128
  rw [census_prefix_186, census_chunk_186] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_187 : countBelow (fun n => firstEventB 15 (23936 + n)) 128 = 0 := by decide

theorem census_prefix_188 : countBelow (firstEventB 15) 24064 = 132 := by
  have h := count_shift_add (firstEventB 15) 23936 128
  rw [census_prefix_187, census_chunk_187] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_188 : countBelow (fun n => firstEventB 15 (24064 + n)) 128 = 0 := by decide

theorem census_prefix_189 : countBelow (firstEventB 15) 24192 = 132 := by
  have h := count_shift_add (firstEventB 15) 24064 128
  rw [census_prefix_188, census_chunk_188] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_189 : countBelow (fun n => firstEventB 15 (24192 + n)) 128 = 1 := by decide

theorem census_prefix_190 : countBelow (firstEventB 15) 24320 = 133 := by
  have h := count_shift_add (firstEventB 15) 24192 128
  rw [census_prefix_189, census_chunk_189] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_190 : countBelow (fun n => firstEventB 15 (24320 + n)) 128 = 0 := by decide

theorem census_prefix_191 : countBelow (firstEventB 15) 24448 = 133 := by
  have h := count_shift_add (firstEventB 15) 24320 128
  rw [census_prefix_190, census_chunk_190] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_191 : countBelow (fun n => firstEventB 15 (24448 + n)) 128 = 1 := by decide

theorem census_prefix_192 : countBelow (firstEventB 15) 24576 = 134 := by
  have h := count_shift_add (firstEventB 15) 24448 128
  rw [census_prefix_191, census_chunk_191] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_192 : countBelow (fun n => firstEventB 15 (24576 + n)) 128 = 3 := by decide

theorem census_prefix_193 : countBelow (firstEventB 15) 24704 = 137 := by
  have h := count_shift_add (firstEventB 15) 24576 128
  rw [census_prefix_192, census_chunk_192] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_193 : countBelow (fun n => firstEventB 15 (24704 + n)) 128 = 0 := by decide

theorem census_prefix_194 : countBelow (firstEventB 15) 24832 = 137 := by
  have h := count_shift_add (firstEventB 15) 24704 128
  rw [census_prefix_193, census_chunk_193] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_194 : countBelow (fun n => firstEventB 15 (24832 + n)) 128 = 0 := by decide

theorem census_prefix_195 : countBelow (firstEventB 15) 24960 = 137 := by
  have h := count_shift_add (firstEventB 15) 24832 128
  rw [census_prefix_194, census_chunk_194] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_195 : countBelow (fun n => firstEventB 15 (24960 + n)) 128 = 0 := by decide

theorem census_prefix_196 : countBelow (firstEventB 15) 25088 = 137 := by
  have h := count_shift_add (firstEventB 15) 24960 128
  rw [census_prefix_195, census_chunk_195] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_196 : countBelow (fun n => firstEventB 15 (25088 + n)) 128 = 0 := by decide

theorem census_prefix_197 : countBelow (firstEventB 15) 25216 = 137 := by
  have h := count_shift_add (firstEventB 15) 25088 128
  rw [census_prefix_196, census_chunk_196] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_197 : countBelow (fun n => firstEventB 15 (25216 + n)) 128 = 1 := by decide

theorem census_prefix_198 : countBelow (firstEventB 15) 25344 = 138 := by
  have h := count_shift_add (firstEventB 15) 25216 128
  rw [census_prefix_197, census_chunk_197] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_198 : countBelow (fun n => firstEventB 15 (25344 + n)) 128 = 0 := by decide

theorem census_prefix_199 : countBelow (firstEventB 15) 25472 = 138 := by
  have h := count_shift_add (firstEventB 15) 25344 128
  rw [census_prefix_198, census_chunk_198] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_199 : countBelow (fun n => firstEventB 15 (25472 + n)) 128 = 2 := by decide

theorem census_prefix_200 : countBelow (firstEventB 15) 25600 = 140 := by
  have h := count_shift_add (firstEventB 15) 25472 128
  rw [census_prefix_199, census_chunk_199] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_200 : countBelow (fun n => firstEventB 15 (25600 + n)) 128 = 2 := by decide

theorem census_prefix_201 : countBelow (firstEventB 15) 25728 = 142 := by
  have h := count_shift_add (firstEventB 15) 25600 128
  rw [census_prefix_200, census_chunk_200] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_201 : countBelow (fun n => firstEventB 15 (25728 + n)) 128 = 1 := by decide

theorem census_prefix_202 : countBelow (firstEventB 15) 25856 = 143 := by
  have h := count_shift_add (firstEventB 15) 25728 128
  rw [census_prefix_201, census_chunk_201] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_202 : countBelow (fun n => firstEventB 15 (25856 + n)) 128 = 0 := by decide

theorem census_prefix_203 : countBelow (firstEventB 15) 25984 = 143 := by
  have h := count_shift_add (firstEventB 15) 25856 128
  rw [census_prefix_202, census_chunk_202] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_203 : countBelow (fun n => firstEventB 15 (25984 + n)) 128 = 1 := by decide

theorem census_prefix_204 : countBelow (firstEventB 15) 26112 = 144 := by
  have h := count_shift_add (firstEventB 15) 25984 128
  rw [census_prefix_203, census_chunk_203] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_204 : countBelow (fun n => firstEventB 15 (26112 + n)) 128 = 0 := by decide

theorem census_prefix_205 : countBelow (firstEventB 15) 26240 = 144 := by
  have h := count_shift_add (firstEventB 15) 26112 128
  rw [census_prefix_204, census_chunk_204] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_205 : countBelow (fun n => firstEventB 15 (26240 + n)) 128 = 1 := by decide

theorem census_prefix_206 : countBelow (firstEventB 15) 26368 = 145 := by
  have h := count_shift_add (firstEventB 15) 26240 128
  rw [census_prefix_205, census_chunk_205] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_206 : countBelow (fun n => firstEventB 15 (26368 + n)) 128 = 0 := by decide

theorem census_prefix_207 : countBelow (firstEventB 15) 26496 = 145 := by
  have h := count_shift_add (firstEventB 15) 26368 128
  rw [census_prefix_206, census_chunk_206] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_207 : countBelow (fun n => firstEventB 15 (26496 + n)) 128 = 2 := by decide

theorem census_prefix_208 : countBelow (firstEventB 15) 26624 = 147 := by
  have h := count_shift_add (firstEventB 15) 26496 128
  rw [census_prefix_207, census_chunk_207] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_208 : countBelow (fun n => firstEventB 15 (26624 + n)) 128 = 0 := by decide

theorem census_prefix_209 : countBelow (firstEventB 15) 26752 = 147 := by
  have h := count_shift_add (firstEventB 15) 26624 128
  rw [census_prefix_208, census_chunk_208] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_209 : countBelow (fun n => firstEventB 15 (26752 + n)) 128 = 0 := by decide

theorem census_prefix_210 : countBelow (firstEventB 15) 26880 = 147 := by
  have h := count_shift_add (firstEventB 15) 26752 128
  rw [census_prefix_209, census_chunk_209] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_210 : countBelow (fun n => firstEventB 15 (26880 + n)) 128 = 0 := by decide

theorem census_prefix_211 : countBelow (firstEventB 15) 27008 = 147 := by
  have h := count_shift_add (firstEventB 15) 26880 128
  rw [census_prefix_210, census_chunk_210] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_211 : countBelow (fun n => firstEventB 15 (27008 + n)) 128 = 1 := by decide

theorem census_prefix_212 : countBelow (firstEventB 15) 27136 = 148 := by
  have h := count_shift_add (firstEventB 15) 27008 128
  rw [census_prefix_211, census_chunk_211] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_212 : countBelow (fun n => firstEventB 15 (27136 + n)) 128 = 0 := by decide

theorem census_prefix_213 : countBelow (firstEventB 15) 27264 = 148 := by
  have h := count_shift_add (firstEventB 15) 27136 128
  rw [census_prefix_212, census_chunk_212] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_213 : countBelow (fun n => firstEventB 15 (27264 + n)) 128 = 1 := by decide

theorem census_prefix_214 : countBelow (firstEventB 15) 27392 = 149 := by
  have h := count_shift_add (firstEventB 15) 27264 128
  rw [census_prefix_213, census_chunk_213] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_214 : countBelow (fun n => firstEventB 15 (27392 + n)) 128 = 0 := by decide

theorem census_prefix_215 : countBelow (firstEventB 15) 27520 = 149 := by
  have h := count_shift_add (firstEventB 15) 27392 128
  rw [census_prefix_214, census_chunk_214] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_215 : countBelow (fun n => firstEventB 15 (27520 + n)) 128 = 0 := by decide

theorem census_prefix_216 : countBelow (firstEventB 15) 27648 = 149 := by
  have h := count_shift_add (firstEventB 15) 27520 128
  rw [census_prefix_215, census_chunk_215] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_216 : countBelow (fun n => firstEventB 15 (27648 + n)) 128 = 1 := by decide

theorem census_prefix_217 : countBelow (firstEventB 15) 27776 = 150 := by
  have h := count_shift_add (firstEventB 15) 27648 128
  rw [census_prefix_216, census_chunk_216] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_217 : countBelow (fun n => firstEventB 15 (27776 + n)) 128 = 2 := by decide

theorem census_prefix_218 : countBelow (firstEventB 15) 27904 = 152 := by
  have h := count_shift_add (firstEventB 15) 27776 128
  rw [census_prefix_217, census_chunk_217] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_218 : countBelow (fun n => firstEventB 15 (27904 + n)) 128 = 1 := by decide

theorem census_prefix_219 : countBelow (firstEventB 15) 28032 = 153 := by
  have h := count_shift_add (firstEventB 15) 27904 128
  rw [census_prefix_218, census_chunk_218] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_219 : countBelow (fun n => firstEventB 15 (28032 + n)) 128 = 0 := by decide

theorem census_prefix_220 : countBelow (firstEventB 15) 28160 = 153 := by
  have h := count_shift_add (firstEventB 15) 28032 128
  rw [census_prefix_219, census_chunk_219] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_220 : countBelow (fun n => firstEventB 15 (28160 + n)) 128 = 0 := by decide

theorem census_prefix_221 : countBelow (firstEventB 15) 28288 = 153 := by
  have h := count_shift_add (firstEventB 15) 28160 128
  rw [census_prefix_220, census_chunk_220] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_221 : countBelow (fun n => firstEventB 15 (28288 + n)) 128 = 0 := by decide

theorem census_prefix_222 : countBelow (firstEventB 15) 28416 = 153 := by
  have h := count_shift_add (firstEventB 15) 28288 128
  rw [census_prefix_221, census_chunk_221] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_222 : countBelow (fun n => firstEventB 15 (28416 + n)) 128 = 0 := by decide

theorem census_prefix_223 : countBelow (firstEventB 15) 28544 = 153 := by
  have h := count_shift_add (firstEventB 15) 28416 128
  rw [census_prefix_222, census_chunk_222] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_223 : countBelow (fun n => firstEventB 15 (28544 + n)) 128 = 0 := by decide

theorem census_prefix_224 : countBelow (firstEventB 15) 28672 = 153 := by
  have h := count_shift_add (firstEventB 15) 28544 128
  rw [census_prefix_223, census_chunk_223] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_224 : countBelow (fun n => firstEventB 15 (28672 + n)) 128 = 1 := by decide

theorem census_prefix_225 : countBelow (firstEventB 15) 28800 = 154 := by
  have h := count_shift_add (firstEventB 15) 28672 128
  rw [census_prefix_224, census_chunk_224] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_225 : countBelow (fun n => firstEventB 15 (28800 + n)) 128 = 1 := by decide

theorem census_prefix_226 : countBelow (firstEventB 15) 28928 = 155 := by
  have h := count_shift_add (firstEventB 15) 28800 128
  rw [census_prefix_225, census_chunk_225] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_226 : countBelow (fun n => firstEventB 15 (28928 + n)) 128 = 1 := by decide

theorem census_prefix_227 : countBelow (firstEventB 15) 29056 = 156 := by
  have h := count_shift_add (firstEventB 15) 28928 128
  rw [census_prefix_226, census_chunk_226] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_227 : countBelow (fun n => firstEventB 15 (29056 + n)) 128 = 0 := by decide

theorem census_prefix_228 : countBelow (firstEventB 15) 29184 = 156 := by
  have h := count_shift_add (firstEventB 15) 29056 128
  rw [census_prefix_227, census_chunk_227] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_228 : countBelow (fun n => firstEventB 15 (29184 + n)) 128 = 0 := by decide

theorem census_prefix_229 : countBelow (firstEventB 15) 29312 = 156 := by
  have h := count_shift_add (firstEventB 15) 29184 128
  rw [census_prefix_228, census_chunk_228] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_229 : countBelow (fun n => firstEventB 15 (29312 + n)) 128 = 0 := by decide

theorem census_prefix_230 : countBelow (firstEventB 15) 29440 = 156 := by
  have h := count_shift_add (firstEventB 15) 29312 128
  rw [census_prefix_229, census_chunk_229] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_230 : countBelow (fun n => firstEventB 15 (29440 + n)) 128 = 1 := by decide

theorem census_prefix_231 : countBelow (firstEventB 15) 29568 = 157 := by
  have h := count_shift_add (firstEventB 15) 29440 128
  rw [census_prefix_230, census_chunk_230] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_231 : countBelow (fun n => firstEventB 15 (29568 + n)) 128 = 0 := by decide

theorem census_prefix_232 : countBelow (firstEventB 15) 29696 = 157 := by
  have h := count_shift_add (firstEventB 15) 29568 128
  rw [census_prefix_231, census_chunk_231] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_232 : countBelow (fun n => firstEventB 15 (29696 + n)) 128 = 1 := by decide

theorem census_prefix_233 : countBelow (firstEventB 15) 29824 = 158 := by
  have h := count_shift_add (firstEventB 15) 29696 128
  rw [census_prefix_232, census_chunk_232] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_233 : countBelow (fun n => firstEventB 15 (29824 + n)) 128 = 1 := by decide

theorem census_prefix_234 : countBelow (firstEventB 15) 29952 = 159 := by
  have h := count_shift_add (firstEventB 15) 29824 128
  rw [census_prefix_233, census_chunk_233] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_234 : countBelow (fun n => firstEventB 15 (29952 + n)) 128 = 0 := by decide

theorem census_prefix_235 : countBelow (firstEventB 15) 30080 = 159 := by
  have h := count_shift_add (firstEventB 15) 29952 128
  rw [census_prefix_234, census_chunk_234] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_235 : countBelow (fun n => firstEventB 15 (30080 + n)) 128 = 0 := by decide

theorem census_prefix_236 : countBelow (firstEventB 15) 30208 = 159 := by
  have h := count_shift_add (firstEventB 15) 30080 128
  rw [census_prefix_235, census_chunk_235] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_236 : countBelow (fun n => firstEventB 15 (30208 + n)) 128 = 1 := by decide

theorem census_prefix_237 : countBelow (firstEventB 15) 30336 = 160 := by
  have h := count_shift_add (firstEventB 15) 30208 128
  rw [census_prefix_236, census_chunk_236] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_237 : countBelow (fun n => firstEventB 15 (30336 + n)) 128 = 0 := by decide

theorem census_prefix_238 : countBelow (firstEventB 15) 30464 = 160 := by
  have h := count_shift_add (firstEventB 15) 30336 128
  rw [census_prefix_237, census_chunk_237] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_238 : countBelow (fun n => firstEventB 15 (30464 + n)) 128 = 1 := by decide

theorem census_prefix_239 : countBelow (firstEventB 15) 30592 = 161 := by
  have h := count_shift_add (firstEventB 15) 30464 128
  rw [census_prefix_238, census_chunk_238] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_239 : countBelow (fun n => firstEventB 15 (30592 + n)) 128 = 2 := by decide

theorem census_prefix_240 : countBelow (firstEventB 15) 30720 = 163 := by
  have h := count_shift_add (firstEventB 15) 30592 128
  rw [census_prefix_239, census_chunk_239] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_240 : countBelow (fun n => firstEventB 15 (30720 + n)) 128 = 2 := by decide

theorem census_prefix_241 : countBelow (firstEventB 15) 30848 = 165 := by
  have h := count_shift_add (firstEventB 15) 30720 128
  rw [census_prefix_240, census_chunk_240] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_241 : countBelow (fun n => firstEventB 15 (30848 + n)) 128 = 1 := by decide

theorem census_prefix_242 : countBelow (firstEventB 15) 30976 = 166 := by
  have h := count_shift_add (firstEventB 15) 30848 128
  rw [census_prefix_241, census_chunk_241] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_242 : countBelow (fun n => firstEventB 15 (30976 + n)) 128 = 0 := by decide

theorem census_prefix_243 : countBelow (firstEventB 15) 31104 = 166 := by
  have h := count_shift_add (firstEventB 15) 30976 128
  rw [census_prefix_242, census_chunk_242] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_243 : countBelow (fun n => firstEventB 15 (31104 + n)) 128 = 0 := by decide

theorem census_prefix_244 : countBelow (firstEventB 15) 31232 = 166 := by
  have h := count_shift_add (firstEventB 15) 31104 128
  rw [census_prefix_243, census_chunk_243] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_244 : countBelow (fun n => firstEventB 15 (31232 + n)) 128 = 0 := by decide

theorem census_prefix_245 : countBelow (firstEventB 15) 31360 = 166 := by
  have h := count_shift_add (firstEventB 15) 31232 128
  rw [census_prefix_244, census_chunk_244] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_245 : countBelow (fun n => firstEventB 15 (31360 + n)) 128 = 0 := by decide

theorem census_prefix_246 : countBelow (firstEventB 15) 31488 = 166 := by
  have h := count_shift_add (firstEventB 15) 31360 128
  rw [census_prefix_245, census_chunk_245] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_246 : countBelow (fun n => firstEventB 15 (31488 + n)) 128 = 0 := by decide

theorem census_prefix_247 : countBelow (firstEventB 15) 31616 = 166 := by
  have h := count_shift_add (firstEventB 15) 31488 128
  rw [census_prefix_246, census_chunk_246] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_247 : countBelow (fun n => firstEventB 15 (31616 + n)) 128 = 1 := by decide

theorem census_prefix_248 : countBelow (firstEventB 15) 31744 = 167 := by
  have h := count_shift_add (firstEventB 15) 31616 128
  rw [census_prefix_247, census_chunk_247] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_248 : countBelow (fun n => firstEventB 15 (31744 + n)) 128 = 1 := by decide

theorem census_prefix_249 : countBelow (firstEventB 15) 31872 = 168 := by
  have h := count_shift_add (firstEventB 15) 31744 128
  rw [census_prefix_248, census_chunk_248] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_249 : countBelow (fun n => firstEventB 15 (31872 + n)) 128 = 1 := by decide

theorem census_prefix_250 : countBelow (firstEventB 15) 32000 = 169 := by
  have h := count_shift_add (firstEventB 15) 31872 128
  rw [census_prefix_249, census_chunk_249] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_250 : countBelow (fun n => firstEventB 15 (32000 + n)) 128 = 0 := by decide

theorem census_prefix_251 : countBelow (firstEventB 15) 32128 = 169 := by
  have h := count_shift_add (firstEventB 15) 32000 128
  rw [census_prefix_250, census_chunk_250] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_251 : countBelow (fun n => firstEventB 15 (32128 + n)) 128 = 2 := by decide

theorem census_prefix_252 : countBelow (firstEventB 15) 32256 = 171 := by
  have h := count_shift_add (firstEventB 15) 32128 128
  rw [census_prefix_251, census_chunk_251] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_252 : countBelow (fun n => firstEventB 15 (32256 + n)) 128 = 0 := by decide

theorem census_prefix_253 : countBelow (firstEventB 15) 32384 = 171 := by
  have h := count_shift_add (firstEventB 15) 32256 128
  rw [census_prefix_252, census_chunk_252] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_253 : countBelow (fun n => firstEventB 15 (32384 + n)) 128 = 0 := by decide

theorem census_prefix_254 : countBelow (firstEventB 15) 32512 = 171 := by
  have h := count_shift_add (firstEventB 15) 32384 128
  rw [census_prefix_253, census_chunk_253] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_254 : countBelow (fun n => firstEventB 15 (32512 + n)) 128 = 2 := by decide

theorem census_prefix_255 : countBelow (firstEventB 15) 32640 = 173 := by
  have h := count_shift_add (firstEventB 15) 32512 128
  rw [census_prefix_254, census_chunk_254] at h
  exact h

/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_255 : countBelow (fun n => firstEventB 15 (32640 + n)) 128 = 0 := by decide

theorem census_prefix_256 : countBelow (firstEventB 15) 32768 = 173 := by
  have h := count_shift_add (firstEventB 15) 32640 128
  rw [census_prefix_255, census_chunk_255] at h
  exact h

/-- Complete period numerator, checked independently of the cylinder classifier. -/
theorem period_count_fifteen : countBelow (firstEventB 15) (2 ^ 15) = 173 := census_prefix_256

/-- Composition-sensitive count bound at every finite cutoff. -/
theorem depth_fifteen_error (N : Nat) :
    32768 * countBelow (firstEventB 15) N ≤ N * 173 + 5638935 ∧
    N * 173 ≤ 32768 * countBelow (firstEventB 15) N + 5638935 := by
  have h := firstEvent_composition_error 15 N
  dsimp only at h
  rw [period_count_fifteen] at h
  simpa only [show (2 : Nat) ^ 15 = 32768 by decide,
    show (32768 - 173 : Nat) = 32595 by decide,
    show (173 * 32595 : Nat) = 5638935 by decide] using h

end Collatz.Research.PassageAtlas
