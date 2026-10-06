import Collatz.Research.StoppingAtlas.Discrepancy

namespace Collatz.Research.StoppingAtlas
open PeriodicCounting
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- Split a counting window into a prefix and a translated suffix. -/
theorem count_shift_add (P : Nat → Bool) (N M : Nat) :
    countBelow P (N + M) = countBelow P N + countBelow (fun n => P (N + n)) M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.add_succ, count_succ, ih, count_succ]
    omega

theorem prefix_10_0 : countBelow (firstEventB 10) 0 = 0 := rfl

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_10_0 : countBelow (fun n => firstEventB 10 (0 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_10_1 : countBelow (firstEventB 10) 128 = 0 := by
  have h := count_shift_add (firstEventB 10) 0 128
  rw [prefix_10_0, chunk_10_0] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_10_1 : countBelow (fun n => firstEventB 10 (128 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_10_2 : countBelow (firstEventB 10) 256 = 0 := by
  have h := count_shift_add (firstEventB 10) 128 128
  rw [prefix_10_1, chunk_10_1] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_10_2 : countBelow (fun n => firstEventB 10 (256 + n)) 128 = 3 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_10_3 : countBelow (firstEventB 10) 384 = 3 := by
  have h := count_shift_add (firstEventB 10) 256 128
  rw [prefix_10_2, chunk_10_2] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_10_3 : countBelow (fun n => firstEventB 10 (384 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_10_4 : countBelow (firstEventB 10) 512 = 5 := by
  have h := count_shift_add (firstEventB 10) 384 128
  rw [prefix_10_3, chunk_10_3] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_10_4 : countBelow (fun n => firstEventB 10 (512 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_10_5 : countBelow (firstEventB 10) 640 = 7 := by
  have h := count_shift_add (firstEventB 10) 512 128
  rw [prefix_10_4, chunk_10_4] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_10_5 : countBelow (fun n => firstEventB 10 (640 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_10_6 : countBelow (firstEventB 10) 768 = 8 := by
  have h := count_shift_add (firstEventB 10) 640 128
  rw [prefix_10_5, chunk_10_5] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_10_6 : countBelow (fun n => firstEventB 10 (768 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_10_7 : countBelow (firstEventB 10) 896 = 9 := by
  have h := count_shift_add (firstEventB 10) 768 128
  rw [prefix_10_6, chunk_10_6] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_10_7 : countBelow (fun n => firstEventB 10 (896 + n)) 128 = 3 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_10_8 : countBelow (firstEventB 10) 1024 = 12 := by
  have h := count_shift_add (firstEventB 10) 896 128
  rw [prefix_10_7, chunk_10_7] at h
  exact h

/-- Complete period numerator at depth 10. -/
theorem period_count_10 : countBelow (firstEventB 10) (2 ^ 10) = 12 := prefix_10_8

theorem prefix_11_0 : countBelow (firstEventB 11) 0 = 0 := rfl

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_11_0 : countBelow (fun n => firstEventB 11 (0 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_11_1 : countBelow (firstEventB 11) 128 = 0 := by
  have h := count_shift_add (firstEventB 11) 0 128
  rw [prefix_11_0, chunk_11_0] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_11_1 : countBelow (fun n => firstEventB 11 (128 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_11_2 : countBelow (firstEventB 11) 256 = 0 := by
  have h := count_shift_add (firstEventB 11) 128 128
  rw [prefix_11_1, chunk_11_1] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_11_2 : countBelow (fun n => firstEventB 11 (256 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_11_3 : countBelow (firstEventB 11) 384 = 0 := by
  have h := count_shift_add (firstEventB 11) 256 128
  rw [prefix_11_2, chunk_11_2] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_11_3 : countBelow (fun n => firstEventB 11 (384 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_11_4 : countBelow (firstEventB 11) 512 = 0 := by
  have h := count_shift_add (firstEventB 11) 384 128
  rw [prefix_11_3, chunk_11_3] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_11_4 : countBelow (fun n => firstEventB 11 (512 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_11_5 : countBelow (firstEventB 11) 640 = 0 := by
  have h := count_shift_add (firstEventB 11) 512 128
  rw [prefix_11_4, chunk_11_4] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_11_5 : countBelow (fun n => firstEventB 11 (640 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_11_6 : countBelow (firstEventB 11) 768 = 0 := by
  have h := count_shift_add (firstEventB 11) 640 128
  rw [prefix_11_5, chunk_11_5] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_11_6 : countBelow (fun n => firstEventB 11 (768 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_11_7 : countBelow (firstEventB 11) 896 = 0 := by
  have h := count_shift_add (firstEventB 11) 768 128
  rw [prefix_11_6, chunk_11_6] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_11_7 : countBelow (fun n => firstEventB 11 (896 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_11_8 : countBelow (firstEventB 11) 1024 = 0 := by
  have h := count_shift_add (firstEventB 11) 896 128
  rw [prefix_11_7, chunk_11_7] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_11_8 : countBelow (fun n => firstEventB 11 (1024 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_11_9 : countBelow (firstEventB 11) 1152 = 0 := by
  have h := count_shift_add (firstEventB 11) 1024 128
  rw [prefix_11_8, chunk_11_8] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_11_9 : countBelow (fun n => firstEventB 11 (1152 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_11_10 : countBelow (firstEventB 11) 1280 = 0 := by
  have h := count_shift_add (firstEventB 11) 1152 128
  rw [prefix_11_9, chunk_11_9] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_11_10 : countBelow (fun n => firstEventB 11 (1280 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_11_11 : countBelow (firstEventB 11) 1408 = 0 := by
  have h := count_shift_add (firstEventB 11) 1280 128
  rw [prefix_11_10, chunk_11_10] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_11_11 : countBelow (fun n => firstEventB 11 (1408 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_11_12 : countBelow (firstEventB 11) 1536 = 0 := by
  have h := count_shift_add (firstEventB 11) 1408 128
  rw [prefix_11_11, chunk_11_11] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_11_12 : countBelow (fun n => firstEventB 11 (1536 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_11_13 : countBelow (firstEventB 11) 1664 = 0 := by
  have h := count_shift_add (firstEventB 11) 1536 128
  rw [prefix_11_12, chunk_11_12] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_11_13 : countBelow (fun n => firstEventB 11 (1664 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_11_14 : countBelow (firstEventB 11) 1792 = 0 := by
  have h := count_shift_add (firstEventB 11) 1664 128
  rw [prefix_11_13, chunk_11_13] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_11_14 : countBelow (fun n => firstEventB 11 (1792 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_11_15 : countBelow (firstEventB 11) 1920 = 0 := by
  have h := count_shift_add (firstEventB 11) 1792 128
  rw [prefix_11_14, chunk_11_14] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_11_15 : countBelow (fun n => firstEventB 11 (1920 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_11_16 : countBelow (firstEventB 11) 2048 = 0 := by
  have h := count_shift_add (firstEventB 11) 1920 128
  rw [prefix_11_15, chunk_11_15] at h
  exact h

/-- Complete period numerator at depth 11. -/
theorem period_count_11 : countBelow (firstEventB 11) (2 ^ 11) = 0 := prefix_11_16

theorem prefix_12_0 : countBelow (firstEventB 12) 0 = 0 := rfl

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_0 : countBelow (fun n => firstEventB 12 (0 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_1 : countBelow (firstEventB 12) 128 = 0 := by
  have h := count_shift_add (firstEventB 12) 0 128
  rw [prefix_12_0, chunk_12_0] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_1 : countBelow (fun n => firstEventB 12 (128 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_2 : countBelow (firstEventB 12) 256 = 1 := by
  have h := count_shift_add (firstEventB 12) 128 128
  rw [prefix_12_1, chunk_12_1] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_2 : countBelow (fun n => firstEventB 12 (256 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_3 : countBelow (firstEventB 12) 384 = 2 := by
  have h := count_shift_add (firstEventB 12) 256 128
  rw [prefix_12_2, chunk_12_2] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_3 : countBelow (fun n => firstEventB 12 (384 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_4 : countBelow (firstEventB 12) 512 = 3 := by
  have h := count_shift_add (firstEventB 12) 384 128
  rw [prefix_12_3, chunk_12_3] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_4 : countBelow (fun n => firstEventB 12 (512 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_5 : countBelow (firstEventB 12) 640 = 4 := by
  have h := count_shift_add (firstEventB 12) 512 128
  rw [prefix_12_4, chunk_12_4] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_5 : countBelow (fun n => firstEventB 12 (640 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_6 : countBelow (firstEventB 12) 768 = 4 := by
  have h := count_shift_add (firstEventB 12) 640 128
  rw [prefix_12_5, chunk_12_5] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_6 : countBelow (fun n => firstEventB 12 (768 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_7 : countBelow (firstEventB 12) 896 = 5 := by
  have h := count_shift_add (firstEventB 12) 768 128
  rw [prefix_12_6, chunk_12_6] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_7 : countBelow (fun n => firstEventB 12 (896 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_8 : countBelow (firstEventB 12) 1024 = 7 := by
  have h := count_shift_add (firstEventB 12) 896 128
  rw [prefix_12_7, chunk_12_7] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_8 : countBelow (fun n => firstEventB 12 (1024 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_9 : countBelow (firstEventB 12) 1152 = 8 := by
  have h := count_shift_add (firstEventB 12) 1024 128
  rw [prefix_12_8, chunk_12_8] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_9 : countBelow (fun n => firstEventB 12 (1152 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_10 : countBelow (firstEventB 12) 1280 = 9 := by
  have h := count_shift_add (firstEventB 12) 1152 128
  rw [prefix_12_9, chunk_12_9] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_10 : countBelow (fun n => firstEventB 12 (1280 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_11 : countBelow (firstEventB 12) 1408 = 9 := by
  have h := count_shift_add (firstEventB 12) 1280 128
  rw [prefix_12_10, chunk_12_10] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_11 : countBelow (fun n => firstEventB 12 (1408 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_12 : countBelow (firstEventB 12) 1536 = 10 := by
  have h := count_shift_add (firstEventB 12) 1408 128
  rw [prefix_12_11, chunk_12_11] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_12 : countBelow (fun n => firstEventB 12 (1536 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_13 : countBelow (firstEventB 12) 1664 = 11 := by
  have h := count_shift_add (firstEventB 12) 1536 128
  rw [prefix_12_12, chunk_12_12] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_13 : countBelow (fun n => firstEventB 12 (1664 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_14 : countBelow (firstEventB 12) 1792 = 13 := by
  have h := count_shift_add (firstEventB 12) 1664 128
  rw [prefix_12_13, chunk_12_13] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_14 : countBelow (fun n => firstEventB 12 (1792 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_15 : countBelow (firstEventB 12) 1920 = 15 := by
  have h := count_shift_add (firstEventB 12) 1792 128
  rw [prefix_12_14, chunk_12_14] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_15 : countBelow (fun n => firstEventB 12 (1920 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_16 : countBelow (firstEventB 12) 2048 = 16 := by
  have h := count_shift_add (firstEventB 12) 1920 128
  rw [prefix_12_15, chunk_12_15] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_16 : countBelow (fun n => firstEventB 12 (2048 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_17 : countBelow (firstEventB 12) 2176 = 16 := by
  have h := count_shift_add (firstEventB 12) 2048 128
  rw [prefix_12_16, chunk_12_16] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_17 : countBelow (fun n => firstEventB 12 (2176 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_18 : countBelow (firstEventB 12) 2304 = 18 := by
  have h := count_shift_add (firstEventB 12) 2176 128
  rw [prefix_12_17, chunk_12_17] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_18 : countBelow (fun n => firstEventB 12 (2304 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_19 : countBelow (firstEventB 12) 2432 = 19 := by
  have h := count_shift_add (firstEventB 12) 2304 128
  rw [prefix_12_18, chunk_12_18] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_19 : countBelow (fun n => firstEventB 12 (2432 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_20 : countBelow (firstEventB 12) 2560 = 19 := by
  have h := count_shift_add (firstEventB 12) 2432 128
  rw [prefix_12_19, chunk_12_19] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_20 : countBelow (fun n => firstEventB 12 (2560 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_21 : countBelow (firstEventB 12) 2688 = 21 := by
  have h := count_shift_add (firstEventB 12) 2560 128
  rw [prefix_12_20, chunk_12_20] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_21 : countBelow (fun n => firstEventB 12 (2688 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_22 : countBelow (firstEventB 12) 2816 = 21 := by
  have h := count_shift_add (firstEventB 12) 2688 128
  rw [prefix_12_21, chunk_12_21] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_22 : countBelow (fun n => firstEventB 12 (2816 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_23 : countBelow (firstEventB 12) 2944 = 22 := by
  have h := count_shift_add (firstEventB 12) 2816 128
  rw [prefix_12_22, chunk_12_22] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_23 : countBelow (fun n => firstEventB 12 (2944 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_24 : countBelow (firstEventB 12) 3072 = 23 := by
  have h := count_shift_add (firstEventB 12) 2944 128
  rw [prefix_12_23, chunk_12_23] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_24 : countBelow (fun n => firstEventB 12 (3072 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_25 : countBelow (firstEventB 12) 3200 = 25 := by
  have h := count_shift_add (firstEventB 12) 3072 128
  rw [prefix_12_24, chunk_12_24] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_25 : countBelow (fun n => firstEventB 12 (3200 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_26 : countBelow (firstEventB 12) 3328 = 26 := by
  have h := count_shift_add (firstEventB 12) 3200 128
  rw [prefix_12_25, chunk_12_25] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_26 : countBelow (fun n => firstEventB 12 (3328 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_27 : countBelow (firstEventB 12) 3456 = 26 := by
  have h := count_shift_add (firstEventB 12) 3328 128
  rw [prefix_12_26, chunk_12_26] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_27 : countBelow (fun n => firstEventB 12 (3456 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_28 : countBelow (firstEventB 12) 3584 = 27 := by
  have h := count_shift_add (firstEventB 12) 3456 128
  rw [prefix_12_27, chunk_12_27] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_28 : countBelow (fun n => firstEventB 12 (3584 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_29 : countBelow (firstEventB 12) 3712 = 28 := by
  have h := count_shift_add (firstEventB 12) 3584 128
  rw [prefix_12_28, chunk_12_28] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_29 : countBelow (fun n => firstEventB 12 (3712 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_30 : countBelow (firstEventB 12) 3840 = 28 := by
  have h := count_shift_add (firstEventB 12) 3712 128
  rw [prefix_12_29, chunk_12_29] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_30 : countBelow (fun n => firstEventB 12 (3840 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_31 : countBelow (firstEventB 12) 3968 = 29 := by
  have h := count_shift_add (firstEventB 12) 3840 128
  rw [prefix_12_30, chunk_12_30] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_12_31 : countBelow (fun n => firstEventB 12 (3968 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_12_32 : countBelow (firstEventB 12) 4096 = 30 := by
  have h := count_shift_add (firstEventB 12) 3968 128
  rw [prefix_12_31, chunk_12_31] at h
  exact h

/-- Complete period numerator at depth 12. -/
theorem period_count_12 : countBelow (firstEventB 12) (2 ^ 12) = 30 := prefix_12_32

theorem prefix_13_0 : countBelow (firstEventB 13) 0 = 0 := rfl

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_0 : countBelow (fun n => firstEventB 13 (0 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_1 : countBelow (firstEventB 13) 128 = 0 := by
  have h := count_shift_add (firstEventB 13) 0 128
  rw [prefix_13_0, chunk_13_0] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_1 : countBelow (fun n => firstEventB 13 (128 + n)) 128 = 3 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_2 : countBelow (firstEventB 13) 256 = 3 := by
  have h := count_shift_add (firstEventB 13) 128 128
  rw [prefix_13_1, chunk_13_1] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_2 : countBelow (fun n => firstEventB 13 (256 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_3 : countBelow (firstEventB 13) 384 = 4 := by
  have h := count_shift_add (firstEventB 13) 256 128
  rw [prefix_13_2, chunk_13_2] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_3 : countBelow (fun n => firstEventB 13 (384 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_4 : countBelow (firstEventB 13) 512 = 4 := by
  have h := count_shift_add (firstEventB 13) 384 128
  rw [prefix_13_3, chunk_13_3] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_4 : countBelow (fun n => firstEventB 13 (512 + n)) 128 = 3 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_5 : countBelow (firstEventB 13) 640 = 7 := by
  have h := count_shift_add (firstEventB 13) 512 128
  rw [prefix_13_4, chunk_13_4] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_5 : countBelow (fun n => firstEventB 13 (640 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_6 : countBelow (firstEventB 13) 768 = 9 := by
  have h := count_shift_add (firstEventB 13) 640 128
  rw [prefix_13_5, chunk_13_5] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_6 : countBelow (fun n => firstEventB 13 (768 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_7 : countBelow (firstEventB 13) 896 = 10 := by
  have h := count_shift_add (firstEventB 13) 768 128
  rw [prefix_13_6, chunk_13_6] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_7 : countBelow (fun n => firstEventB 13 (896 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_8 : countBelow (firstEventB 13) 1024 = 10 := by
  have h := count_shift_add (firstEventB 13) 896 128
  rw [prefix_13_7, chunk_13_7] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_8 : countBelow (fun n => firstEventB 13 (1024 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_9 : countBelow (firstEventB 13) 1152 = 12 := by
  have h := count_shift_add (firstEventB 13) 1024 128
  rw [prefix_13_8, chunk_13_8] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_9 : countBelow (fun n => firstEventB 13 (1152 + n)) 128 = 3 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_10 : countBelow (firstEventB 13) 1280 = 15 := by
  have h := count_shift_add (firstEventB 13) 1152 128
  rw [prefix_13_9, chunk_13_9] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_10 : countBelow (fun n => firstEventB 13 (1280 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_11 : countBelow (firstEventB 13) 1408 = 16 := by
  have h := count_shift_add (firstEventB 13) 1280 128
  rw [prefix_13_10, chunk_13_10] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_11 : countBelow (fun n => firstEventB 13 (1408 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_12 : countBelow (firstEventB 13) 1536 = 16 := by
  have h := count_shift_add (firstEventB 13) 1408 128
  rw [prefix_13_11, chunk_13_11] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_12 : countBelow (fun n => firstEventB 13 (1536 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_13 : countBelow (firstEventB 13) 1664 = 18 := by
  have h := count_shift_add (firstEventB 13) 1536 128
  rw [prefix_13_12, chunk_13_12] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_13 : countBelow (fun n => firstEventB 13 (1664 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_14 : countBelow (firstEventB 13) 1792 = 19 := by
  have h := count_shift_add (firstEventB 13) 1664 128
  rw [prefix_13_13, chunk_13_13] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_14 : countBelow (fun n => firstEventB 13 (1792 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_15 : countBelow (firstEventB 13) 1920 = 19 := by
  have h := count_shift_add (firstEventB 13) 1792 128
  rw [prefix_13_14, chunk_13_14] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_15 : countBelow (fun n => firstEventB 13 (1920 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_16 : countBelow (firstEventB 13) 2048 = 21 := by
  have h := count_shift_add (firstEventB 13) 1920 128
  rw [prefix_13_15, chunk_13_15] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_16 : countBelow (fun n => firstEventB 13 (2048 + n)) 128 = 3 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_17 : countBelow (firstEventB 13) 2176 = 24 := by
  have h := count_shift_add (firstEventB 13) 2048 128
  rw [prefix_13_16, chunk_13_16] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_17 : countBelow (fun n => firstEventB 13 (2176 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_18 : countBelow (firstEventB 13) 2304 = 25 := by
  have h := count_shift_add (firstEventB 13) 2176 128
  rw [prefix_13_17, chunk_13_17] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_18 : countBelow (fun n => firstEventB 13 (2304 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_19 : countBelow (firstEventB 13) 2432 = 27 := by
  have h := count_shift_add (firstEventB 13) 2304 128
  rw [prefix_13_18, chunk_13_18] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_19 : countBelow (fun n => firstEventB 13 (2432 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_20 : countBelow (firstEventB 13) 2560 = 27 := by
  have h := count_shift_add (firstEventB 13) 2432 128
  rw [prefix_13_19, chunk_13_19] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_20 : countBelow (fun n => firstEventB 13 (2560 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_21 : countBelow (firstEventB 13) 2688 = 29 := by
  have h := count_shift_add (firstEventB 13) 2560 128
  rw [prefix_13_20, chunk_13_20] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_21 : countBelow (fun n => firstEventB 13 (2688 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_22 : countBelow (firstEventB 13) 2816 = 29 := by
  have h := count_shift_add (firstEventB 13) 2688 128
  rw [prefix_13_21, chunk_13_21] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_22 : countBelow (fun n => firstEventB 13 (2816 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_23 : countBelow (firstEventB 13) 2944 = 29 := by
  have h := count_shift_add (firstEventB 13) 2816 128
  rw [prefix_13_22, chunk_13_22] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_23 : countBelow (fun n => firstEventB 13 (2944 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_24 : countBelow (firstEventB 13) 3072 = 31 := by
  have h := count_shift_add (firstEventB 13) 2944 128
  rw [prefix_13_23, chunk_13_23] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_24 : countBelow (fun n => firstEventB 13 (3072 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_25 : countBelow (firstEventB 13) 3200 = 32 := by
  have h := count_shift_add (firstEventB 13) 3072 128
  rw [prefix_13_24, chunk_13_24] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_25 : countBelow (fun n => firstEventB 13 (3200 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_26 : countBelow (firstEventB 13) 3328 = 32 := by
  have h := count_shift_add (firstEventB 13) 3200 128
  rw [prefix_13_25, chunk_13_25] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_26 : countBelow (fun n => firstEventB 13 (3328 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_27 : countBelow (firstEventB 13) 3456 = 33 := by
  have h := count_shift_add (firstEventB 13) 3328 128
  rw [prefix_13_26, chunk_13_26] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_27 : countBelow (fun n => firstEventB 13 (3456 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_28 : countBelow (firstEventB 13) 3584 = 35 := by
  have h := count_shift_add (firstEventB 13) 3456 128
  rw [prefix_13_27, chunk_13_27] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_28 : countBelow (fun n => firstEventB 13 (3584 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_29 : countBelow (firstEventB 13) 3712 = 36 := by
  have h := count_shift_add (firstEventB 13) 3584 128
  rw [prefix_13_28, chunk_13_28] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_29 : countBelow (fun n => firstEventB 13 (3712 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_30 : countBelow (firstEventB 13) 3840 = 37 := by
  have h := count_shift_add (firstEventB 13) 3712 128
  rw [prefix_13_29, chunk_13_29] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_30 : countBelow (fun n => firstEventB 13 (3840 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_31 : countBelow (firstEventB 13) 3968 = 39 := by
  have h := count_shift_add (firstEventB 13) 3840 128
  rw [prefix_13_30, chunk_13_30] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_31 : countBelow (fun n => firstEventB 13 (3968 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_32 : countBelow (firstEventB 13) 4096 = 41 := by
  have h := count_shift_add (firstEventB 13) 3968 128
  rw [prefix_13_31, chunk_13_31] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_32 : countBelow (fun n => firstEventB 13 (4096 + n)) 128 = 3 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_33 : countBelow (firstEventB 13) 4224 = 44 := by
  have h := count_shift_add (firstEventB 13) 4096 128
  rw [prefix_13_32, chunk_13_32] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_33 : countBelow (fun n => firstEventB 13 (4224 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_34 : countBelow (firstEventB 13) 4352 = 45 := by
  have h := count_shift_add (firstEventB 13) 4224 128
  rw [prefix_13_33, chunk_13_33] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_34 : countBelow (fun n => firstEventB 13 (4352 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_35 : countBelow (firstEventB 13) 4480 = 46 := by
  have h := count_shift_add (firstEventB 13) 4352 128
  rw [prefix_13_34, chunk_13_34] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_35 : countBelow (fun n => firstEventB 13 (4480 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_36 : countBelow (firstEventB 13) 4608 = 47 := by
  have h := count_shift_add (firstEventB 13) 4480 128
  rw [prefix_13_35, chunk_13_35] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_36 : countBelow (fun n => firstEventB 13 (4608 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_37 : countBelow (firstEventB 13) 4736 = 47 := by
  have h := count_shift_add (firstEventB 13) 4608 128
  rw [prefix_13_36, chunk_13_36] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_37 : countBelow (fun n => firstEventB 13 (4736 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_38 : countBelow (firstEventB 13) 4864 = 48 := by
  have h := count_shift_add (firstEventB 13) 4736 128
  rw [prefix_13_37, chunk_13_37] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_38 : countBelow (fun n => firstEventB 13 (4864 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_39 : countBelow (firstEventB 13) 4992 = 50 := by
  have h := count_shift_add (firstEventB 13) 4864 128
  rw [prefix_13_38, chunk_13_38] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_39 : countBelow (fun n => firstEventB 13 (4992 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_40 : countBelow (firstEventB 13) 5120 = 52 := by
  have h := count_shift_add (firstEventB 13) 4992 128
  rw [prefix_13_39, chunk_13_39] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_40 : countBelow (fun n => firstEventB 13 (5120 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_41 : countBelow (firstEventB 13) 5248 = 53 := by
  have h := count_shift_add (firstEventB 13) 5120 128
  rw [prefix_13_40, chunk_13_40] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_41 : countBelow (fun n => firstEventB 13 (5248 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_42 : countBelow (firstEventB 13) 5376 = 55 := by
  have h := count_shift_add (firstEventB 13) 5248 128
  rw [prefix_13_41, chunk_13_41] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_42 : countBelow (fun n => firstEventB 13 (5376 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_43 : countBelow (firstEventB 13) 5504 = 56 := by
  have h := count_shift_add (firstEventB 13) 5376 128
  rw [prefix_13_42, chunk_13_42] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_43 : countBelow (fun n => firstEventB 13 (5504 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_44 : countBelow (firstEventB 13) 5632 = 58 := by
  have h := count_shift_add (firstEventB 13) 5504 128
  rw [prefix_13_43, chunk_13_43] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_44 : countBelow (fun n => firstEventB 13 (5632 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_45 : countBelow (firstEventB 13) 5760 = 59 := by
  have h := count_shift_add (firstEventB 13) 5632 128
  rw [prefix_13_44, chunk_13_44] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_45 : countBelow (fun n => firstEventB 13 (5760 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_46 : countBelow (firstEventB 13) 5888 = 61 := by
  have h := count_shift_add (firstEventB 13) 5760 128
  rw [prefix_13_45, chunk_13_45] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_46 : countBelow (fun n => firstEventB 13 (5888 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_47 : countBelow (firstEventB 13) 6016 = 63 := by
  have h := count_shift_add (firstEventB 13) 5888 128
  rw [prefix_13_46, chunk_13_46] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_47 : countBelow (fun n => firstEventB 13 (6016 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_48 : countBelow (firstEventB 13) 6144 = 64 := by
  have h := count_shift_add (firstEventB 13) 6016 128
  rw [prefix_13_47, chunk_13_47] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_48 : countBelow (fun n => firstEventB 13 (6144 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_49 : countBelow (firstEventB 13) 6272 = 65 := by
  have h := count_shift_add (firstEventB 13) 6144 128
  rw [prefix_13_48, chunk_13_48] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_49 : countBelow (fun n => firstEventB 13 (6272 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_50 : countBelow (firstEventB 13) 6400 = 66 := by
  have h := count_shift_add (firstEventB 13) 6272 128
  rw [prefix_13_49, chunk_13_49] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_50 : countBelow (fun n => firstEventB 13 (6400 + n)) 128 = 0 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_51 : countBelow (firstEventB 13) 6528 = 66 := by
  have h := count_shift_add (firstEventB 13) 6400 128
  rw [prefix_13_50, chunk_13_50] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_51 : countBelow (fun n => firstEventB 13 (6528 + n)) 128 = 3 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_52 : countBelow (firstEventB 13) 6656 = 69 := by
  have h := count_shift_add (firstEventB 13) 6528 128
  rw [prefix_13_51, chunk_13_51] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_52 : countBelow (fun n => firstEventB 13 (6656 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_53 : countBelow (firstEventB 13) 6784 = 70 := by
  have h := count_shift_add (firstEventB 13) 6656 128
  rw [prefix_13_52, chunk_13_52] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_53 : countBelow (fun n => firstEventB 13 (6784 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_54 : countBelow (firstEventB 13) 6912 = 71 := by
  have h := count_shift_add (firstEventB 13) 6784 128
  rw [prefix_13_53, chunk_13_53] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_54 : countBelow (fun n => firstEventB 13 (6912 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_55 : countBelow (firstEventB 13) 7040 = 73 := by
  have h := count_shift_add (firstEventB 13) 6912 128
  rw [prefix_13_54, chunk_13_54] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_55 : countBelow (fun n => firstEventB 13 (7040 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_56 : countBelow (firstEventB 13) 7168 = 74 := by
  have h := count_shift_add (firstEventB 13) 7040 128
  rw [prefix_13_55, chunk_13_55] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_56 : countBelow (fun n => firstEventB 13 (7168 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_57 : countBelow (firstEventB 13) 7296 = 75 := by
  have h := count_shift_add (firstEventB 13) 7168 128
  rw [prefix_13_56, chunk_13_56] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_57 : countBelow (fun n => firstEventB 13 (7296 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_58 : countBelow (firstEventB 13) 7424 = 77 := by
  have h := count_shift_add (firstEventB 13) 7296 128
  rw [prefix_13_57, chunk_13_57] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_58 : countBelow (fun n => firstEventB 13 (7424 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_59 : countBelow (firstEventB 13) 7552 = 78 := by
  have h := count_shift_add (firstEventB 13) 7424 128
  rw [prefix_13_58, chunk_13_58] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_59 : countBelow (fun n => firstEventB 13 (7552 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_60 : countBelow (firstEventB 13) 7680 = 79 := by
  have h := count_shift_add (firstEventB 13) 7552 128
  rw [prefix_13_59, chunk_13_59] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_60 : countBelow (fun n => firstEventB 13 (7680 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_61 : countBelow (firstEventB 13) 7808 = 80 := by
  have h := count_shift_add (firstEventB 13) 7680 128
  rw [prefix_13_60, chunk_13_60] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_61 : countBelow (fun n => firstEventB 13 (7808 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_62 : countBelow (firstEventB 13) 7936 = 82 := by
  have h := count_shift_add (firstEventB 13) 7808 128
  rw [prefix_13_61, chunk_13_61] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_62 : countBelow (fun n => firstEventB 13 (7936 + n)) 128 = 2 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_63 : countBelow (firstEventB 13) 8064 = 84 := by
  have h := count_shift_add (firstEventB 13) 7936 128
  rw [prefix_13_62, chunk_13_62] at h
  exact h

/-- Kernel computation on one translated 128-input block. -/
theorem chunk_13_63 : countBelow (fun n => firstEventB 13 (8064 + n)) 128 = 1 := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_13_64 : countBelow (firstEventB 13) 8192 = 85 := by
  have h := count_shift_add (firstEventB 13) 8064 128
  rw [prefix_13_63, chunk_13_63] at h
  exact h

/-- Complete period numerator at depth 13. -/
theorem period_count_13 : countBelow (firstEventB 13) (2 ^ 13) = 85 := prefix_13_64

/-- Numerical error bar at depth thirteen, valid at every cutoff. -/
theorem depth_thirteen_error (N : Nat) :
    8192 * countBelow (firstEventB 13) N ≤ N * 85 + 689095 ∧
    N * 85 ≤ 8192 * countBelow (firstEventB 13) N + 689095 := by
  have h := firstEvent_composition_error 13 N
  dsimp only at h
  rw [period_count_13] at h
  simpa only [show (2 : Nat) ^ 13 = 8192 by decide,
    show (8192 - 85 : Nat) = 8107 by decide, show (85 * 8107 : Nat) = 689095 by decide] using h

end Collatz.Research.StoppingAtlas
