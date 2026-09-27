import CollatzTargetDensity.BinaryProfileReturn

/-! Exact rising profile returns; checked by ordinary kernel reduction. -/
namespace CollatzTargetDensity.BinaryProfileReturn

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def return11 : List Chunk := [
  ⟨11, 13, 3, [⟨11, 17, 1, 1⟩, ⟨17, 13, 2, 1⟩]⟩
]

def return521 : List Chunk := [
  ⟨521, 391, 261, [⟨521, 391, 2, 1⟩]⟩,
  ⟨391, 661, 49, [⟨391, 587, 1, 1⟩, ⟨587, 881, 1, 1⟩, ⟨881, 661, 2, 1⟩]⟩,
  ⟨661, 31, 331, [⟨661, 31, 6, 1⟩]⟩,
  ⟨31, 121, 1, [⟨31, 47, 1, 1⟩, ⟨47, 71, 1, 1⟩, ⟨71, 107, 1, 1⟩, ⟨107, 161, 1, 1⟩, ⟨161, 121, 2, 1⟩]⟩,
  ⟨121, 91, 61, [⟨121, 91, 2, 1⟩]⟩,
  ⟨91, 103, 23, [⟨91, 137, 1, 1⟩, ⟨137, 103, 2, 1⟩]⟩,
  ⟨103, 175, 13, [⟨103, 155, 1, 1⟩, ⟨155, 233, 1, 1⟩, ⟨233, 175, 2, 1⟩]⟩,
  ⟨175, 445, 11, [⟨175, 263, 1, 1⟩, ⟨263, 395, 1, 1⟩, ⟨395, 593, 1, 1⟩, ⟨593, 445, 2, 1⟩]⟩,
  ⟨445, 167, 223, [⟨445, 167, 3, 1⟩]⟩,
  ⟨167, 283, 21, [⟨167, 251, 1, 1⟩, ⟨251, 377, 1, 1⟩, ⟨377, 283, 2, 1⟩]⟩,
  ⟨283, 319, 71, [⟨283, 425, 1, 1⟩, ⟨425, 319, 2, 1⟩]⟩,
  ⟨319, 911, 5, [⟨319, 479, 1, 1⟩, ⟨479, 719, 1, 1⟩, ⟨719, 1079, 1, 1⟩, ⟨1079, 1619, 1, 1⟩, ⟨1619, 2429, 1, 1⟩, ⟨2429, 911, 3, 1⟩]⟩,
  ⟨911, 577, 57, [⟨911, 1367, 1, 1⟩, ⟨1367, 2051, 1, 1⟩, ⟨2051, 3077, 1, 1⟩, ⟨3077, 577, 4, 1⟩]⟩
]

def return186239 : List Chunk := [
  ⟨186239, 795521, 1455, [⟨186239, 279359, 1, 1⟩, ⟨279359, 419039, 1, 1⟩, ⟨419039, 628559, 1, 1⟩, ⟨628559, 942839, 1, 1⟩, ⟨942839, 1414259, 1, 1⟩, ⟨1414259, 2121389, 1, 1⟩, ⟨2121389, 795521, 3, 1⟩]⟩,
  ⟨795521, 596641, 397761, [⟨795521, 596641, 2, 1⟩]⟩,
  ⟨596641, 447481, 298321, [⟨596641, 447481, 2, 1⟩]⟩,
  ⟨447481, 335611, 223741, [⟨447481, 335611, 2, 1⟩]⟩,
  ⟨335611, 377563, 83903, [⟨335611, 503417, 1, 1⟩, ⟨503417, 377563, 2, 1⟩]⟩,
  ⟨377563, 424759, 94391, [⟨377563, 566345, 1, 1⟩, ⟨566345, 424759, 2, 1⟩]⟩,
  ⟨424759, 358391, 53095, [⟨424759, 637139, 1, 1⟩, ⟨637139, 955709, 1, 1⟩, ⟨955709, 358391, 3, 1⟩]⟩,
  ⟨358391, 302393, 44799, [⟨358391, 537587, 1, 1⟩, ⟨537587, 806381, 1, 1⟩, ⟨806381, 302393, 3, 1⟩]⟩,
  ⟨302393, 226795, 151197, [⟨302393, 226795, 2, 1⟩]⟩,
  ⟨226795, 255145, 56699, [⟨226795, 340193, 1, 1⟩, ⟨340193, 255145, 2, 1⟩]⟩,
  ⟨255145, 191359, 127573, [⟨255145, 191359, 2, 1⟩]⟩
]

theorem small_return_checked : returnCheck 2 11 13 return11 = true := by decide

theorem sparse_return_checked : returnCheck 4 521 577 return521 = true := by decide

theorem returns_up_to_five_checked :
    (List.range 5).all (fun j => returnCheck (j + 1) 186239 191359 return186239) = true := by
  decide

theorem return_checked_of_width {k : ℕ} (hk : 1 ≤ k) (hK : k ≤ 5) :
    returnCheck k 186239 191359 return186239 = true := by
  have h := List.all_eq_true.mp returns_up_to_five_checked (k - 1)
    (List.mem_range.mpr (by omega))
  simpa [show k - 1 + 1 = k by omega] using h

/-- A nonlinear function of the full histogram, monotone in integer size
at each fixed histogram, cannot strictly decrease at every run checkpoint. -/
theorem no_strict_checkpoint_descent (k : ℕ) (hk : 1 ≤ k) (hK : k ≤ 5)
    (F : Histogram → ℕ → ℝ) (hF : ∀ p, Monotone (F p)) :
    ¬(∀ n, 1 < n → Odd n →
      F (histogram k (checkpoint n)) (checkpoint n) < F (histogram k n) n) :=
  checked_return_not_strict (return_checked_of_width hk hK) F hF

/-- Strict dependence on size forces an increasing checkpoint somewhere. -/
theorem no_nonincreasing_checkpoint_potential (k : ℕ) (hk : 1 ≤ k) (hK : k ≤ 5)
    (F : Histogram → ℕ → ℝ) (hF : ∀ p, StrictMono (F p)) :
    ¬(∀ n, 1 < n → Odd n →
      F (histogram k (checkpoint n)) (checkpoint n) ≤ F (histogram k n) n) :=
  checked_return_not_nonincreasing (return_checked_of_width hk hK) F hF

end CollatzTargetDensity.BinaryProfileReturn
