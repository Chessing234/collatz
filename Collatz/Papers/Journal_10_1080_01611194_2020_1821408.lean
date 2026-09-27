import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Türker Tuncer and Huseyin Yuce Kurum, "A novel Collatz conjecture-based digital image watermarking method", 2020.

Title: A novel Collatz conjecture-based digital image watermarking method

Abstract (from harvested metadata, truncated):
In this research, a novel Collatz conjecture-based image transformation and a modified logistic map are used for digital image watermarking. The proposed modified logistic map is utilized as a pseudo-random number generator (PRNG) to select the pixel to be watermarked. The host image is divided into nonoverlapping blocks, for instance, 2 × 2, 3 × 3, 4 × 4, 8 × 8, and 10 × 10 size blocks. A Collatz transformation is used on the selected pixel to generate a Collatz value because watermark embedding and extraction processes are implemented on the Collatz values. Evaluation criteria, such as visual quality, payload capacity, robustness, and execution time have been used to measure the performance of the proposed method. The results obtained and calculated clearly show that the proposed...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1080/01611194.2020.1821408
-/

namespace Collatz.Papers.Journal_10_1080_01611194_2020_1821408

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Türker Tuncer and Huseyin Yuce Kurum, \"A novel Collatz conjecture-based digital image watermarking method\", Cryptologia, DOI:10.1080/01611194.2020.1821408 [2020]."

/-- Recorded main claim shell (structural); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Journal_10_1080_01611194_2020_1821408
