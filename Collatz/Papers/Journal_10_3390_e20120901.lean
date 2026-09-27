import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Dora M. Ballesteros et al., "A Novel Image Encryption Scheme Based on Collatz Conjecture", 2018.

Title: A Novel Image Encryption Scheme Based on Collatz Conjecture

Abstract (from harvested metadata, truncated):
Image encryption methods aim to protect content privacy. Typically, they encompass scrambling and diffusion. Every pixel of the image is permuted (scrambling) and its value is transformed according to a key (diffusion). Although several methods have been proposed in the literature, some of them have been cryptanalyzed. In this paper, we present a novel method that deviates the traditional schemes. We use variable length codes based on Collatz conjecture for transforming the content of the image into non-intelligible audio; therefore, scrambling and diffusion processes are performed simultaneously in a non-linear way. With our method, different ciphered audio is obtained every time, and it depends exclusively on the selected key (the size of the key space equal to 8 . 57 × 10 506 )....

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.3390/e20120901
-/

namespace Collatz.Papers.Journal_10_3390_e20120901

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Dora M. Ballesteros et al., \"A Novel Image Encryption Scheme Based on Collatz Conjecture\", Entropy, DOI:10.3390/e20120901 [2018]."

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

end Collatz.Papers.Journal_10_3390_e20120901
