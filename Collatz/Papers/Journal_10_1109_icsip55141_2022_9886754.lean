import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Aimee D. Molato et al., "LSB-based Random Embedding Image Steganography Technique Using Modified Collatz Conjecture", 2022.

Title: LSB-based Random Embedding Image Steganography Technique Using Modified Collatz Conjecture

Abstract (from harvested metadata, truncated):
With digital communication breakthroughs, reliable data security and secure sharing of secret information remain a challenge. LSB is considered one of the most used techniques in steganography because of its simple and easy implementation. However, the algorithm can easily be broken down, and the attacker can obtain the secret message due to its simplicity. This paper combines Diffie-Hellman Key Exchange with a modified Collatz Conjecture to generate unique random numbers. The generated random numbers are used to identify the unique pixel locations where the secret message will be embedded. The simulation results using INRIA Holiday datasets yielded PSNR and SSIM mean values of 69.24 and 0.9999, respectively, which are favorable enough to conclude that the employed method generates highly...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1109/icsip55141.2022.9886754
-/

namespace Collatz.Papers.Journal_10_1109_icsip55141_2022_9886754

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Aimee D. Molato et al., \"LSB-based Random Embedding Image Steganography Technique Using Modified Collatz Conjecture\", 2022 7th International Conference on Signal and Image Processing (ICSIP), DOI:10.1109/icsip55141.2022.9886754 [2022]."

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

end Collatz.Papers.Journal_10_1109_icsip55141_2022_9886754
