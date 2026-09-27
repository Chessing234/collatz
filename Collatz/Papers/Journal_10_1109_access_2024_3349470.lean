import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Abeer Al-Hyari et al., "Generating Powerful Encryption Keys for Image Cryptography With Chaotic Maps by Incorporating Collatz Conjecture", 2024.

Title: Generating Powerful Encryption Keys for Image Cryptography With Chaotic Maps by Incorporating Collatz Conjecture

Abstract (from harvested metadata, truncated):
In recent years, the chaotic logistic map key (CLMK) has been widely used for image encryption due to its ability to generate random and unpredictable sequences of numbers. The CLMK algorithm uses the chaotic logistic map to generate a key stream, which is then used to encrypt the plaintext image. This study proposes an image encryption scheme based on CLMK, Collatz Conjecture, and indexing techniques; it uses a private key of a 15-digit size that is parsed in a novel way to generate a considerable keyspace reaches up to 297. The Collatz Conjecture generator is used to create variable length sequences that are used to generate the Chaotic parametersr1,r2,x1, andx2; these parameters are used to create a 2D CLMK for encrypting each color channel and a 1D vector that is used for permeation,...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1109/access.2024.3349470
-/

namespace Collatz.Papers.Journal_10_1109_access_2024_3349470

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Abeer Al-Hyari et al., \"Generating Powerful Encryption Keys for Image Cryptography With Chaotic Maps by Incorporating Collatz Conjecture\", IEEE Access, DOI:10.1109/access.2024.3349470 [2024]."

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

end Collatz.Papers.Journal_10_1109_access_2024_3349470
