import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Aimee D. Molato and Fredilyn B. Calanda, "A Secured LSB-Based Image Steganography using Modified Collatz Conjecture", 2023.

Title: A Secured LSB-Based Image Steganography using Modified Collatz Conjecture

Abstract (from harvested metadata, truncated):
This research paper presents a novel approach to improving the strength of Least Significant Bit (LSB) embedding in steganography through the use of the Collatz Conjecture. LSB image steganography is commonly employed due to its simplicity of implementation. The technique involves directly replacing the message bit into the LSB of an image in a sequential manner. However, this simple technique poses a problem in LSB steganography due to its vulnerability to detection by statistical attacks. To address this issue, the study focuses on the modification of the Collatz Conjecture structure to generate random numbers for the random placement of encrypted message bits. The randomness of the generated numbers was evaluated using the NIST Test Suite, which confirmed their truly random nature. The...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1109/icaccs57279.2023.10113029
-/

namespace Collatz.Papers.Journal_10_1109_icaccs57279_2023_10113029

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Aimee D. Molato and Fredilyn B. Calanda, \"A Secured LSB-Based Image Steganography using Modified Collatz Conjecture\", DOI:10.1109/icaccs57279.2023.10113029 [2023]."

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

end Collatz.Papers.Journal_10_1109_icaccs57279_2023_10113029
