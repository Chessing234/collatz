import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Diego Renza et al., "Encrypted audio dataset based on the Collatz conjecture", 2019.

Title: Encrypted audio dataset based on the Collatz conjecture

Abstract (from harvested metadata, truncated):
In information security, one way to keep a secret content is through encryption. The objective is to alter the content so that it is not intelligible, and therefore only the intended user can reveal the secret content. With the aim to provide examples of encrypted audio data, we applied a novel method of encryption based on the Collatz conjecture in five hundred speech recordings (50 speakers, 10 different messages), and then five hundred encrypted audio files were obtained. The main characteristics of our encrypted recordings are as follows: the spectrogram is quasi-uniform, histograms have a repetitive pattern, average of samples is around −0.4, standard deviation is around 0.55; Shannon entropy is around 7.5 (for 8-bits per sample). The novelty of the results consists in obtaining a...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1016/j.dib.2019.104537
-/

namespace Collatz.Papers.Journal_10_1016_j_dib_2019_104537

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Diego Renza et al., \"Encrypted audio dataset based on the Collatz conjecture\", Data in Brief, DOI:10.1016/j.dib.2019.104537 [2019]."

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

end Collatz.Papers.Journal_10_1016_j_dib_2019_104537
