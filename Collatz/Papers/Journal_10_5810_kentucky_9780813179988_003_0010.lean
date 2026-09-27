import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Peter H. Reid, "Syracuse University Training and Marriage", 2020.

Title: Syracuse University Training and Marriage

Abstract (from harvested metadata, truncated):
Peppy Dennett and Bill Kinsey spent three months at Syracuse University in training for their teaching assignment in Africa. Their time at Syracuse is discussed, especially the content of the training program. Bill was scheduled for a post in Malawi, so he needed a transfer to allow the marriage and joint posting in Tanzania. Peppy’s mother opposed the marriage at first; she was appalled at the quick decision to wed. She relented and pulled everything together for a wedding, and they were married a few days before leaving for Africa. Peppy’s sister and Peppy’s friends describe their reaction on their first and only meeting with Bill before the couple left for Africa: “We hardly knew him.”

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5810/kentucky/9780813179988.003.0010
-/

namespace Collatz.Papers.Journal_10_5810_kentucky_9780813179988_003_0010

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Peter H. Reid, \"Syracuse University Training and Marriage\", Every Hill a Burial Place, DOI:10.5810/kentucky/9780813179988.003.0010 [2020]."

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

end Collatz.Papers.Journal_10_5810_kentucky_9780813179988_003_0010
