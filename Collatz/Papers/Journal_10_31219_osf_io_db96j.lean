import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kavak, Mesut, "Collatz Problemi İspatı", 2023.

Title: Collatz Problemi İspatı

Abstract (from harvested metadata, truncated):
Pozitif bir tam sayı seçildiğinde, sayı çift ise 2'ye bölünür; aksi takdirde 3 ile çarpılır ve bundan sonra sonuca 1 eklenir. Sonucun tek veya çift olması şartından dolayı problemin gerekli seçeneği ile aynı işlem tekrarlandığında, 0 ve 1'den farklı olan her pozitif tamsayı 1'e indirgenebilir mi?

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.31219/osf.io/db96j
-/

namespace Collatz.Papers.Journal_10_31219_osf_io_db96j

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kavak, Mesut, \"Collatz Problemi İspatı\", DOI:10.31219/osf.io/db96j [2023]."

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

end Collatz.Papers.Journal_10_31219_osf_io_db96j
