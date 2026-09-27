import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Samuel Buya Bonaya, "On the Proof of the Collatz Conjecture", 2026.

Title: On the Proof of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
This paper presents a comprehensive framework for the proof of the Collatz conjecture by analyzing the dynamics of odd integers under the Collatz map. We introduce a parametrization of odd integers that decomposes each number into a power-of-two component and a remainder term, capturing the essential arithmetic structure. By examining the inverse relations and the 2-adic factorization at each iteration, we identify a terminal family of odd integers of the form &lt;i&gt;N&lt;/i&gt;&amp;nbsp;&lt;i&gt;=&lt;/i&gt; 2 2&lt;i&gt;n&lt;/i&gt;-1 3 to which all odd orbits eventually reduce. The arithmetic and dynamical structure at the terminal stage guarantees collapse to 1, thereby establishing that every positive 1 integer reaches 1 under the Collatz iteration. This approach provides a clear and...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.2139/ssrn.6188618
-/

namespace Collatz.Papers.Journal_10_2139_ssrn_6188618

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Samuel Buya Bonaya, \"On the Proof of the Collatz Conjecture\", SSRN Electronic Journal, DOI:10.2139/ssrn.6188618 [2026]."

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

end Collatz.Papers.Journal_10_2139_ssrn_6188618
