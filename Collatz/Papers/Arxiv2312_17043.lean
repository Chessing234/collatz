import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Tomasz R. Działa, "Collatz-Weyl Generators: High Quality and High Throughput Parameterized Pseudorandom Number Generators", arXiv:2312.17043 [2023].

Title: Collatz-Weyl Generators: High Quality and High Throughput Parameterized Pseudorandom Number Generators

Abstract (from OpenAlex metadata, truncated):
We introduce the Collatz-Weyl Generators, a family of uniform pseudorandom number generators (PRNGs) which are based on generalized Collatz mappings, derived from the Collatz conjecture and Weyl sequences. The high-quality statistical properties of our generators is demonstrated by the fact that they pass stringent randomness tests used by the research and standardization community. The proposed Collatz-Weyl Generators have a number of important properties, including solid mathematical foundations, enablement of high throughput and low latency implementation, small code and/or ASIC size, enablement of producing multiple independent streams and potential of support of cryptographic applications.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2312.17043
-/

namespace Collatz.Papers.Arxiv2312_17043

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Tomasz R. Dzia\u0142a, \"Collatz-Weyl Generators: High Quality and High Throughput Parameterized Pseudorandom Number Generators\", arXiv:2312.17043 [2023]."

/-- Recorded main claim shell (generalization); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv2312_17043
