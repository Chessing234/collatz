import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Tomasz R. Działa, "Collatz-Weyl Generators: High Quality and High Throughput Parameterized Pseudorandom Number Generators", arXiv:2312.17043 [2023].

Title: Collatz-Weyl Generators: High Quality and High Throughput Parameterized Pseudorandom Number Generators

Abstract (truncated):
We introduce the Collatz-Weyl Generators, a family of uniform pseudorandom number generators (PRNGs) which are based on generalized Collatz mappings, derived from the Collatz conjecture and Weyl sequences. The high-quality statistical properties of our generators is demonstrated by the fact that they pass stringent randomness tests used by the research and standardization community. The proposed Collatz-Weyl Generators have a number of important properties, including solid mathematical foundations, enablement of high throughput and low latency implementation, small code and/or ASIC size, enablement of producing multiple independent streams and potential of support of cryptographic applications.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2312.17043
-/

namespace MathlibAttack.Papers.Arxiv2312_17043

open MathlibAttack.Papers

def citation : String := "Tomasz R. Dzia\u0142a, \"Collatz-Weyl Generators: High Quality and High Throughput Parameterized Pseudorandom Number Generators\", arXiv:2312.17043 [2023]."

/-- Recorded claim shell (generalization); paper theorem not proved.
Placeholder equals the Collatz conjecture proposition. -/
def mainStatement : Prop := CollatzConjecture

theorem step_one_eq : step 1 = 4 := step_one
theorem step_two_eq : step 2 = 1 := step_two

end MathlibAttack.Papers.Arxiv2312_17043
