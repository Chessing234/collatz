import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hamad Mousa A. Aljassas and Sreela Sasi, "Performance Evaluation of Proof-of-Work and Collatz Conjecture Consensus Algorithms", 2019.

Title: Performance Evaluation of Proof-of-Work and Collatz Conjecture Consensus Algorithms

Abstract (from harvested metadata, truncated):
Blockchain is the underlying technology of Bitcoin that allows a peer-to-peer distributed ledger with security and immutability. The core of a blockchain is the consensus mechanism that sets the rule for nodes in handling the shared data. Implementation of the consensus algorithm depends on the nature of targeted business environment. In this research, the performance of two consensus algorithms, Proof-of-Work (PoW) and Proof-of-Collatz Conjecture (PCC), are studied in the context of a private blockchain. A quantitative analysis on the execution time, deployment time, and latency time are done for 1, 10, 100, 1000, and 10000 transactions and the results are presented. The results shows that PCC takes only (1/1000)thof the execution time that is required for PoW for these different sets of...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1109/cais.2019.8769514
-/

namespace Collatz.Papers.Journal_10_1109_cais_2019_8769514

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hamad Mousa A. Aljassas and Sreela Sasi, \"Performance Evaluation of Proof-of-Work and Collatz Conjecture Consensus Algorithms\", DOI:10.1109/cais.2019.8769514 [2019]."

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

end Collatz.Papers.Journal_10_1109_cais_2019_8769514
