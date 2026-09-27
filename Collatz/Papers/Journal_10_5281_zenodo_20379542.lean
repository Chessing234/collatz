import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Dennis, Knight, "Frontier Closure and a Proposed Computer-Assisted Proof of the Collatz Conjecture via the Five-Lemma Quotient Admission Framework — Proof Package", 2026.

Title: Frontier Closure and a Proposed Computer-Assisted Proof of the Collatz Conjecture via the Five-Lemma Quotient Admission Framework — Proof Package

Abstract (from harvested metadata, truncated):
This repository contains the complete proof package for a proposed computer-assisted proof of the Collatz Conjecture via the Five-Lemma Quotient Admission Framework (Lemmas A–E). The proof is conditional on computational conditions RC1–RC4. Package contents: Main paper and companion documents (PDF) Lean 4 proof skeleton (3,331 build jobs, zero errors; axioms: propext, Classical.choice, Quot.sound only) 33 Python audit scripts (FSM closure, seam audit, gate audit, root tube, Mersenne corridor, D-layer) Proof chain documentation (Documents 93 and 100–127) FSM pointwise closure certificates (5,666 coarse M674 states, all independently certified closed) Entry certificates for refinement rounds 1...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20379542
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20379542

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Dennis, Knight, \"Frontier Closure and a Proposed Computer-Assisted Proof of the Collatz Conjecture via the Five-Lemma Quotient Admission Framework — Proof Package\", Dennis Knight, DOI:10.5281/zenodo.20379542 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_20379542
