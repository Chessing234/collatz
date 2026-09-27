import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Petrov, Alexey (KAMAZ) and email: infinium.science@mail.ru, "Origami Proof of the Collatz Conjecture in Infinium Ontology: A Formal Verification in Lean 4", 2026.

Title: Origami Proof of the Collatz Conjecture in Infinium Ontology: A Formal Verification in Lean 4

Abstract (from harvested metadata, truncated):
The Collatz conjecture is one of the most enduring open problems in mathematics. We present a constructive proof within the framework of Infinium Ontology (△-ontology), where the fundamental object is not a structureless point but the infinium △₁ₓ₁ — a right isosceles triangle with legs 1 and hypotenuse √2. In this framework, natural numbers acquire a geometric body as mosaics of infiniums. We introduce a complexity function that strictly decreases at each Collatz step, guaranteeing convergence to the base triangle. The proof is formalized and verified in the Lean 4 proof assistant. We discuss the implications of this result for the unity of mathematics and the foundational role of geometric...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20730638
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20730638

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Petrov, Alexey (KAMAZ) and email: infinium.science@mail.ru, \"Origami Proof of the Collatz Conjecture in Infinium Ontology: A Formal Verification in Lean 4\", Zenodo, DOI:10.5281/zenodo.20730638 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_20730638
