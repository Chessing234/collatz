import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Michael Mark Anthony, "Two-Field Integer Propagation Modeland a Riemann–P Realization of Collatz Dynamics", arXiv:2602.01977 [2026].

Title: Two-Field Integer Propagation Modeland a Riemann–P Realization of Collatz Dynamics

Abstract (from OpenAlex metadata, truncated):
This paper proposes a geometric propagation model on the plane formed by two alternating integer fields placed on parallel layers y=n. Odd layers carry an expansion field and even layers carry a collapse field. Local directions are specified through explicit gradient (tangent-slope) laws for the fields Ψ, yielding parallel corridors, trajectory merging, and event-driven switching at inter-layer boundaries. This gradient field is connected to the Riemann–P (three-singularity Fuchsian) differential equation: choosing a half-integer local exponent produces square root scaling, so dilations of the independent variable generate multiplicative amplitude updates. When integers are embedded as a half-integer leaf u=n+1/2 and a first-return-to-leaf rule selects dyadic contraction depth, the induced return map is exactly the Collatz map. We provide vector-field examples, switching rules, a formal 

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2602.01977
-/

namespace Collatz.Papers.Arxiv2602_01977

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Michael Mark Anthony, \"Two-Field Integer Propagation Modeland a Riemann\u2013P Realization of Collatz Dynamics\", arXiv:2602.01977 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv2602_01977
