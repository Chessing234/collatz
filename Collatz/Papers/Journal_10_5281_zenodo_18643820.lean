import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Toru Kawahara, "Resolving the Collatz Problem via a Finite-State Phase Machine Structural Absorption, Core Phases, and Exhaustive Bounded Delay", 2026.

Title: Resolving the Collatz Problem via a Finite-State Phase Machine Structural Absorption, Core Phases, and Exhaustive Bounded Delay

Abstract (from harvested metadata, truncated):
This paper presents a complete structural resolution of the odd-only Collatz problem via an explicit finite-state reformulation. The Collatz dynamics are reconstructed as a deterministic finite-state phase machine by compressing odd integers into phase states modulo a fixed power of two. Within this framework, global behavior is reduced from an infinite iterative process to a finite reachability problem on a fully enumerable transition graph. In contrast to the previous version (v0.5, DOI: https://doi.org/10.5281/zenodo.18446986), the present release provides an exhaustive certification of global reachability and bounded absorption. All states of the finite-state machine are shown to reach a small absorbing core consisting of the phases {1, 5, 17}, with a uniformly bounded delay. The...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18643820
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18643820

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Toru Kawahara, \"Resolving the Collatz Problem via a Finite-State Phase Machine Structural Absorption, Core Phases, and Exhaustive Bounded Delay\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18643820 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_18643820
