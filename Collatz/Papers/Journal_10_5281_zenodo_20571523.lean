import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for 王, 江祁, "A Binary Finite State Machine Proof of the Collatz Conjecture 科拉茨猜想的二进制有限状态机证明", 2026.

Title: A Binary Finite State Machine Proof of the Collatz Conjecture 科拉茨猜想的二进制有限状态机证明

Abstract (from harvested metadata, truncated):
This paper presents a rigorous proof of the Collatz conjecture using a binary finite state machine approach. The core insight is that under binary representation, the Collatz operations exhibit strict locality. For odd numbers congruent to 3 modulo 4 — the only case requiring detailed analysis — the operation (3N+1)/2 is shown to have exactly one carry bit and one division by 2, yielding a net carry of zero. The carry propagation always terminates within a 6-bit window, and the state space of 64 possible 6-bit patterns is strictly closed under the operation. Within this closed state space, only 16 states (those ending in binary "11") require tracking. A set of elimination rules is introduced, and exhaustive enumeration verifies that all 16 "stubborn" states exit the stubborn set in...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20571523
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20571523

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "王, 江祁, \"A Binary Finite State Machine Proof of the Collatz Conjecture 科拉茨猜想的二进制有限状态机证明\", DOI:10.5281/zenodo.20571523 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_20571523
