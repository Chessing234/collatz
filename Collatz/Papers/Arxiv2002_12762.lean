import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Maxwell C. Siegel, "Fourier Analysis of the Parity-Vector Parameterization of the Generalized Collatz px+1 maps", arXiv:2002.12762 [2020].

Title: Fourier Analysis of the Parity-Vector Parameterization of the Generalized Collatz px+1 maps

Abstract (from OpenAlex metadata, truncated):
Let p be an odd prime, and consider the map H_p which sends an integer x to either x/2 or (px+1)/2 depending on whether x is even or odd. The values at x=0 of arbitrary composition sequences of the maps x/2 and (px+1)/2 can be parameterized over the 2-adic integers (Z2) leading to a continuous function from Z2 to Zp which the author calls the "characteristic function" (or "numen") of H_p. Lipschitz-type estimates are given for the characteristic function when p-1 is a power of 2 and 2 is a primitive root mod p, and it is shown that the set of periodic points of H_p is equal to the set of (rational) integer values attained by the characteristic function over Z2. Additionally, although the pre-image of R under the characteristic function has zero Haar measure in the Z2, by pre-composing the characteristic function with an appropriately selected self-embedding of Z2, one can perform Fourier

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2002.12762
-/

namespace Collatz.Papers.Arxiv2002_12762

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Maxwell C. Siegel, \"Fourier Analysis of the Parity-Vector Parameterization of the Generalized Collatz px+1 maps\", arXiv:2002.12762 [2020]."

/-- Recorded nontrivial-cycle exclusion shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ n : Nat, 1 < n → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial cycle through `1` returns after three steps. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩


end Collatz.Papers.Arxiv2002_12762
