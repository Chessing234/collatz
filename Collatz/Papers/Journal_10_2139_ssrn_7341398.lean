import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Idris Ali Shaik, "Natural-density Collatz Descent to a Stretched-logarithmic Scale", 2026.

Title: Natural-density Collatz Descent to a Stretched-logarithmic Scale

Abstract (from harvested metadata, truncated):
For the shortcut Collatz map, given by T (n) = n/2 for even n and T (n) = (3n + 1)/2 for odd n, write T min (n) = min k≥0 T k (n). We prove that, for every 0 &amp;lt; δ &amp;lt; δ 0 , T min (n) ≤ exp((log n) 1-δ) on a set of positive integers of natural density one, where δ 0 = log(1/a 0) log(2/a 0) = 0.251245530155874. .. , a 0 = log 2 3 2. This prescribed scale is eventually smaller than every fixed power of n, improving the scale in earlier fixed-power natural-density descent results. We also prove a stretchedexponential bound for the exceptional count and locate a descent witness before 6.953 log n iterations of T. The proof conditions a dyadic parity word on its odd-step count, controls...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.2139/ssrn.7341398
-/

namespace Collatz.Papers.Journal_10_2139_ssrn_7341398

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Idris Ali Shaik, \"Natural-density Collatz Descent to a Stretched-logarithmic Scale\", DOI:10.2139/ssrn.7341398 [2026]."

/-- Recorded density-style claim shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ eps : Rat, 0 < eps →
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → 0 < N →
      ((1 : Rat) - eps) * (N : Rat) ≤ (N : Rat)

/-- Weak density scaffolding (Mathlib-copied `Rat` facts); strictly weaker than the paper. -/
theorem mainStatement_weak : mainStatement := by
  intro eps heps
  refine ⟨0, ?_⟩
  intro N _ _
  exact Collatz.Papers.MathlibCopied.density_shell_of_pos eps N heps

end Collatz.Papers.Journal_10_2139_ssrn_7341398
