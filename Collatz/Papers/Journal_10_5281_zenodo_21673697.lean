import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Nidhal Mghirbi, "Defect‑Area Bounds for Collatz Cycles via Rotation‑Numerator Lifts", 2026.

Title: Defect‑Area Bounds for Collatz Cycles via Rotation‑Numerator Lifts

Abstract (from harvested metadata, truncated):
Let $T(x)=(3x+1)/2^{\nu_2(3x+1)}$ act on positive odd integers. For a hypothetical cycle of period $p$ and total valuation $K$, the balanced rotation defines a defect profile $d_t=\lfloor tK/p\rfloor-S_t\ge 0$ with support $s$, height $H$, and area $E$. When $\gcd(p,K)=1$, a distinguished unit $\xi$ modulo $D=2^K-3^p$ with $\xi^p\equiv 1/2$, $\xi^K\equiv 1/3$ turns integer closure into a sparse exponential relation. We construct an exact lift of that relation to $\mathbb{Z}$ and prove it telescopes to a difference of normalized rotation numerators, $g_a/2^{d_a}-g_{a-\tau}/2^{d_{a-\tau}}$. All $g_a$ being odd, the lift never vanishes; sparsity makes it too small to be a nonzero multiple of $D...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21673697
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21673697

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Nidhal Mghirbi, \"Defect‑Area Bounds for Collatz Cycles via Rotation‑Numerator Lifts\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21673697 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21673697
