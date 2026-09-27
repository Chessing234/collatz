import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hamaji, Shinsuke, "Hidden Variables Induced by Omission: Natural Mathematics and the Collatz Conjecture", 2026.

Title: Hidden Variables Induced by Omission: Natural Mathematics and the Collatz Conjecture

Abstract (from harvested metadata, truncated):
This paper identifies the structural limitations inherent in conventional mathematics, which treats the natural numbers as a pre‑given static set (a global inertial frame) and thereby omits, a priori, the deterministic generative rules of natural numbers (hidden causal variables). This omission renders the internal causal structure of natural numbers opaque and leads to well‑known foundational issues such as the halting problem and the intrusion of non‑standard models. As a case study, we examine the Collatz conjecture. Although the Collatz process consists of three linear maps, the conventional static‑set framework cannot guarantee a bijection onto the trivial loop (1–4–2–1). Because genera...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20060063
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20060063

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hamaji, Shinsuke, \"Hidden Variables Induced by Omission: Natural Mathematics and the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.20060063 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20060063
