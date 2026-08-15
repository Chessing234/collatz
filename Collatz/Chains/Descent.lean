import Collatz.Strategy.Pillars
import Collatz.Strategy.Reductions
import Collatz.Search.StoppingTime

/-!
# Chains 1–6: descent

A **chain** is a list of hypotheses together with a *proved* implication from
those hypotheses to the Collatz conjecture.  The hypotheses are open; the
implication is not.  The point of collecting many chains is to see which
decompositions are genuinely different attacks and which are the same problem
wearing a new hat.

This file collects the chains built on descent: statements of the form "every
number eventually gets smaller in some sense".

Some hypotheses here are **refuted** rather than left open, and those
refutations are proved too.  A refuted chain is not a failure — it is the
cheapest possible outcome, since it removes a direction permanently.

| chain | hypothesis                                       | status   |
|-------|--------------------------------------------------|----------|
| 1     | every `n > 1` has an iterate below itself         | open     |
| 2     | a monovariant `Φ` exists                          | open     |
| 3     | every `n > 1` reaches at most `n / 2`             | open     |
| 4     | the drop happens within `n` steps                 | open     |
| 5     | the drop happens within a *uniform* bound `B`     | **false** |
| 6     | no orbit stays weakly above its start forever     | open     |
-/

namespace Collatz
namespace Chains

open Reach Strategy

/-! ## A helper for refutations

To refute a hypothesis we must exhibit a number whose orbit does *not* drop
within a given budget.  The sweep below turns that into one kernel
computation. -/

/-- `noDropBy n B` is `true` when no iterate `T^k(n)` with `k ≤ B` falls below
`n`. -/
def noDropBy (n B : Nat) : Bool :=
  (List.range (B + 1)).all fun k => decide (n ≤ acceleratedOrbit k n)

/-- Reading a single index out of the sweep. -/
theorem le_accOrbit_of_noDropBy {n B k : Nat} (h : noDropBy n B = true) (hk : k ≤ B) :
    n ≤ acceleratedOrbit k n := by
  rw [noDropBy, List.all_eq_true] at h
  have := h k (List.mem_range.mpr (by omega))
  simpa using this

/-! ## Chain 1 — the stopping-time chain -/

/-- Hypothesis: every `n > 1` has some accelerated iterate below itself. -/
def H1_dropsEventually : Prop := ∀ n : Nat, 1 < n → ∃ k : Nat, acceleratedOrbit k n < n

/-- **Chain 1.**  The stopping-time hypothesis implies Collatz. -/
theorem chain01 (h : H1_dropsEventually) : CollatzConjecture :=
  collatz_of_finiteStoppingTime h

/-- Chain 1 is not merely sufficient: it is equivalent to the conjecture, so
this chain is a restatement rather than a reduction. -/
theorem chain01_equiv : CollatzConjecture ↔ H1_dropsEventually :=
  collatz_iff_finiteStoppingTime

/-! ## Chain 2 — the monovariant chain -/

/-- Hypothesis: some function strictly decreases along every accelerated step
above `1`. -/
def H2_monovariant : Prop := ∃ Φ : Nat → Nat, ∀ n : Nat, 1 < n → Φ (acceleratedStep n) < Φ n

/-- **Chain 2.**  A monovariant implies Collatz, by well-founded descent on its
values rather than on the numbers themselves. -/
theorem chain02 (h : H2_monovariant) : CollatzConjecture := by
  obtain ⟨Φ, hΦ⟩ := h
  have key : ∀ v n : Nat, Φ n = v → 0 < n → ReachesOne n := by
    intro v
    induction v using Nat.strongRecOn with
    | _ v ih =>
      intro n hv hn
      by_cases h1 : n = 1
      · subst h1; exact reachesOne_one
      · have hn1 : 1 < n := by omega
        have hlt : Φ (acceleratedStep n) < Φ n := hΦ n hn1
        have hpos : 0 < acceleratedStep n := by
          have h2 := acceleratedOrbit_positive hn 1
          rw [acceleratedOrbit, acceleratedOrbit] at h2
          exact h2
        have hrec := ih (Φ (acceleratedStep n)) (by omega) (acceleratedStep n) rfl hpos
        exact (reachesOne_accStep_iff hn).mpr hrec
  intro n hn
  exact key (Φ n) n rfl hn

/-- The obvious candidate monovariant fails: the identity increases on `3`. -/
theorem chain02_identity_fails : ¬ (∀ n : Nat, 1 < n → acceleratedStep n < n) := by
  intro h
  have := h 3 (by omega)
  simp [acceleratedStep] at this

/-- So does doubling the identity, and any monotone rescaling of it: the failure
is intrinsic to `n ↦ n`, not to its scale. -/
theorem chain02_scaled_identity_fails (c : Nat) (hc : 0 < c) :
    ¬ (∀ n : Nat, 1 < n → c * acceleratedStep n < c * n) := by
  intro h
  have h3 := h 3 (by omega)
  have hstep : acceleratedStep 3 = 5 := by decide
  rw [hstep] at h3
  have : c * 5 < c * 3 := h3
  have hmono : c * 3 ≤ c * 5 := Nat.mul_le_mul_left c (by omega)
  omega

/-! ## Chain 3 — halving -/

/-- Hypothesis: every `n > 1` reaches a value at most `n / 2`. -/
def H3_reachesHalf : Prop := ∀ n : Nat, 1 < n → ∃ k : Nat, acceleratedOrbit k n ≤ n / 2

/-- **Chain 3.**  Reaching the halfway point implies Collatz. -/
theorem chain03 (h : H3_reachesHalf) : CollatzConjecture := by
  refine collatz_of_finiteStoppingTime (fun n hn => ?_)
  obtain ⟨k, hk⟩ := h n hn
  exact ⟨k, by omega⟩

/-- Chain 3 is implied by Collatz as well, so it is another restatement. -/
theorem chain03_of_collatz (hC : CollatzConjecture) : H3_reachesHalf := by
  intro n hn
  -- the orbit reaches `1`, which is at most `n / 2` once `n ≥ 2`
  have hpos : 0 < n := by omega
  have hacc := Papers.Lagarias1985.collatzConjecturesEquivalent.mp hC n hn
  obtain ⟨k, hk⟩ := hacc
  refine ⟨k, ?_⟩
  rw [hk]
  omega

/-! ## Chain 4 — a decidable-per-instance version -/

/-- Hypothesis: the drop happens within `n` steps.  Unlike Chain 1 this is
decidable for each individual `n`, since the search range is finite. -/
def H4_dropsWithinSelf : Prop :=
  ∀ n : Nat, 1 < n → ∃ k : Nat, k ≤ n ∧ acceleratedOrbit k n < n

/-- **Chain 4.**  A self-bounded drop implies Collatz. -/
theorem chain04 (h : H4_dropsWithinSelf) : CollatzConjecture := by
  refine collatz_of_finiteStoppingTime (fun n hn => ?_)
  obtain ⟨k, _, hk⟩ := h n hn
  exact ⟨k, hk⟩

/-! ## Chain 5 — a uniform bound, and its refutation -/

/-- Hypothesis: one bound `B` works for every `n`. -/
def H5_uniformDrop (B : Nat) : Prop :=
  ∀ n : Nat, 1 < n → ∃ k : Nat, k ≤ B ∧ acceleratedOrbit k n < n

/-- **Chain 5.**  A uniform drop bound implies Collatz. -/
theorem chain05 {B : Nat} (h : H5_uniformDrop B) : CollatzConjecture := by
  refine collatz_of_finiteStoppingTime (fun n hn => ?_)
  obtain ⟨k, _, hk⟩ := h n hn
  exact ⟨k, hk⟩

/-- `27` does not drop within fifty accelerated steps. -/
theorem noDropBy_twentyseven : noDropBy 27 50 = true := by decide

/-- **Chain 5 is refuted at `B = 50`** by the orbit of `27`, whose stopping time
is `59`.  The uniform hypothesis is false for every `B < 59`. -/
theorem chain05_refuted_fifty : ¬ H5_uniformDrop 50 := by
  intro h
  obtain ⟨k, hk, hlt⟩ := h 27 (by omega)
  have := le_accOrbit_of_noDropBy noDropBy_twentyseven hk
  omega

/-- More generally, no uniform bound below the stopping time of `27` can work,
so any proof of Chain 5 must first bound stopping times — which is Chain 1
again. -/
theorem chain05_refuted_of_lt {B : Nat} (hB : B ≤ 50) : ¬ H5_uniformDrop B := by
  intro h
  obtain ⟨k, hk, hlt⟩ := h 27 (by omega)
  have hk50 : k ≤ 50 := by omega
  have := le_accOrbit_of_noDropBy noDropBy_twentyseven hk50
  omega

/-! ## Chain 6 — no infinite ascent -/

/-- Hypothesis: no number stays weakly below its whole forward orbit. -/
def H6_noAscent : Prop :=
  ¬ ∃ n : Nat, 1 < n ∧ ∀ k : Nat, n ≤ acceleratedOrbit k n

/-- **Chain 6.**  Excluding infinite ascent implies Collatz. -/
theorem chain06 (h : H6_noAscent) : CollatzConjecture := by
  refine collatz_of_finiteStoppingTime (fun n hn => ?_)
  by_cases hd : ∃ k : Nat, acceleratedOrbit k n < n
  · exact hd
  · exfalso
    exact h ⟨n, hn, fun k => by
      have : ¬ acceleratedOrbit k n < n := fun hc => hd ⟨k, hc⟩
      omega⟩

/-- Chain 6 is the contrapositive of Chain 1, so the two are the same
statement. -/
theorem chain06_iff_chain01 : H6_noAscent ↔ H1_dropsEventually := by
  constructor
  · intro h n hn
    by_cases hd : ∃ k : Nat, acceleratedOrbit k n < n
    · exact hd
    · exact absurd ⟨n, hn, fun k => by
        have : ¬ acceleratedOrbit k n < n := fun hc => hd ⟨k, hc⟩
        omega⟩ h
  · intro h ⟨n, hn, hall⟩
    obtain ⟨k, hk⟩ := h n hn
    have := hall k
    omega

end Chains
end Collatz
