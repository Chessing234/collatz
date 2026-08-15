import Collatz.Chains.OrbitMin
import Collatz.Structure.OrbitMinSieve

/-!
# Chains 191–205: the sieve on orbit minima

`Collatz.Structure.OrbitMinSieve` shows the residue sieve applies to the orbit
minimum of *any* counterexample, not merely to the least counterexample.  The
argument is cheaper than minimality: the orbit minimum never drops, and a
descending residue class would force a drop.

That yields the weakest hypothesis in the project that still implies Collatz.
Chain 191 needs the drop property only for numbers that are

* orbit minima of their own orbit,
* at least `102 400`, and
* in one of the sixty-four surviving classes modulo `1024`.

Every earlier residue chain demanded the drop property for *all* large numbers
in those classes; this one demands it only for the orbit minima among them,
which are additionally odd, `3` modulo `4`, and heavy at every scale.
-/

namespace Collatz
namespace Chains

open Reach Strategy Congruence AccCycle OrbitMin OrbitMinSieve

/-! ## Chain 191: the weakest sufficient hypothesis -/

/-- Hypothesis: every large surviving orbit minimum drops. -/
def H191_minSurvivorsDrop : Prop :=
  ∀ n m : Nat, 0 < n → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → 102400 ≤ m →
    survives 10 (m % 2 ^ 10) = true →
    ∃ k : Nat, acceleratedOrbit k m < m

/-- **Chain 191.**  The weakest hypothesis in the project that still gives
Collatz: the drop property is needed only for orbit minima in the sixty-four
surviving classes. -/
theorem chain191 (h : H191_minSurvivorsDrop) : CollatzConjecture := by
  intro n hn
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
    have hge := ge_verified hn hr hm
    have hs := survives_of_counterexample hn hr hm hmin (j := 10) (by omega)
    obtain ⟨k, hk⟩ := h n m hn hm hmin hge hs
    have hno := no_drop hm hmin k
    omega

/-- Hypothesis: no orbit minimum of a counterexample survives the sieve. -/
def H192_minFailsSieve : Prop :=
  ∀ n m : Nat, 0 < n → ¬ ReachesOne n → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → survives 10 (m % 2 ^ 10) = false

/-- **Chain 192.**  Orbit minima of counterexamples always survive the sieve, so
this closes the problem. -/
theorem chain192 (h : H192_minFailsSieve) : CollatzConjecture := by
  intro n hn
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
    have htrue := survives_of_counterexample hn hr hm hmin (j := 10) (by omega)
    have hfalse := h n m hn hr hm hmin
    rw [htrue] at hfalse
    simp at hfalse

/-- Hypothesis: the orbit minimum of a counterexample is not `3` modulo `4`. -/
def H193_minNotThreeModFour : Prop :=
  ∀ n m : Nat, 0 < n → ¬ ReachesOne n → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → m % 4 ≠ 3

/-- **Chain 193.**  It always is. -/
theorem chain193 (h : H193_minNotThreeModFour) : CollatzConjecture := by
  intro n hn
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
    exact h n m hn hr hm hmin (residue_mod_four hn hr hm hmin)

/-! ## Chains 194–198: refutations -/

/-- Hypothesis: some counterexample's orbit minimum fails the sieve. -/
def H194_someMinFails : Prop :=
  ∃ n m : Nat, 0 < n ∧ ¬ ReachesOne n ∧ (∃ i : Nat, acceleratedOrbit i n = m) ∧
    (∀ j : Nat, m ≤ acceleratedOrbit j n) ∧ survives 10 (m % 2 ^ 10) = false

/-- **Chain 194 is refuted.** -/
theorem chain194_refuted : ¬ H194_someMinFails := by
  intro ⟨n, m, hn, hr, hm, hmin, hfalse⟩
  have htrue := survives_of_counterexample hn hr hm hmin (j := 10) (by omega)
  rw [htrue] at hfalse
  simp at hfalse

/-- Hypothesis: some counterexample's orbit minimum lies in a descending class
at a level below its size. -/
def H195_someMinDescends : Prop :=
  ∃ n m k : Nat, (∃ i : Nat, acceleratedOrbit i n = m) ∧
    (∀ j : Nat, m ≤ acceleratedOrbit j n) ∧ 2 ^ k ≤ m ∧ Descends k (m % 2 ^ k)

/-- **Chain 195 is refuted**: an orbit minimum lies in no descending class. -/
theorem chain195_refuted : ¬ H195_someMinDescends := by
  intro ⟨n, m, k, hm, hmin, hk, hd⟩
  exact not_descends_of_min hm hmin hk hd

/-- Hypothesis: some counterexample's orbit minimum is not `3` modulo `4`. -/
def H196_someMinNotThree : Prop :=
  ∃ n m : Nat, 0 < n ∧ ¬ ReachesOne n ∧ (∃ i : Nat, acceleratedOrbit i n = m) ∧
    (∀ j : Nat, m ≤ acceleratedOrbit j n) ∧ m % 4 ≠ 3

/-- **Chain 196 is refuted.** -/
theorem chain196_refuted : ¬ H196_someMinNotThree := by
  intro ⟨n, m, hn, hr, hm, hmin, hne⟩
  exact hne (residue_mod_four hn hr hm hmin)

/-! ## Chains 197–205: the assembled statement -/

/-- **Chain 197.**  The complete profile of a counterexample's orbit minimum,
combining the sieve, the residue classes, heaviness, and the no-drop property. -/
theorem chain197_profile {n : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n) :
    ∃ m : Nat, 102400 ≤ m ∧ m % 2 = 1 ∧ m % 4 = 3 ∧
      (∀ j : Nat, j ≤ 16 → survives j (m % 2 ^ j) = true) ∧
      Search.survivorsMod1024.contains (m % 2 ^ 10) = true ∧
      (∀ k : Nat, 2 ^ k ≤ m → 2 ^ k < 2 * 3 ^ oddCount m k) ∧
      (∀ k : Nat, m ≤ acceleratedOrbit k m) := by
  obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
  exact ⟨m, ge_verified hn hnr hm, accCycleMin_odd hn hm hmin,
    residue_mod_four hn hnr hm hmin,
    fun j hj => survives_of_counterexample hn hnr hm hmin hj,
    residue_mod_1024 hn hnr hm hmin,
    fun k hk => OrbitMin.heavy hn hm hmin hk,
    no_drop hm hmin⟩

/-- **Chain 198.**  The orbit-minimum sieve targets, collected. -/
theorem chain198 :
    (H191_minSurvivorsDrop → CollatzConjecture) ∧
    (H192_minFailsSieve → CollatzConjecture) ∧
    (H193_minNotThreeModFour → CollatzConjecture) :=
  ⟨chain191, chain192, chain193⟩

/-- **Chain 199.**  The refutations of this file, collected. -/
theorem chain199_refuted :
    (¬ H194_someMinFails) ∧ (¬ H195_someMinDescends) ∧ (¬ H196_someMinNotThree) :=
  ⟨chain194_refuted, chain195_refuted, chain196_refuted⟩

end Chains
end Collatz
