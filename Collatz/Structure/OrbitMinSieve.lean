import Collatz.Structure.HeavySet
import Collatz.Structure.Minimal

/-!
# The sieve applies to every orbit minimum

`Collatz.Structure.Minimal` sieves *the* least counterexample: it lies in no
descending residue class, because a descent would produce a smaller
counterexample, contradicting minimality.

That argument needs a global minimum over all counterexamples.  But there is a
cheaper hypothesis giving the same conclusion.  The orbit minimum `m` of any
single counterexample **never drops** — `T^k(m)` is again on the orbit of `n`,
hence at least `m`.  A descending residue class would force exactly such a drop.

So `m` lies in no descending class either, and the whole sieve applies to it:

**the orbit minimum of any counterexample survives the sieve at every level `j`
with `2 ^ j ≤ m`.**

Since a counterexample's orbit minimum exceeds `102 400 > 2 ^ 16`, that is every
level up to `16`.  In particular its residue modulo `1024` is one of the
sixty-four survivors of `Minimal.sieveCheck_ten`.

This is strictly more general than the minimal-counterexample sieve, and — like
`OrbitMin` itself — it reaches divergent orbits, where no minimal counterexample
argument is available.
-/

namespace Collatz
namespace OrbitMinSieve

open Reach Congruence AccCycle OrbitMin

/-! ## No descending class contains an orbit minimum -/

/-- **The orbit minimum lies in no descending residue class.**  A descent would
contradict the fact that the minimum never drops. -/
theorem not_descends_of_min {n m : Nat}
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) {k : Nat} (hk : 2 ^ k ≤ m) :
    ¬ Descends k (m % 2 ^ k) := by
  intro hd
  have hdrop := accOrbit_lt_of_descends_of_mod hd hk
  have hno := no_drop hm hmin k
  omega

/-- **The orbit minimum survives the sieve at every level below its size.** -/
theorem survives_of_min {n m : Nat}
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) {j : Nat} (hj : 2 ^ j ≤ m) :
    survives j (m % 2 ^ j) = true := by
  refine survives_of_not_descends (fun i hi => ?_)
  have hmod : m % 2 ^ j % 2 ^ i = m % 2 ^ i :=
    Nat.mod_mod_of_dvd m (Arith.two_pow_dvd_two_pow hi)
  rw [hmod]
  have hle : 2 ^ i ≤ m := Nat.le_trans (Arith.two_pow_le_two_pow hi) hj
  exact not_descends_of_min hm hmin hle

/-! ## Levels available for a counterexample -/

/-- A counterexample's orbit minimum exceeds `2 ^ 16`, so every level up to `16`
is available to the sieve. -/
theorem pow_le_min {n m : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m) {j : Nat} (hj : j ≤ 16) :
    2 ^ j ≤ m := by
  have hge := ge_verified hn hnr hm
  have h1 : (2:Nat) ^ j ≤ 2 ^ 16 := Arith.two_pow_le_two_pow hj
  have h2 : (2:Nat) ^ 16 = 65536 := by decide
  omega

/-- **The sieve on a counterexample's orbit minimum**, at every level up to
`16`. -/
theorem survives_of_counterexample {n m : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) {j : Nat} (hj : j ≤ 16) :
    survives j (m % 2 ^ j) = true :=
  survives_of_min hm hmin (pow_le_min hn hnr hm hj)

/-! ## Reading off the residue -/

/-- **The orbit minimum of a counterexample is one of the sixty-four survivors
modulo `1024`.** -/
theorem residue_mod_1024 {n m : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) :
    Search.survivorsMod1024.contains (m % 2 ^ 10) = true := by
  have hs := survives_of_counterexample hn hnr hm hmin (j := 10) (by omega)
  have hlt : m % 2 ^ 10 < 2 ^ 10 := Nat.mod_lt _ (Arith.two_pow_pos 10)
  exact mem_allowed_of_sieveCheck Search.sieveCheck_survivors hlt hs

/-- The residue modulo `4` is `3`, recovered from the sieve rather than from the
halving argument. -/
theorem residue_mod_four {n m : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) : m % 4 = 3 := by
  have hs := survives_of_counterexample hn hnr hm hmin (j := 2) (by omega)
  have hlt : m % 2 ^ 2 < 2 ^ 2 := Nat.mod_lt _ (Arith.two_pow_pos 2)
  have hc := mem_allowed_of_sieveCheck Minimal.sieveCheck_two hlt hs
  rw [show (2:Nat) ^ 2 = 4 from by decide] at hc
  simpa using hc

/-- **The complete residue profile of a counterexample's orbit minimum.** -/
theorem profile {n : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n) :
    ∃ m : Nat, 102400 ≤ m ∧ m % 2 = 1 ∧ m % 4 = 3 ∧
      (∀ j : Nat, j ≤ 16 → survives j (m % 2 ^ j) = true) ∧
      Search.survivorsMod1024.contains (m % 2 ^ 10) = true := by
  obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
  refine ⟨m, ge_verified hn hnr hm, accCycleMin_odd hn hm hmin,
    residue_mod_four hn hnr hm hmin, ?_, residue_mod_1024 hn hnr hm hmin⟩
  intro j hj
  exact survives_of_counterexample hn hnr hm hmin hj

end OrbitMinSieve
end Collatz
