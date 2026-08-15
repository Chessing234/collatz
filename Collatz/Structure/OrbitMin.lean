import Collatz.Structure.MinimalHeavy
import Collatz.Structure.CycleMinClass
import Collatz.Search.Sieved
import Collatz.Structure.AccDivergence

/-!
# The minimum of an arbitrary orbit

Most of the cycle theory only ever used two properties of the least point: that
it *occurs* on the orbit, and that nothing on the orbit is smaller.  Neither
mentions cycles.  So the same conclusions hold for the **orbit minimum of any
positive number**, whether its orbit cycles, diverges, or reaches `1`.

That matters because it covers the divergence half, which the cycle lemmas do
not reach.  Writing `m` for the least value ever attained by the orbit of `n`:

* `m` is odd (`AccCycle.accCycleMin_odd`);
* `m ≡ 3 (mod 4)` when `m > 1` (`CycleMinClass.cycleMin_mod_four`);
* `m` never drops — `m ≤ T^k(m)` for every `k`, because `T^k(m)` is again on the
  orbit of `n`;
* hence `m` is **heavy at every scale**: `2 ^ k < 2 · 3 ^ {a(m,k)}` whenever
  `2 ^ k ≤ m`.

The last item is the point.  `Collatz.Structure.MinimalHeavy` proved heaviness
for *the* least counterexample; here it holds for the orbit minimum of *any*
counterexample — a strictly stronger statement, and one that applies to
divergent orbits, where there is no least counterexample to appeal to.
-/

namespace Collatz
namespace OrbitMin

open Reach Congruence AccCycle

/-! ## The orbit minimum does not drop -/

/-- **The orbit minimum never drops.**  Every iterate of `m` is again an iterate
of `n`, hence at least `m`. -/
theorem no_drop {n m : Nat} (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (k : Nat) :
    m ≤ acceleratedOrbit k m := by
  obtain ⟨i, hi⟩ := hm
  have hshift : acceleratedOrbit k m = acceleratedOrbit (k + i) n := by
    rw [← hi, acceleratedOrbit_add]
  rw [hshift]
  exact hmin (k + i)

/-- **The orbit minimum is heavy at every scale below itself.**  This is the
`MinimalHeavy` bound, freed from any reference to minimal counterexamples. -/
theorem heavy {n m : Nat} (hn : 0 < n) (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) {k : Nat} (hk : 2 ^ k ≤ m) :
    2 ^ k < 2 * 3 ^ oddCount m k :=
  AffineBoundSharp.two_pow_lt_of_no_drop (accCycleMin_pos hn hm) hk (no_drop hm hmin k)

/-- The density form of the same bound. -/
theorem three_mul_le_five_mul {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) {k : Nat} (hk : 2 ^ k ≤ m) :
    3 * (k - 1) ≤ 5 * oddCount m k := by
  have hlt := heavy hn hm hmin hk
  have hle : 2 ^ (k - 1) ≤ 3 ^ oddCount m k := by
    cases k with
    | zero =>
      have h3 := Arith.three_pow_pos (oddCount m 0)
      simp
    | succ j =>
      have hsplit : (2:Nat) ^ (j + 1) = 2 * 2 ^ j := Arith.two_pow_succ j
      have hidx : j + 1 - 1 = j := by omega
      rw [hidx]
      omega
  exact Density.three_mul_le_five_mul_of_heavy hle

/-! ## The minimum of a counterexample's orbit -/

/-- If the orbit of `n` never reaches `1`, its minimum lies beyond the verified
range. -/
theorem ge_verified {n m : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m) : 102400 ≤ m := by
  obtain ⟨i, hi⟩ := hm
  by_cases hlt : m < 102400
  · exfalso
    have hpos : 0 < m := by
      rw [← hi]; exact acceleratedOrbit_positive hn i
    have hreach : ReachesOne m := Search.reachesOne_of_lt_102400 hpos hlt
    rw [← hi] at hreach
    exact hnr (reachesOne_of_accOrbit hn hreach)
  · omega

/-- **The full profile of a counterexample's orbit minimum.**  It is large, odd,
`3` modulo `4`, never drops, and is heavy at every scale below itself. -/
theorem profile {n : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n) :
    ∃ m : Nat, 102400 ≤ m ∧ m % 2 = 1 ∧ m % 4 = 3 ∧
      (∀ k : Nat, m ≤ acceleratedOrbit k m) ∧
      (∀ k : Nat, 2 ^ k ≤ m → 2 ^ k < 2 * 3 ^ oddCount m k) := by
  obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
  have hge := ge_verified hn hnr hm
  exact ⟨m, hge, accCycleMin_odd hn hm hmin,
    CycleMinClass.cycleMin_mod_four hn hm hmin (by omega),
    no_drop hm hmin,
    fun k hk => heavy hn hm hmin hk⟩

/-- Restated for divergent orbits, where the cycle lemmas do not apply: the
minimum of a divergent orbit satisfies exactly the same constraints. -/
theorem divergent_profile {n : Nat} (hn : 0 < n)
    (_hdiv : AccDivergence.AccDivergent n) (hnr : ¬ ReachesOne n) :
    ∃ m : Nat, 102400 ≤ m ∧ m % 4 = 3 ∧
      (∀ k : Nat, 2 ^ k ≤ m → 2 ^ k < 2 * 3 ^ oddCount m k) := by
  obtain ⟨m, hge, _, hfour, _, hheavy⟩ := profile hn hnr
  exact ⟨m, hge, hfour, hheavy⟩

/-- The contrapositive, which is what a proof would use: a light scale anywhere
at the orbit minimum forces the orbit to reach `1`. -/
theorem reachesOne_of_light {n m k : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n)
    (hk : 2 ^ k ≤ m) (hlight : 2 * 3 ^ oddCount m k ≤ 2 ^ k) : ReachesOne n := by
  exfalso
  have := heavy hn hm hmin hk
  omega

end OrbitMin
end Collatz
