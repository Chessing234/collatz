import Collatz.Structure.RunValue
import Collatz.Structure.OrbitMin
import Collatz.Strategy.NeverDrops

/-!
# The wider verified range, propagated

`Search.reachesOne_of_lt_307200` clears three times the range the development is
stated against.  The constants elsewhere are left at `102 400` so that no
existing proof changes; this file records the sharper forms, which are the ones
worth quoting.

* A counterexample's orbit minimum is at least `307 200`, not `102 400`.
* Hence the greatest point of a nontrivial cycle is at least `614 400` by the
  doubling bound, and at least `691 199` by the `9/4` bound from `RunValue`.

The second is the more interesting number, because it combines the computation
with the run theory rather than with the elementary `M ≥ 2m`.
-/

namespace Collatz
namespace VerifiedSharp

open Reach Congruence AccCycle CycleExtremes OrbitMin

/-- **The sharper size bound.**  Any point on the orbit of a counterexample is at
least `307 200`. -/
theorem ge_verified_sharp {n m : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m) : 307200 ≤ m := by
  obtain ⟨i, hi⟩ := hm
  by_cases hlt : m < 307200
  · exfalso
    have hpos : 0 < m := by
      rw [← hi]; exact acceleratedOrbit_positive hn i
    have hreach : ReachesOne m := Search.reachesOne_of_lt_307200 hpos hlt
    rw [← hi] at hreach
    exact hnr (reachesOne_of_accOrbit hn hreach)
  · omega

/-- A number that never drops and exceeds one is at least `307 200`. -/
theorem neverDrops_ge_sharp {x : Nat} (hgt : 1 < x) (h : NeverDrops.NeverDrops x) :
    307200 ≤ x :=
  ge_verified_sharp (by omega) (NeverDrops.not_reachesOne_of_neverDrops hgt h)
    (NeverDrops.self_witness x)

/-- **The greatest point of a nontrivial cycle exceeds `614 400`**, by the
doubling bound. -/
theorem cycleMax_ge_sharp {n L m : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) :
    614400 ≤ cycleMax n L := by
  have hge := ge_verified_sharp hn hnr hm
  have hdouble := two_mul_min_le_cycleMax hn h hmin
  omega

/-- **And exceeds `691 199`**, by the `9/4` bound: the least point of a cycle
always opens with a run of two odd steps, so the cycle climbs to at least
`9/4` of it. -/
theorem cycleMax_ge_sharper {n L m : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) :
    691199 ≤ cycleMax n L := by
  have hge := ge_verified_sharp hn hnr hm
  have hnine := RunValue.nine_mul_min_le_four_mul_cycleMax hn h hm hmin (by omega)
  omega

/-- The two bounds together, with the run bound strictly stronger. -/
theorem cycle_bounds_sharp {n L m : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) :
    307200 ≤ m ∧ 614400 ≤ cycleMax n L ∧ 691199 ≤ cycleMax n L :=
  ⟨ge_verified_sharp hn hnr hm,
   cycleMax_ge_sharp hn h hnr hm hmin,
   cycleMax_ge_sharper hn h hnr hm hmin⟩

end VerifiedSharp
end Collatz
