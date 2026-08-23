import Collatz.Strategy.RealizableFrontier6809
import Collatz.Search.VerifiedExtended

namespace Collatz
namespace Probe
open Reach

/-- Plain-map version: every PLAIN orbit point of a counterexample is ≥ 1086464. -/
theorem plain_ge_verified {n m : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n)
    (hm : ∃ k : Nat, orbit k n = m) : 1086464 ≤ m := by
  obtain ⟨k, hk⟩ := hm
  by_cases hlt : m < 1086464
  · exfalso
    have hpos : 0 < m := by rw [← hk]; exact orbit_positive hn k
    have hreach : ReachesOne m := Search.reachesOne_of_lt_1086464 hpos hlt
    rw [← hk] at hreach
    exact hnr ((reachesOne_iff_orbit k n).mpr hreach)
  · omega

/-- Ancestor version: every predecessor of a counterexample is itself ≥ 1086464,
so the whole REVERSE tree of a counterexample also avoids the bottom region. -/
theorem ancestor_ge_verified {x n k : Nat} (hx : 0 < x) (hnr : ¬ ReachesOne n)
    (h : orbit k x = n) : 1086464 ≤ x := by
  refine Search.counterexample_ge_1086464 hx ?_
  intro hr
  have h1 : ReachesOne (orbit k x) := (reachesOne_iff_orbit k x).mp hr
  rw [h] at h1
  exact hnr h1

#print axioms plain_ge_verified
#print axioms ancestor_ge_verified

end Probe
end Collatz
