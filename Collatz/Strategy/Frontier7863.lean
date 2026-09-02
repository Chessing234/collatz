import Collatz.Strategy.FrontierParametric
import Collatz.Search.VerifiedRung7863
import Collatz.Search.VerifiedRange

/-!
# The frontier at the next rung: no nontrivial cycle shorter than 7863

Everything needed for this was in place separately:

* `Strategy.PreCertified.cert_4961` — the certificate reaching `4961`, banked
  before any range supported it;
* `Strategy.PreCertified.pow_gap_4961` — the gap `2 ^ 7862 < 3 ^ 4961`;
* `Strategy.FrontierParametric.length_ge_of_cert` — the frontier theorem stated
  once over `(c, A, F)`;
* `Search.VerifiedRung7863` — the verified range pushed to `1 358 848`, past the
  riser `G(4296) = 1 358 717`, using `Search.FuelMonotone` to carry the earlier
  `1061` blocks up from fuel `200` to `224` without recomputation.

So this file is an instantiation and nothing more.  The previous frontier was
`6809`.
-/

namespace Collatz
namespace Frontier7863

open Reach Search VerifiedRange AccCycle

/-- The verified range as a `VerifiedBelow`. -/
theorem verified_1358848 : VerifiedBelow 1358848 :=
  fun _ hn hlt => reachesOne_of_lt_1358848 hn hlt

/-- The range in the form the frontier theorem consumes. -/
theorem ge_verified_1358718 {n m : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m) : 1358718 ≤ m :=
  ge_verified_of (verifiedBelow_mono (by omega) verified_1358848) hn hnr hm

/-- **Every nontrivial accelerated cycle has length at least `7863`.**

Unconditional.  The certificate and the exponent gap were already proved in
`PreCertified`; the only new input is the extended verified range. -/
theorem length_ge_7863 {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) : 7863 ≤ L :=
  FrontierParametric.length_ge_7863_of_verified
    (fun hn' hnr' hm => ge_verified_1358718 hn' hnr' hm) hn h hnr

end Frontier7863
end Collatz
