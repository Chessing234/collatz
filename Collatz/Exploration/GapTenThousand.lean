import Collatz.Exploration.GapEndpointScan

/-! A finite endpoint certificate through horizon 10000.
It proves descent conditional on a first light crossing, not crossing existence. -/
namespace Collatz.Exploration.GapTenThousand
open GapEndpointScan

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem endpoint_certificate : scan 3330950 10000 0 1 1=true := by decide

/-- Every source at least 3330950 descends at a first coefficient crossing by 10000. -/
theorem descent_at_first_light {n j : Nat} (hn : 3330950 ≤ n) (hj : j ≤ 10000)
    (hf : FirstLightDescent.FirstLight n j) : acceleratedOrbit j n < n :=
  first_light_of_scan endpoint_certificate hn hj hf

end Collatz.Exploration.GapTenThousand
