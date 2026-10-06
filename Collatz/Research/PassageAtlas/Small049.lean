import Collatz.Research.PassageAtlas.Small048

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_049 : checkInterval 164 200082 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_202130 : checkInterval 164 0 202130 = true :=
  checkInterval_append 164 0 200082 2048
    prefix_200082 small_block_049

end Collatz.Research.PassageAtlas
