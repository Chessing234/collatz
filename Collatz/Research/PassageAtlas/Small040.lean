import Collatz.Research.PassageAtlas.Small039

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_040 : checkInterval 164 181650 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_183698 : checkInterval 164 0 183698 = true :=
  checkInterval_append 164 0 181650 2048
    prefix_181650 small_block_040

end Collatz.Research.PassageAtlas
