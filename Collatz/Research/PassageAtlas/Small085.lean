import Collatz.Research.PassageAtlas.Small084

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_085 : checkInterval 164 273810 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_275858 : checkInterval 164 0 275858 = true :=
  checkInterval_append 164 0 273810 2048
    prefix_273810 small_block_085

end Collatz.Research.PassageAtlas
