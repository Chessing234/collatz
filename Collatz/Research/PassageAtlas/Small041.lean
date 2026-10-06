import Collatz.Research.PassageAtlas.Small040

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_041 : checkInterval 164 183698 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_185746 : checkInterval 164 0 185746 = true :=
  checkInterval_append 164 0 183698 2048
    prefix_183698 small_block_041

end Collatz.Research.PassageAtlas
