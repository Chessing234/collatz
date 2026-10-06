import Collatz.Research.PassageAtlas.Small032

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_033 : checkInterval 164 167314 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_169362 : checkInterval 164 0 169362 = true :=
  checkInterval_append 164 0 167314 2048
    prefix_167314 small_block_033

end Collatz.Research.PassageAtlas
