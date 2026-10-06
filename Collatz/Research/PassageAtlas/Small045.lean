import Collatz.Research.PassageAtlas.Small044

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_045 : checkInterval 164 191890 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_193938 : checkInterval 164 0 193938 = true :=
  checkInterval_append 164 0 191890 2048
    prefix_191890 small_block_045

end Collatz.Research.PassageAtlas
