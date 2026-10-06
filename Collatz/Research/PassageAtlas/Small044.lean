import Collatz.Research.PassageAtlas.Small043

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_044 : checkInterval 164 189842 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_191890 : checkInterval 164 0 191890 = true :=
  checkInterval_append 164 0 189842 2048
    prefix_189842 small_block_044

end Collatz.Research.PassageAtlas
