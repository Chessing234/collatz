import Collatz.Research.PassageAtlas.SmallBase

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_000 : checkInterval 164 99730 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_101778 : checkInterval 164 0 101778 = true :=
  checkInterval_append 164 0 99730 2048
    prefix_99730 small_block_000

end Collatz.Research.PassageAtlas
