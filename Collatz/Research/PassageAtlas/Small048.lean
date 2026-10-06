import Collatz.Research.PassageAtlas.Small047

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_048 : checkInterval 164 198034 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_200082 : checkInterval 164 0 200082 = true :=
  checkInterval_append 164 0 198034 2048
    prefix_198034 small_block_048

end Collatz.Research.PassageAtlas
