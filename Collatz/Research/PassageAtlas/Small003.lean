import Collatz.Research.PassageAtlas.Small002

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_003 : checkInterval 164 105874 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_107922 : checkInterval 164 0 107922 = true :=
  checkInterval_append 164 0 105874 2048
    prefix_105874 small_block_003

end Collatz.Research.PassageAtlas
