import Collatz.Research.PassageAtlas.Small080

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_081 : checkInterval 164 265618 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_267666 : checkInterval 164 0 267666 = true :=
  checkInterval_append 164 0 265618 2048
    prefix_265618 small_block_081

end Collatz.Research.PassageAtlas
