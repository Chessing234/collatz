import Collatz.Research.PassageAtlas.Small079

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_080 : checkInterval 164 263570 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_265618 : checkInterval 164 0 265618 = true :=
  checkInterval_append 164 0 263570 2048
    prefix_263570 small_block_080

end Collatz.Research.PassageAtlas
