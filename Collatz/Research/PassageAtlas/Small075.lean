import Collatz.Research.PassageAtlas.Small074

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_075 : checkInterval 164 253330 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_255378 : checkInterval 164 0 255378 = true :=
  checkInterval_append 164 0 253330 2048
    prefix_253330 small_block_075

end Collatz.Research.PassageAtlas
