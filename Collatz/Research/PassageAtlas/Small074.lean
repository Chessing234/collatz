import Collatz.Research.PassageAtlas.Small073

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_074 : checkInterval 164 251282 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_253330 : checkInterval 164 0 253330 = true :=
  checkInterval_append 164 0 251282 2048
    prefix_251282 small_block_074

end Collatz.Research.PassageAtlas
