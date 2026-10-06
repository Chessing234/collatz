import Collatz.Research.PassageAtlas.Small076

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_077 : checkInterval 164 257426 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_259474 : checkInterval 164 0 259474 = true :=
  checkInterval_append 164 0 257426 2048
    prefix_257426 small_block_077

end Collatz.Research.PassageAtlas
