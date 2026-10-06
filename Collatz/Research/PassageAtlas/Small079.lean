import Collatz.Research.PassageAtlas.Small078

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_079 : checkInterval 164 261522 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_263570 : checkInterval 164 0 263570 = true :=
  checkInterval_append 164 0 261522 2048
    prefix_261522 small_block_079

end Collatz.Research.PassageAtlas
