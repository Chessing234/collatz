import Collatz.Strategy.FirstLight1024

namespace Collatz.Research.PassageAtlas
open FirstLightScan

/-- Reuse the inherited checked range at the enlarged scan horizon. -/
theorem prefix_99730 : checkInterval 164 0 99730 = true :=
  checkInterval_mono_horizon 135 164 0 99730 (by decide)
    FirstLight1024Chunks.prefix_99730

end Collatz.Research.PassageAtlas
