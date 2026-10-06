import Collatz.Strategy.FirstLight1024
import Collatz.Strategy.FirstLightConsequences

/-! The large kernel certificate as an input to the reusable stopping-time API. -/
namespace Collatz.FirstLightConsequences

/-- First crossings through 1024 cause descent for every start above 1. -/
theorem exactThrough_1024 : ExactThrough 1024 :=
  fun _ _ hn hk hf => FirstLight1024.descent_at_first_light_le_1024 hn hk hf

end Collatz.FirstLightConsequences
