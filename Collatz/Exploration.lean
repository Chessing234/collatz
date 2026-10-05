import Collatz.Exploration.AdaptiveResidueObstruction
import Collatz.Exploration.BlockRanking
import Collatz.Exploration.DensityBoundary
import Collatz.Exploration.FirstDescent
import Collatz.Exploration.OrbitFloor
import Collatz.Exploration.RankGrowth
import Collatz.Exploration.RankReduction
import Collatz.Exploration.RankTransport
import Collatz.Exploration.ResiduePotential
import Collatz.Exploration.TimeChange
import Collatz.Exploration.TraceCertificate

/-!
# Verified exploration entry point

This umbrella exposes the orbit-floor, time-change, ranking, potential
obstruction, density-boundary, and finite-trace modules. None proves the
Collatz conjecture. Conditional hypotheses remain explicit in their statements.

Build with `lake build Collatz.Exploration`. Run the complete isolated audit
with `python3 scripts/verify_exploration.py`. The audit scope is this exploration,
not unrelated pre-existing research in the repository.
-/
