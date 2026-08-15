import Collatz.Search.Descent
open Collatz Search
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem check_drop_100000 : allDropUpTo 100000 200 = true := by decide
