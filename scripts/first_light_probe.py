#!/usr/bin/env python3
"""Independent integer-arithmetic check; Lean provides the proof certificate."""
import json
from pathlib import Path
K = 128
N = 1186
best = (0, 0, 0)
for k in range(K+1):
    for a in range(k+1):
        gap = 2**k-3**a
        if gap > 0:
            bound = a*3**a//(3*gap)
            assert bound < N
            if bound > best[0]:
                best = bound, k, a
max_time = 0
for n in range(2, N):
    x, a = n, 0
    for k in range(1, K+1):
        a += x%2
        x = (3*x+1)//2 if x%2 else x//2
        if 3**a < 2**k:
            assert x < n
            max_time = max(max_time, k)
            break
    else:
        raise AssertionError(('no crossing in checked range', n))
result = dict(horizon=K, small_start_count=N-2,
    largest_exception_bound=best[0], worst_bound_pair=dict(k=best[1], a=best[2]),
    maximum_first_crossing_among_small_starts=max_time,
    failures=0, universal_collatz_proof=False)
path=Path(__file__).resolve().parents[1]/'Research/FirstLightProbe.json'
path.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
