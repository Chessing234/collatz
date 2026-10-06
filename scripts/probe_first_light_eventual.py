#!/usr/bin/env python3
"""Independent orbit checks above the symbolic exceptional-start bound."""
import json


def events(n, h):
    x, a = n, 0
    crossing = descent = None
    for k in range(1, h+1):
        odd = x % 2
        a += odd
        x = (3*x+1)//2 if odd else x//2
        if crossing is None and 3**a < 2**k:
            crossing = k
        if descent is None and x < n:
            descent = k
    return crossing, descent


def main():
    cases = 0
    for h in range(65):
        threshold, period = h*3**h, 2**h
        for offset in range(1, 65):
            n = threshold+offset
            left = events(n, h)
            right = events(n+period, h)
            assert left[0] == left[1], (h, n, left)
            assert right[0] == right[1], (h, n+period, right)
            assert left == right, (h, n, left, right)
            cases += 1
    print(json.dumps({'status': 'passed', 'horizons': [0, 64],
                      'paired_representatives': cases,
                      'bound': 'n > H * 3**H',
                      'scope': 'Regression evidence; universal statements are Lean theorems.'}, indent=2))


if __name__ == '__main__':
    main()
