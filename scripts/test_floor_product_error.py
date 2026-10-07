#!/usr/bin/env python3
"""Exact-integer tests of multiplicative error bounds and their limits."""

def main():
    cases = exhausted = 0
    for n in range(1, 1001):
        x, C, D, B, a, floor = n, 1, 1, 0, 0, n
        for j in range(1, 101):
            floor = min(floor, x)
            if x % 2:
                x = (3*x+1)//2
                C *= 3
                B = 3*B+D
                a += 1
            else: x //= 2
            D *= 2
            for b in {0, 1, floor//2, floor}:
                m = b+1 if b % 2 == 0 else b
                v, w = 3*m, 3*m+1
                assert D*x == C*n+B
                assert v**a*D*x <= w**a*C*n
                assert v**a*B <= (w**a-v**a)*C*n
                if a >= w and B > 0:
                    assert v**a*B > 0
                    exhausted += 1
                cases += 1
    # One-step equality witnesses the sharp factor; increasing v fails.
    for b in range(1001):
        m = b+1 if b % 2 == 0 else b
        v, w = 3*m, 3*m+1
        assert v*(3*m+1) == 3*w*m
        assert (v+1)*(3*m+1) > 3*w*m
    bands = 0
    for n in range(1, 201):
        states, coeffs, counts = [n], [1], [0]
        for j in range(20):
            x = states[-1]
            odd = x % 2
            states.append((3*x+1)//2 if odd else x//2)
            coeffs.append(coeffs[-1]*(3 if odd else 1))
            counts.append(counts[-1]+odd)
        for a in range(1, 21):
            b = min(states[:a+1])
            v = 3*(b+1 if b % 2 == 0 else b)
            w = v+1
            for c in range(21):
                Q = 3
                P = (Q*states[c]+b-1)//b
                assert Q*states[c] <= P*b
                assert Q*coeffs[c]*2**a*v**counts[a] <= P*2**c*coeffs[a]*w**counts[a]
                bands += 1
    print(f'{bands} two-endpoint product band budgets')
    print(f'{cases} product checks; {exhausted} cases beyond the linear budget; 1001 factor controls')

if __name__ == '__main__': main()
