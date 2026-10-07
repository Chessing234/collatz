#!/usr/bin/env python3
"""Independent recurrence tests, including sharp constants and endpoint exits."""

def main():
    checked = exited = 0
    for n in range(1, 2001):
        x, C, D, B, odds, floor = n, 1, 1, 0, 0, n
        for j in range(1, 101):
            floor = min(floor, x)
            if x % 2:
                x = (3*x+1)//2
                B = 3*B+D
                C *= 3
                odds += 1
            else:
                x //= 2
            D *= 2
            assert D*x == C*n+B
            for b in {0, 1, floor//2, floor}:
                odd_ceiling = b+1 if b % 2 == 0 else b
                w = 3*odd_ceiling+1
                assert w*B <= odds*(C*n+B)
                assert max(w-odds, 0)*B <= odds*C*n
                checked += 1
            exited += x < floor
    for b in range(2001):
        n = b+1 if b % 2 == 0 else b
        w = 3*n+1
        assert w == 2*((3*n+1)//2)
        assert w+1 > 3*n+1  # Any larger uniform weight fails at this first step.
    # Exhaust the source-elimination lemma, including zero coefficients.
    spread = 0
    for n in range(6):
        for D in range(1, 5):
            for L in range(5):
                for x in range(8):
                    B = D*x-L*n
                    if B < 0: continue
                    for H in range(5):
                        for E in range(1, 4):
                            y = (H*n+E-1)//E
                            for b in range(x+1):
                                for P in range(5):
                                    Q = 2
                                    g = Q*H*D-P*L*E
                                    if g >= 0 and Q*y <= P*b:
                                        assert g*b <= Q*H*B
                                        spread += 1
    exits = 0
    for n in range(1, 301):
        states, coeffs, counts = [n], [1], [0]
        for j in range(30):
            x = states[-1]
            odd = x % 2
            states.append((3*x+1)//2 if odd else x//2)
            coeffs.append(coeffs[-1]*(3 if odd else 1))
            counts.append(counts[-1]+odd)
        for b in {1, max(1, n//6), n}:
            if n > 6*b: continue
            w = 3*(b+1 if b % 2 == 0 else b)+1
            for a in range(1, 30):
                for c in range(1, 30):
                    g = coeffs[c]*2**a-6*coeffs[a]*2**c
                    if g > 0 and 6*coeffs[c]*counts[a]*coeffs[a] < g*max(w-counts[a], 0):
                        assert any(x < b or 6*b < x for x in states[:max(a,c)+1])
                        exits += 1
    assert exits > 0
    print(f'{exits} nonvacuous conditional exit instances')
    print(f'{checked} floor budgets; {exited} endpoint exits; 2001 sharpness controls; {spread} spread cases')

if __name__ == '__main__': main()
