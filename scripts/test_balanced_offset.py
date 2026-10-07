#!/usr/bin/env python3
"""Independent integer checks of normalized offsets and smaller six-band witnesses."""
import random
from test_six_band_prefixes import accelerated, ordinary, balanced_residue, verify_safe


def check(K, N, r, bits):
    modulus = 2**K
    m = N+r+12*(r+K+1)+2
    n = modulus*m+r
    assert N < n and 1 < n
    assert n <= modulus*N+28*4**K
    x, odd = r, 0
    for j in range(K+1):
        assert 2**j*x <= 3**odd*(r+j)
        assert x < 3*(r+K+1)
        if j < K:
            odd += x%2
            x = accelerated(x)
    duration = K+sum(bits)
    assert duration >= K+(3*K+4)//5
    x = n
    for _ in range(duration+1):
        assert n <= x <= 6*n
        x = ordinary(x)
    return duration+1


def main():
    rng = random.Random(20261007)
    states = witnesses = 0
    for K in list(range(129))+[256,512,1024,2048]:
        r, bits = balanced_residue(K)
        verify_safe(K, r, bits)
        for N in [0,1,10**120]+[rng.randrange(10**60) for _ in range(12)]:
            states += check(K,N,r,bits)
            witnesses += 1
    for H in range(10001):
        K=(5*H+7)//8
        assert H <= K+(3*K+4)//5
    # The heavy-prefix assumption is essential for normalized_bound.
    r,j = 16,5
    x=r
    for _ in range(j):
        x=accelerated(x)
    assert 2**j*x > 3*(r+j)
    # A six-band survivor need not be permanently trapped: explicit first exit.
    r,bits=balanced_residue(1)
    n=2*(r+12*(r+2)+2)+r
    assert n == 79
    x=n
    for _ in range(13):
        x=ordinary(x)
    assert x<n
    print(f'{witnesses} smaller witnesses; {states} ordinary states; assumption/exit controls passed')


if __name__ == '__main__':
    main()
