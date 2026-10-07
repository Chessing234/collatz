#!/usr/bin/env python3
"""Exact constructive witnesses and independent ordinary/accelerated checks."""
import random


def accelerated(n):
    return n//2 if n%2==0 else (3*n+1)//2


def ordinary(n):
    return n//2 if n%2==0 else 3*n+1


def balanced_residue(K):
    r, a, x, modulus = 0, 1, 0, 1
    bits = []
    for _ in range(K):
        bit = int(a < 2*modulus)
        if x%2 != bit:
            r += modulus
            x += a
        assert x%2 == bit
        bits.append(bit)
        x = accelerated(x)
        if bit:
            a *= 3
        modulus *= 2
        assert modulus <= a < 3*modulus
        assert r < modulus
    return r, bits


def verify_safe(K, r, bits):
    x, a, modulus = r, 1, 1
    for j in range(K+1):
        assert modulus <= a < 3*modulus
        if j<K:
            assert x%2 == bits[j]
            if x%2:
                assert a < 2*modulus
                a *= 3
            x = accelerated(x)
            modulus *= 2


def witness(K, N, r):
    bound = 2**K*(r+1)
    m = N+r+6*bound+2
    return 2**K*m+r


def check_prefix(K, N, r, bits):
    n = witness(K,N,r)
    assert n>N and n>1
    assert n <= 2**K*N+10*8**K
    if N==0:
        assert n <= 10*8**K
    assert (3*K+4)//5 <= sum(bits)
    duration=K+sum(bits)
    x = n
    for _ in range(duration+1):
        assert n <= x <= 6*n
        x = ordinary(x)
    x = n
    for j in range(K+1):
        assert n <= x < 3*n
        assert x == 3**sum(bits[:j])*2**(K-j)*(N+r+6*2**K*(r+1)+2)+iterate_acc(r,j)
        if j<K:
            assert x%2 == bits[j]
            if x%2:
                assert 3*x+1 <= 6*n
            x = accelerated(x)
    return duration+1


def iterate_acc(n,j):
    for _ in range(j):
        n=accelerated(n)
    return n


def main():
    horizons = list(range(129))+[256,512,1024,2048]
    cache = {}
    for K in horizons:
        r,bits=balanced_residue(K)
        verify_safe(K,r,bits)
        cache[K]=(r,bits)
    rng = random.Random(600017)
    witnesses=states=0
    for _ in range(2000):
        K=rng.randrange(129)
        N=rng.randrange(10**120)
        r,bits=cache[K]
        states+=check_prefix(K,N,r,bits)
        witnesses+=1
    for K in horizons:
        r,bits=cache[K]
        states+=check_prefix(K,0,r,bits)
        witnesses+=1
    # Ordinary odd peaks are necessary when transferring accelerated bounds.
    assert accelerated(3)==5 and ordinary(3)==10
    assert 3<=accelerated(3)<=5 and ordinary(3)>5
    # Without the safe multiplier lower bound, a large even input descends immediately.
    n=2**128*100
    assert ordinary(n)<n
    # A fixed small source is not a witness at every horizon: 3 leaves [3,18] at time 6.
    x=3
    for _ in range(6):
        x=ordinary(x)
    assert x==2
    # The integer coefficient gap alone cannot absorb an arbitrarily large offset.
    assert 2*10+11>3*10
    print(f'{len(horizons)} safe residues; {witnesses} scaled witnesses; '
          f'{states} ordinary prefix states; affine identities and transfer controls passed')


if __name__=='__main__':
    main()
