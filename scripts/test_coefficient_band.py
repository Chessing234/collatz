#!/usr/bin/env python3
"""Independent arithmetic audit of coefficient ceilings and fixed-band classes."""
from pathlib import Path
import random
import re
from test_six_band_prefixes import accelerated,ordinary,balanced_residue

ROOT=Path(__file__).resolve().parents[1]
K,R,Q=5754,119899,20000


def checker(R,Q,K,n,C=1,D=1):
    for j in range(K+1):
        if not (D<=C and Q*C<=R*D):
            return False
        if j<K:
            if n%2:
                if 3*Q*C>R*D:
                    return False
                C*=3
            n=accelerated(n)
            D*=2
    return True


def direct_bounds(R,Q,K,n,C,D):
    states=[n]
    odds=[0]
    for _ in range(K):
        odds.append(odds[-1]+states[-1]%2)
        states.append(accelerated(states[-1]))
    for j in range(K+1):
        c,d=C*3**odds[j],D*2**j
        if d>c or Q*c>R*d:
            return False
        if j<K and states[j]%2 and 3*Q*c>R*d:
            return False
    return True


def witness_check(N,r,bits):
    A=2**K
    m=N+R*K+Q+2
    n=A*m+r
    assert N<n and 1<n and n<=A*(N+R*K+Q+3)
    assert R*K+Q<=n
    x,y,C,D=n,r,1,1
    for j in range(K+1):
        assert x==C*2**(K-j)*m+y
        assert n<=x and Q*x<=(R+1)*n
        assert D*x<=C*(n+j)
        if j<K:
            assert x%2==y%2==bits[j]
            if x%2:
                assert Q*(3*x+1)<=(R+1)*n
                C*=3
            x,y=accelerated(x),accelerated(y)
            D*=2
    duration=K+sum(bits)
    assert duration==9385
    x=n
    for _ in range(duration+1):
        assert n<=x and 200*x<=1199*n
        x=ordinary(x)
    return duration+1


def main():
    comparisons=0
    for k in range(9):
        for n in range(128):
            for R0,Q0 in [(3,1),(5,1),(17,3),(119899,20000)]:
                for C,D in [(1,1),(3,2)]:
                    assert checker(R0,Q0,k,n,C,D)==direct_bounds(R0,Q0,k,n,C,D)
                    comparisons+=1
    r,bits=balanced_residue(K)
    source=(ROOT/'Collatz/Exploration/Band5995.lean').read_text()
    literal=int(re.search(r'def seed5754 : Nat := (\d+)',source).group(1))
    assert literal==r and r<2**K and sum(bits)==3631
    assert checker(R,Q,K,r)
    assert not checker(R-1,Q,K,r)
    rng=random.Random(599520261007)
    states=0
    thresholds=[0,1,10**120]+[rng.randrange(10**120) for _ in range(32)]
    for N in thresholds:
        states+=witness_check(N,r,bits)
    # The coefficient ceiling alone does not absorb the additive +1 error.
    assert checker(45,10,2,3)
    assert 10*ordinary(ordinary(ordinary(3)))>46*3
    # A lighter input cannot be accepted even with a generous upper ceiling.
    assert not checker(100,1,1,2)
    print(f'{comparisons} checker/trace comparisons; {len(thresholds)} fixed-width witnesses; {states} ordinary states; ceiling/budget controls passed')


if __name__=='__main__':
    main()
