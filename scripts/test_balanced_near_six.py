#!/usr/bin/env python3
"""Independent exact arithmetic for retained margins and sub-six witnesses."""
import random
from test_six_band_prefixes import accelerated, ordinary, balanced_residue, verify_safe


def check(K, N, r, bits):
    A=2**K
    n=A*(N+6*K+3)+r
    assert N<n and 1<n and n<=A*(N+6*K+4)
    assert n>=A*(6*K+1)
    x,C,D=n,1,1
    for j in range(K+1):
        assert n<=x
        assert D*x<=C*(n+j)
        assert A*x+2*n<=6*A*n
        if j<K:
            assert x%2==bits[j]
            if x%2:
                assert C<2*D
                assert D*(3*x+1)+2*n<=6*D*n
                C*=3
            x=accelerated(x)
            D*=2
    duration=K+sum(bits)
    assert K+(3*K+4)//5<=duration
    x=n
    for _ in range(duration+1):
        assert n<=x
        assert A*x+2*n<=6*A*n
        assert A*x<=(6*A-2)*n
        x=ordinary(x)
    return duration+1


def main():
    rng=random.Random(202610071)
    states=witnesses=0
    for K in list(range(129))+[256,512,1024,2048]:
        r,bits=balanced_residue(K)
        verify_safe(K,r,bits)
        for N in [0,1,10**120]+[rng.randrange(10**60) for _ in range(12)]:
            states+=check(K,N,r,bits)
            witnesses+=1
        # Exact translation from cross-multiplied widths to deficit inequality.
        for Q in [1,2,17,10**30]:
            for d in [0,1,Q,6*Q]:
                assert (((6*Q-d)*2**K<(6*2**K-2)*Q)==(2*Q<d*2**K))
    for H in range(10001):
        K=(5*H+7)//8
        assert H<=K+(3*K+4)//5
    # Stronger deficit 3/2^K fails for the existing K=1 compact witness.
    assert 2*ordinary(ordinary(ordinary(19)))>(6*2-3)*19
    # Omitting D<=A invalidates denominator enlargement.
    D,A,n,x=2,1,1,5
    assert D*x+2*n<=6*D*n and A*x+2*n>6*A*n
    # Omitting D>0 also invalidates it at n=0.
    D,A,n,x=0,1,0,1
    assert D*x+2*n<=6*D*n and A*x+2*n>6*A*n
    print(f'{witnesses} sub-six witnesses; {states} ordinary states; margin/deficit controls passed')


if __name__=='__main__':
    main()
