#!/usr/bin/env python3
"""Direct rational-band exits, parametric prefixes, and finite high-visit witnesses."""
import random
from test_barrier_kernel import trajectory
from generate_wider_band_arithmetic import tree, parameters


def exit_time(P, Q, b, start):
    n = start
    for k in range(18):
        if n < b or P*b < Q*n:
            return k
        n = n//2 if n % 2 == 0 else 3*n+1
    raise AssertionError((P, Q, b, start, 'accepted seventeen-step band'))


def main():
    exhaustive = large = windows = blocks = prefixes = 0
    maximum = 0
    for P, Q in [(21,4), (51,10)]:
        for b in range(2, 501):
            for n in range(P*b//Q+3):
                k = exit_time(P,Q,b,n)
                maximum = max(maximum,k)
                exhaustive += 1
        rng = random.Random(P*100+Q)
        for _ in range(10000):
            b = rng.randrange(2,10**120)
            for n in [0,b,2*b,P*b//Q,P*b//Q+1,rng.randrange(b,P*b//Q+1)]:
                maximum = max(maximum,exit_time(P,Q,b,n))
                large += 1
    assert maximum == 17
    sharp = trajectory(1010,17)
    assert sharp == [1010,505,1516,758,379,1138,569,1708,854,427,1282,
                     641,1924,962,481,1444,722,361]
    for P,Q in [(21,4),(51,10)]:
        assert all(379 <= n and Q*n <= P*379 for n in sharp[:-1])
        assert exit_time(P,Q,379,1010) == 17
    nodes = tree()
    for word,node in nodes.items():
        if not node['valid']:
            continue
        ps = parameters(node)
        for q in [0,1,2,17,65537,2**180-1]:
            values = [a*q+c for a,c in ps]
            for bit,n,m in zip(word,values,values[1:]):
                assert n%2 == int(bit)
                assert m == (n//2 if bit=='0' else 3*n+1)
            prefixes += 1
    for seed in list(range(2,2002))+[2**90-1,2**180-1]:
        values = trajectory(seed,511)
        for b in sorted({2,max(2,seed//5),max(2,seed//2),seed}):
            end = next((i for i,n in enumerate(values) if n<b),len(values))
            prefix = values[:end]
            for t in range(max(0,len(prefix)-17)):
                assert any(21*b<4*n for n in prefix[t:t+18])
                windows += 1
            witnesses = []
            for q in range(len(prefix)//18):
                s = next(i for i in range(18*q,18*q+18) if 21*b<4*prefix[i])
                witnesses.append(s)
                blocks += 1
            assert len(set(witnesses)) == len(witnesses)
    assert all(1 <= n and 4*n <= 21 for n in trajectory(1,100))
    # Changing the sign gives a trapped cycle at barrier 5.
    n = 5
    for _ in range(100):
        assert 5 <= n and 4*n <= 21*5
        n = n//2 if n%2==0 else 3*n-1
    assert 4*max(trajectory(2,17)) <= 21*2  # lower survival is essential
    print(f'{exhaustive} exhaustive and {large} large-integer band exits; maximum 17; '
          f'{prefixes} affine prefix samples; {windows} lower-surviving windows; '
          f'{blocks} distinct block witnesses; sharpness and hypothesis controls passed')


if __name__ == '__main__':
    main()
