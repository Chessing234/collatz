#!/usr/bin/env python3
"""Direct rational-band exits, parametric prefixes, and finite high-visit witnesses."""
import random
from test_barrier_kernel import trajectory
import generate_wider_band_arithmetic as guide
from generate_wider_band_arithmetic import tree, parameters
guide.configure(11,2,30,'ElevenHalvesArithmetic',235)


def exit_time(P, Q, b, start):
    n = start
    for k in range(31):
        if n < b or P*b < Q*n:
            return k
        n = n//2 if n % 2 == 0 else 3*n+1
    raise AssertionError((P, Q, b, start, 'accepted thirty-step band'))


def main():
    exhaustive = large = windows = blocks = prefixes = 0
    maximum = 0
    for P, Q in [(11,2)]:
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
    sharp = trajectory(201714,30)
    assert min(sharp[:-1]) == 71803 and max(sharp[:-1]) == 382948
    assert sharp[-1] == 68158
    assert all(71803 <= n and 2*n <= 11*71803 for n in sharp[:-1])
    assert exit_time(11,2,71803,201714) == 30
    assert exit_time(382948,71803,71803,201714)==30
    maximum = max(maximum,30)
    assert maximum == 30
    family = 0
    for q in list(range(1000))+[2**180-1,2**180,10**120-1,10**120]:
        start=262144*q+201714
        barrier=93312*q+71803
        peak=497664*q+382948
        values=trajectory(start,30)
        assert min(values[:30])==barrier and max(values[:30])==peak
        assert values[17]==barrier and values[12]==peak
        assert 3*peak+4==16*barrier
        for P,Q in [(16,3),(27,5),(11,2),(54,10)]:
            assert all(barrier<=x and Q*x<=P*barrier for x in values[:30])
            assert exit_time(P,Q,barrier,start)==30
        if q%2==0:
            assert values[30]==177147*(q//2)+68158 and values[30]<barrier
        else:
            assert values[30]==1062882*(q//2)+940390 and 11*barrier<2*values[30]
        family+=1
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
            for t in range(max(0,len(prefix)-30)):
                assert any(11*b<2*n for n in prefix[t:t+31])
                windows += 1
            witnesses = []
            for q in range(len(prefix)//31):
                s = next(i for i in range(31*q,31*q+31) if 11*b<2*prefix[i])
                witnesses.append(s)
                blocks += 1
            assert len(set(witnesses)) == len(witnesses)
    assert all(1 <= n and 2*n <= 11 for n in trajectory(1,100))
    # Changing the sign gives a trapped cycle at barrier 5.
    n = 5
    for _ in range(100):
        assert 5 <= n and 2*n <= 11*5
        n = n//2 if n%2==0 else 3*n-1
    assert 2*max(trajectory(2,30)) <= 11*2  # lower survival is essential
    from explore_band_clocks import explore
    complete=explore(11,2,30,10000)
    short=explore(11,2,29,10000)
    limited=explore(11,2,30,10)
    assert complete['fully_closed'] and complete['candidate_clock']==30
    assert not short['fully_closed'] and short['open_frontiers']>0
    assert limited['budget_exhausted'] and limited['candidate_clock'] is None
    print(f'{exhaustive} exhaustive and {large} large-integer band exits; maximum 30; '
          f'{prefixes} affine prefix samples; {windows} lower-surviving windows; '
          f'{blocks} distinct block witnesses; {family} infinite-family samples; sharpness and hypothesis controls passed')


if __name__ == '__main__':
    main()
