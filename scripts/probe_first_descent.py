#!/usr/bin/env python3
"""Independent probes: prefix transport, cylinder disjointness, ranking, inverse search."""
from fractions import Fraction
from pathlib import Path
import json,re
ROOT=Path(__file__).resolve().parents[1]
def step(n): return (3*n+1)//2 if n%2 else n//2
def main():
    selected=[]
    for p in sorted((ROOT/'Collatz/Research/FirstDescent').glob('Batch*.lean')):
        selected.extend(tuple(map(int,m)) for m in re.findall(r'theorem data_(\d+)_(\d+) : oddCount \d+ \d+ = (\d+) ∧\n    acceleratedOrbit \d+ \d+ = (\d+)',p.read_text()))
    assert len(selected)==2400
    coefficient_checks=0
    seen=set();coverage=Fraction(0)
    for k,r,a,b in selected:
        assert 0<r<2**k
        # A prefix ancestor would mean two certificates describe overlapping cylinders.
        assert all((j,r%(2**j)) not in seen for j in range(k))
        assert (k,r) not in seen
        seen.add((k,r));coverage+=Fraction(1,2**k)
        n=r;odd=0
        for j in range(k):
            assert n>=r and 2**j<=3**odd
            coefficient_checks+=1
            odd+=n%2;n=step(n)
        assert n==b and odd==a and n<r
    # Actual descent is tested independently, rather than inferred from density.
    worst=(0,0);hist={}
    for start in range(2,500001):
        n=start
        for k in range(1,2001):
            n=step(n)
            if n<start:
                worst=max(worst,(k,start));hist[k]=hist.get(k,0)+1;break
        else: raise AssertionError(('fuel exhausted',start))
    # Inverse edges are genuine predecessors; inverse density alone does not prove
    # that every forward orbit intersects this tree.
    frontier={1};tree={1};sizes=[]
    for depth in range(1,21):
        nxt=set()
        for x in frontier:
            nxt.add(2*x)
            if x%3==2:
                y=(2*x-1)//3
                assert y%2==1 and step(y)==x
                nxt.add(y)
        for y in nxt: assert step(y) in frontier
        frontier=nxt-tree;tree|=nxt;sizes.append(len(tree))
    report=dict(selected_cylinders=2400,prefix_coefficient_checks=coefficient_checks,
      pairwise_disjoint=True,selected_natural_density=str(coverage),
      selected_natural_density_decimal=float(coverage),
      odd_integer_coverage_fraction=float(2*coverage),
      finite_descent=dict(limit=500000,fuel=2000,worst_steps=worst[0],witness=worst[1],histogram=hist),
      inverse_tree_sizes=sizes,
      ranking_obstruction=dict(input=3,endpoint=step(3)),
      scope='Computational checks only. Density is of selected residue cylinders, not all convergent integers. No universal descent conclusion.')
    (ROOT/'Collatz/Research/FirstDescent/experiments.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('selected_cylinders','prefix_coefficient_checks','selected_natural_density','odd_integer_coverage_fraction')}))
if __name__=='__main__':main()
