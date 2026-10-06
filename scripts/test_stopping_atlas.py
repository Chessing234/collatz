#!/usr/bin/env python3
"""Independent integer-orbit, finite-counting, and gap-certificate checks."""
from collections import Counter
import json
from stopping_atlas import REPORT, write_or_check


def direct(n, horizon):
    """Scalar iteration: deliberately independent of the interval solver."""
    start=n; a=0; first=None; crossing=None
    for k in range(1,horizon+1):
        a+=n&1
        n=(3*n+1)//2 if n&1 else n//2
        if first is None and n<start:first=k
        if crossing is None and 3**a<1<<k:crossing=k
    return first,crossing,n,a


def main():
    manifest=write_or_check(True); checks=Counter(); census={}
    for row in manifest['rows']:
        k,r=row['depth'],row['residue']; totals=census.setdefault(k,Counter())
        totals[row['kind']]+=1
        for m in (0,1,2,17,1<<80):
            n=(1<<k)*m+r
            first,crossing,end,a=direct(n,k)
            belongs=row['lower']<=m and (row['upper'] is None or m<row['upper'])
            assert (first==k)==belongs,(row,m,first)
            assert end==3**row['odd_count']*m+row['endpoint']
            assert a==row['odd_count']
            checks['class_samples']+=1
        assert row['kind']!='finite'
    # Independent validation of every exceptional start used by the horizon bridge.
    max_crossing=0
    for n in range(2,99730):
        first,crossing,_,_=direct(n,135)
        assert first is not None and first==crossing,(n,first,crossing)
        max_crossing=max(max_crossing,crossing)
        checks['exceptional_starts']+=1
    # Exhaust every light odd count, not merely the checker's maximal candidate.
    p3=[3**a for a in range(1540)]
    max_required=0; worst=[]
    for k in range(1,1539):
        p2=1<<k
        for a in range(k+1):
            if p3[a]>=p2:break
            threshold=a*p3[a]//(3*(p2-p3[a]))+1
            assert threshold<=99730,(k,a,threshold)
            if threshold>max_required:max_required=threshold;worst=[k,a]
            checks['gap_pairs']+=1
    threshold=971*p3[971]//(3*((1<<1539)-p3[971]))+1
    assert threshold==330588 and threshold>99730
    checks['boundary_failure']+=1
    # First-passage partition at arbitrary cutoffs, with exact integer arithmetic.
    for N in (0,1,2,3,31,64,101,257,1025):
        events=[0]*21; survival=[0]*21
        for n in range(2,N+2):
            _,crossing,_,_=direct(n,20)
            if crossing is not None:events[crossing]+=1
            for h in range(21):survival[h]+=crossing is None or crossing>h
        for h in range(21):
            assert sum(events[:h+1])+survival[h]==N
            if h<20:assert survival[h]==survival[h+1]+events[h+1]
            checks['conservation_cutoffs']+=1
    # Exhaust all short binary periods and several prefixes/full periods.
    for M in range(1,11):
        for mask in range(1<<M):
            bits=[(mask>>i)&1 for i in range(M)]; A=sum(bits)
            C=0
            for N in range(3*M+1):
                assert C==(N//M)*A+sum(bits[:N%M])
                assert abs(M*C-N*A)<=A*(M-A)
                checks['period_discrepancies']+=1
                if N<3*M:C+=bits[N%M]
    # False hypotheses are detected independently of Lean's rejection controls.
    assert direct(1,2)[0] is None
    assert direct(3,5)[0]==4
    assert census[11]['tail']==0
    report={'status':'passed','checks':dict(checks),'total_checks':sum(checks.values()),
            'census':census,'exceptional_max_crossing':max_crossing,
            'gap_max_required':max_required,'gap_worst_pair':worst,
            'next_threshold':threshold,'randomness':'none; deterministic exhaustive bounded checks',
            'limitation':'Sampled class indices supplement, but do not replace, universally quantified Lean proofs.'}
    (REPORT/'python-tests.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
