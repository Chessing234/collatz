#!/usr/bin/env python3
"""Exact exploratory branch search. Its output is not a Lean certificate."""
import argparse
import json
import generate_wider_band_arithmetic as guide


def explore(P,Q,horizon,node_budget):
    guide.configure(P,Q,horizon,'ExploratoryGuide',1)
    nodes=leaves=max_cut=frontiers=0
    deepest=-1
    witness=None
    exhausted=False
    def walk(word,states,r,m):
        nonlocal nodes,leaves,max_cut,frontiers,deepest,witness,exhausted
        if nodes>=node_budget:
            exhausted=True
            return
        nodes+=1
        interval=guide.domain(states,r,m)
        if interval is None:
            leaves+=1
            max_cut=max(max_cut,len(word))
            return
        if len(word)>deepest:
            deepest=len(word)
            n=interval[2]
            values=[(a*n+c)//d for a,c,d in states]
            b=min(values)
            assert all(b<=v and Q*v<=P*b for v in values)
            actual=n
            for expected in values:
                assert actual==expected
                actual=actual//2 if actual%2==0 else 3*actual+1
            witness={'start':n,'barrier':b,'through':len(word),'next_state':actual}
        if len(word)==horizon:
            frontiers+=1
            return
        a,c,d=states[-1]
        for bit in (0,1):
            modulus=2*d
            residue=(pow(a,-1,modulus)*(bit*d-c))%modulus
            if (r-residue)%min(m,modulus):
                nodes+=1;leaves+=1;max_cut=max(max_cut,len(word)+1)
                continue
            nr,nm=(residue,modulus) if modulus>m else (r,m)
            state=(a,c,2*d) if bit==0 else (3*a,3*c+d,d)
            walk(word+str(bit),states+[state],nr,nm)
            if exhausted:
                return
    walk('',[(1,0,1)],0,1)
    closed=not exhausted and frontiers==0
    if closed:
        assert deepest+1==max_cut
        assert witness['next_state']<witness['barrier'] or P*witness['barrier']<Q*witness['next_state']
    return {'numerator':P,'denominator':Q,'horizon':horizon,'nodes':nodes,
            'terminal_branches':leaves,'open_frontiers':frontiers,
            'budget_exhausted':exhausted,'fully_closed':closed,
            'candidate_clock':max_cut if closed else None,'witness':witness}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ratios',nargs='+',default=['11/2','23/4'])
    parser.add_argument('--horizon',type=int,default=100)
    parser.add_argument('--node-budget',type=int,default=100000)
    args=parser.parse_args()
    assert 0<args.horizon<500 and args.node_budget>0
    for ratio in args.ratios:
        P,Q=map(int,ratio.split('/'))
        print(json.dumps(explore(P,Q,args.horizon,args.node_budget)),flush=True)


if __name__=='__main__':
    main()
