#!/usr/bin/env python3
"""Exact exploratory comparison; finite output does not prove global completeness."""
import argparse
import json


def investigate(limit, horizon):
    delayed=[]; missing=[]; matched=0
    for n in range(2,limit+1):
        v=3*(n+1 if n%2==0 else n);w=v+1
        x=n;C=D=V=W=1;first_descent=None
        for j in range(horizon+1):
            if x<n and first_descent is None:first_descent=j
            if C*W<D*V:
                assert first_descent is not None and first_descent<=j
                if first_descent==j:matched+=1
                else:delayed.append({'source':n,'first_descent':first_descent,'first_certificate':j,'delay':j-first_descent})
                break
            if x%2:
                x=(3*x+1)//2;C*=3;V*=v;W*=w
            else:x//=2
            D*=2
        else:missing.append(n)
    assert matched+len(delayed)+len(missing)==max(limit-1,0)
    return {'limit':limit,'horizon':horizon,'matched':matched,'delayed':delayed,'missing':missing,'scope':'finite exact arithmetic; no completeness or novelty claim'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--limit',type=int,default=1000000)
    parser.add_argument('--horizon',type=int,default=1000)
    args=parser.parse_args()
    if args.limit<2 or args.horizon<0:parser.error('limit >= 2 and horizon >= 0 required')
    print(json.dumps(investigate(args.limit,args.horizon),indent=2))

if __name__=='__main__':main()
