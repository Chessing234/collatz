#!/usr/bin/env python3
"""Generate and individually verify a complete new dyadic first-descent census.

Every batch covers a disjoint range of (depth,residue) pairs. The generated
proofs classify infinite classes, including failures. Batches are certificate
units, not separate discoveries. --commit checks each before its own commit.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import time
from descent_intervals import exact_interval, trace, row_source
from generate_stopping_census import census_source

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'Collatz/Research/StoppingAtlas'
REPORT = ROOT / 'Research/StoppingAtlas'
BASELINE = 'a4bb6ce3d4163f091e7951d976d7073086c94ef1'
BATCH_COUNT = 1000
DEPTHS = (10, 11, 12, 13)


def generated():
    rows=[]
    for k in DEPTHS:
        for r in range(1 << k):
            states,counts=trace(r,k)
            interval=exact_interval(k,r)
            rows.append({'depth':k,'residue':r,'odd_count':counts[-1],
                         'endpoint':states[-1],'lower':interval.lower,
                         'upper':interval.upper,'kind':interval.kind})
    files={};batches=[]
    for i in range(BATCH_COUNT):
        start=len(rows)*i//BATCH_COUNT;stop=len(rows)*(i+1)//BATCH_COUNT
        name=f'Batch{i+1:04}'
        content=('import Collatz.Research.DescentIntervals.Classifier\n\n'
                 f'namespace Collatz.Research.StoppingAtlas.{name}\n\n'
                 'open Collatz.Research.DescentIntervals\n\n'
                 'set_option maxRecDepth 20000\nset_option maxHeartbeats 0\n\n')
        content+=''.join(row_source(row) for row in rows[start:stop])
        content+=f'end Collatz.Research.StoppingAtlas.{name}\n'
        files[LEAN/f'{name}.lean']=content
        batches.append({'module':name,'start':start,'stop':stop,
                        'sha256':hashlib.sha256(content.encode()).hexdigest()})
    files[LEAN/'Certificates.lean']=''.join(
        f'import Collatz.Research.StoppingAtlas.{b["module"]}\n' for b in batches)
    files[LEAN/'Census.lean']=census_source()
    return files,{'baseline':BASELINE,'depths':DEPTHS,'batch_count':BATCH_COUNT,
                  'cylinder_count':len(rows),'certificate_theorems':4*len(rows),
                  'batches':batches,'rows':rows}


def write_or_check(check=False):
    files,manifest=generated()
    files[REPORT/'manifest.json']=json.dumps(manifest,indent=2)+'\n'
    for p,s in files.items():
        if check:
            if not p.is_file() or p.read_text()!=s:
                raise RuntimeError(f'generated output differs: {p.relative_to(ROOT)}')
        else:
            p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
    print(f'{"Checked" if check else "Generated"} {len(manifest["rows"])} distinct cylinders in {BATCH_COUNT} batches',flush=True)
    return manifest


def checked_build(batch):
    name=batch['module'];begin=time.monotonic()
    p=subprocess.run(['lake','build',f'Collatz.Research.StoppingAtlas.{name}'],
                     cwd=ROOT,capture_output=True,text=True)
    text=p.stdout+p.stderr
    if p.returncode:
        (REPORT/f'{name}.failure.log').write_text(text)
        raise RuntimeError(f'kernel build rejected {name}; see failure log')
    return {'module':name,'source_sha256':batch['sha256'],'build_exit_code':p.returncode,
            'seconds':round(time.monotonic()-begin,3),
            'build_output_sha256':hashlib.sha256(text.encode()).hexdigest()}


def git_write(arguments):
    """Retry transient index-lock contention without touching another process's lock."""
    for attempt in range(30):
        result=subprocess.run(['git',*arguments],cwd=ROOT,capture_output=True,text=True)
        if result.returncode==0:return
        if 'index.lock' not in result.stderr:
            raise RuntimeError(result.stderr)
        time.sleep(min(0.1*(attempt+1),2))
    raise RuntimeError(result.stderr)


def commit_batches(manifest,jobs):
    # The shared import must be up to date before independent module builds.
    subprocess.run(['lake','build','Collatz.Research.DescentIntervals.Classifier'],cwd=ROOT,check=True)
    receipts=[]
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        results=pool.map(checked_build,manifest['batches'])
        for batch,receipt in zip(manifest['batches'],results):
            name=batch['module'];relative=f'Collatz/Research/StoppingAtlas/{name}.lean'
            tracked=subprocess.run(['git','ls-files','--error-unmatch',relative],
                cwd=ROOT,capture_output=True).returncode==0
            clean=tracked and subprocess.run(['git','diff','--quiet','HEAD','--',relative],cwd=ROOT).returncode==0
            if not clean:
                git_write(['add','--',relative])
                first,last=manifest['rows'][batch['start']],manifest['rows'][batch['stop']-1]
                message=f'proof: certify atlas {name} ({first["depth"]}:{first["residue"]} to {last["depth"]}:{last["residue"]})'
                git_write(['commit','--only','-m',message,'--',relative])
            receipt['commit']=subprocess.check_output(['git','log','-1','--format=%H','--',relative],cwd=ROOT,text=True).strip()
            receipts.append(receipt)
            (REPORT/'batch-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
            print(f'{name}: checked and {"already committed" if clean else "committed"} {batch["stop"]-batch["start"]} classes',flush=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true');parser.add_argument('--commit',action='store_true')
    parser.add_argument('--jobs',type=int,default=4)
    args=parser.parse_args()
    if not 1<=args.jobs<=8:parser.error('jobs must be between 1 and 8')
    manifest=write_or_check(args.check)
    if args.commit:commit_batches(manifest,args.jobs)

if __name__=='__main__':main()
