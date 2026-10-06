#!/usr/bin/env python3
"""Check that all 1000 individually verified batches retain distinct commits.

Run in a full checkout after --commit, not GitHub's default shallow checkout.
This checks provenance and history, not mathematics; use the Lean audit for that.
"""
import argparse
import hashlib
import json
import subprocess
from passage_atlas import BASELINE, REPORT, ROOT, write_or_check


def git(*args):
    return subprocess.check_output(['git',*args],cwd=ROOT)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--read-only', action='store_true', help='verify current reachability without updating the saved snapshot')
    args = parser.parse_args()
    manifest=write_or_check(True)
    receipts=json.loads((REPORT/'batch-receipts.json').read_text())
    assert len(receipts)==1000
    by_module={receipt['module']:receipt for receipt in receipts}
    assert len(by_module)==1000
    assert len({receipt['commit'] for receipt in receipts})==1000
    subprocess.run(['git','merge-base','--is-ancestor',BASELINE,'HEAD'],cwd=ROOT,check=True)
    new=set(git('rev-list',f'{BASELINE}..HEAD').decode().splitlines())
    for batch in manifest['batches']:
        receipt=by_module[batch['module']]
        assert receipt['build_exit_code']==0
        assert receipt['source_sha256']==batch['sha256']
        assert receipt['commit'] in new
        path=f'Collatz/Research/PassageAtlas/{batch["module"]}.lean'
        blob=git('show',f'{receipt["commit"]}:{path}')
        assert hashlib.sha256(blob).hexdigest()==batch['sha256']
        changed=git('diff-tree','--no-commit-id','--name-only','-r',receipt['commit']).decode().splitlines()
        assert changed==[path],(receipt['commit'],changed)
    result={'status':'passed','baseline':BASELINE,
            'batch_commits':1000,'new_commits_at_check':len(new),
            'head_at_check':git('rev-parse','HEAD').decode().strip(),
            'checks':['baseline is ancestor','distinct commits','each commit changes only its own batch',
                      'historical source matches certified manifest','all batch commits reachable from HEAD']}
    if not args.read_only:
        (REPORT/'history-verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
