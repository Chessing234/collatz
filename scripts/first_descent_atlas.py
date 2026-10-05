#!/usr/bin/env python3
"""Generate and kernel-check primitive first-descent cylinders, then commit each batch."""
import json, subprocess, hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'Collatz/Research/FirstDescent'
def orbit(n,k):
    a=0; values=[n]
    for _ in range(k):
        a+=n%2
        n=(3*n+1)//2 if n%2 else n//2
        values.append(n)
    return a,n,values

def run(args):
    p=subprocess.run(args,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    if p.returncode: raise RuntimeError(p.stdout)
    return p.stdout

def main():
    chosen=[]; census=[]
    for k in range(2,24):
        count=0
        for r in range(3,2**k,2):
            a,b,v=orbit(r,k)
            if b<r and all(x>=r for x in v[1:-1]) and 3**a<2**k:
                count+=1
                if len(chosen)<2400: chosen.append((k,r,a,b))
        census.append(dict(depth=k,primitive_classes=count))
        if len(chosen)==2400: break
    assert len(chosen)==2400
    tests=0
    for k,r,a,b in chosen:
        for m in (0,1,2,17,1024,10**12):
            aa,bb,v=orbit(2**k*m+r,k)
            assert aa==a and bb==3**a*m+b and bb<v[0]
            assert all(x>=v[0] for x in v[:-1])
            tests+=1
    run(['lake','build','Collatz.Research.DescentAtlas.Core'])
    files=[]
    for i in range(300):
        name=f'Batch{i+1:03}'
        path=BASE/(name+'.lean')
        parts=['import Collatz.Research.DescentAtlas.Core\n\n',
            f'/-! Primitive first-descent cylinders, batch {i+1}. Numerical facts are kernel checked. -/\nnamespace Collatz.Research.FirstDescent.{name}\nopen Collatz\nopen Collatz.Research.DescentAtlas\n\n']
        for k,r,a,b in chosen[i*8:(i+1)*8]:
            tag=f'{k}_{r}'
            parts.append(f'''/-- Exact endpoint and coefficient for the primitive cylinder ({k}, {r}). -/
theorem data_{tag} : oddCount {r} {k} = {a} ∧
    acceleratedOrbit {k} {r} = {b} ∧ {3**a} < {2**k} := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_{tag} : ∀ j : Fin {k},
    {r} ≤ acceleratedOrbit j.val {r} := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_{tag} (m : Nat) :
    acceleratedOrbit {k} ({2**k} * m + {r}) = {3**a} * m + {b} := by
  have h := Congruence.accOrbit_pow_two_mul_add {k} m {r}
  rw [data_{tag}.1, data_{tag}.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_{tag} (m : Nat) :
    acceleratedOrbit {k} ({2**k} * m + {r}) < {2**k} * m + {r} := by
  apply descent_of_endpoint
  · rw [data_{tag}.1]; exact data_{tag}.2.2
  · rw [data_{tag}.2.1]; decide

''')
        parts.append(f'end Collatz.Research.FirstDescent.{name}\n')
        path.write_text(''.join(parts));files.append(path)
        run(['lake','env','lean',str(path.relative_to(ROOT))])
        paths=[str(path.relative_to(ROOT))]
        if i==0: paths.append('scripts/first_descent_atlas.py')
        run(['git','add','--',*paths])
        if run(['git','diff','HEAD','--',*paths]):
            run(['git','commit','--only','-m',f'proof: verify primitive first-descent cylinders {i+1:03}', '--',*paths])
        if (i+1)%10==0: print(f'Checked and committed {i+1}/300 batches',flush=True)
    (BASE/'All.lean').write_text(''.join(f'import Collatz.Research.FirstDescent.Batch{i+1:03}\n' for i in range(300)))
    report=dict(certificates=len(chosen),batches=300,lean_lines=sum(len(p.read_text().splitlines()) for p in files),independent_tests=tests,census=census,method='lake env lean; kernel decide; each batch checked before committing',hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in files})
    (BASE/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('certificates','batches','lean_lines','independent_tests')}),flush=True)
if __name__=='__main__': main()
