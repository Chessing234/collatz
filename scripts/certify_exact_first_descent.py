#!/usr/bin/env python3
"""Strengthen every checked endpoint cylinder to kernel-checked exact first descent."""
from pathlib import Path
import re,subprocess
ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'Collatz/Research/FirstDescent'
def main():
    chunks=['import Collatz.Research.FirstDescent.All\nimport Collatz.Research.FirstDescent.PrefixTransport\n\nnamespace Collatz.Research.FirstDescent.Exact\nopen Collatz\nopen Collatz.Research.FirstDescent\n\n']
    count=0
    for path in sorted(BASE.glob('Batch*.lean')):
        name=path.stem
        for k,r,a,b in re.findall(r'theorem data_(\d+)_(\d+) : oddCount \d+ \d+ = (\d+) ∧\n    acceleratedOrbit \d+ \d+ = (\d+)',path.read_text()):
            count+=1
            tag=f'{k}_{r}'
            chunks.append(f'''/-- Exact first descent for every member of cylinder ({k}, {r}). -/
theorem first_{tag} (m : Nat) :
    acceleratedOrbit {k} (2 ^ {k} * m + {r}) < 2 ^ {k} * m + {r} ∧
    ∀ j, j < {k} → 2 ^ {k} * m + {r} ≤
      acceleratedOrbit j (2 ^ {k} * m + {r}) := by
  apply first_descent_transport
  · rw [{name}.data_{tag}.1]; decide
  · rw [{name}.data_{tag}.2.1]; decide
  · have hp : ∀ j : Fin {k}, 2 ^ j.val ≤ 3 ^ oddCount {r} j.val ∧
        {r} ≤ acceleratedOrbit j.val {r} := by decide
    intro j hj
    exact hp ⟨j, hj⟩

''')
    assert count==2400
    chunks.append('end Collatz.Research.FirstDescent.Exact\n')
    p=BASE/'Exact.lean';p.write_text(''.join(chunks))
    subprocess.run(['lake','build','Collatz.Research.FirstDescent.Exact'],cwd=ROOT,check=True)
    print(f'Kernel checked {count} exact first-descent theorems',flush=True)
if __name__=='__main__':main()
