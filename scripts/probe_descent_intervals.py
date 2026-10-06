#!/usr/bin/env python3
"""Finite census and hypothesis search; outputs are explicitly experimental."""
from collections import Counter
import json
from descent_intervals import REPORT, exact_interval


def main():
    rows = []
    finite_examples = []
    for k in range(1, 17):
        kinds = Counter()
        cutoffs = Counter()
        for r in range(1 << k):
            interval = exact_interval(k, r)
            kinds[interval.kind] += 1
            if interval.kind == 'tail':
                cutoffs[interval.lower] += 1
            elif interval.kind == 'finite' and len(finite_examples) < 20:
                finite_examples.append({'depth': k, 'residue': r,
                                        'lower': interval.lower, 'upper': interval.upper})
        rows.append({'depth': k, 'canonical_classes': 1 << k,
                     'empty': kinds['empty'], 'tail': kinds['tail'], 'finite': kinds['finite'],
                     'tail_cutoffs': dict(sorted(cutoffs.items()))})
        print(f"Depth {k}: {dict(kinds)}", flush=True)
    report = {
        'scope': 'Finite Python census, not a Lean proof or a general theorem',
        'max_depth': 16,
        'canonical_classes_examined': sum(row['canonical_classes'] for row in rows),
        'rows': rows,
        'finite_nonempty_examples': finite_examples,
        'open_question': 'Can a canonical exact first-descent interval be finite and nonempty at any depth?',
        'coverage_warning': 'Empty at a specified depth does not mean never descends. No finite maximum depth covers every input.'
    }
    (REPORT/'census.json').write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
