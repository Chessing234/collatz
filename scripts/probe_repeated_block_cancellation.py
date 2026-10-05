"""Exact finite regression; not a replacement for the quantified Lean proofs."""
import itertools
import json
import math
from pathlib import Path


def coefficients(word):
    c = 0
    for i, bit in enumerate(word):
        if bit:
            c = 3 * c + 2**i
    return 3 ** sum(word), 2 ** len(word), c


def main():
    words = [w for length in range(1, 8)
             for w in itertools.product((0, 1), repeat=length)]
    counts = dict(instances=0, exact_formula_instances=0,
                  nonzero_defect_instances=0, direct_word_checks=0,
                  missing_coprime_failures=0)
    for u in words:
        a, b, c = coefficients(u)
        gu = b-a
        for v in [()] + words:
            av, bv, cv = coefficients(v)
            gv = bv-av
            defect = gu*cv-c*gv
            aw, bw, cw = av, bv, cv
            for k in range(13):
                if not (k == 0 and not v):
                    gap = bw-aw
                    d = math.gcd(cw, gap)
                    counts['instances'] += 1
                    assert gu*cw-c*gap == b**k*defect
                    assert defect % d == 0
                    if defect:
                        counts['nonzero_defect_instances'] += 1
                        assert d <= abs(defect)
                        assert abs(gap) <= (abs(gap)//d)*abs(defect)
                    if math.gcd(gu, gv) == 1:
                        counts['exact_formula_instances'] += 1
                        assert d == math.gcd(defect, gap)
                    elif d != math.gcd(defect, gap):
                        counts['missing_coprime_failures'] += 1
                    if len(u) <= 3 and len(v) <= 3 and k <= 4:
                        counts['direct_word_checks'] += 1
                        assert (aw, bw, cw) == coefficients(u*k+v)
                cw, aw, bw = aw*c+b*cw, a*aw, b*bw
    two_block_checks = 0
    coprime_sum_checks = 0
    small_words = [w for w in words if len(w) <= 5]
    for u in small_words:
        a, b, c = coefficients(u)
        for v in small_words:
            av, bv, cv = coefficients(v)
            defect = (b-a)*cv-c*(bv-av)
            for k in range(7):
                su = (b**k-a**k)//(b-a)
                for l in range(7):
                    if k+l == 0:
                        continue
                    sv = (bv**l-av**l)//(bv-av)
                    aw, bw, cw = coefficients(u*k+v*l)
                    common = math.gcd(cw, bw-aw)
                    s = math.gcd(su, sv)
                    assert (abs(defect)*s) % common == 0
                    two_block_checks += 1
                    if s == 1 and defect:
                        assert common <= abs(defect)
                        coprime_sum_checks += 1
    report = dict(status='passed', scope='all nonempty binary u of length <=7; '
                  'all binary v of length <=7; 0<=k<=12', counts=counts,
                  proof_status='finite regression only; see Lean for all k',
                  two_block_scope='nonempty u,v of length <=5; 0<=k,l<=6; k+l>0',
                  two_block_checks=two_block_checks,
                  coprime_sum_checks=coprime_sum_checks)
    path = Path(__file__).resolve().parents[1] / 'Research/RepeatedBlockCancellationProbe.json'
    path.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
