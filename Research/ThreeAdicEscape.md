# Three-adic escape: exact finite populations and the quantifier boundary

This development starts from commit c7c0c76 on 5 October 2026. It is a small
part of the requested 20,000-line, 300-commit research programme. Those targets
are not satisfied by this batch. No proof of universal descent is claimed.

## Source-grounded directions

- Terras, *A stopping time problem on the positive integers* (1976), establishes
  the classical stopping-time approach. Almost every starting value has a
  finite stopping time in natural density. The quantifier is not every input.
  [Original paper](https://matwbn.icm.edu.pl/ksiazki/aa/aa30/aa3034.pdf).
- Allouche and Korec sharpen the typical descent scale to powers of the input;
  Korec covers exponents greater than log(3)/log(4). These results motivate
  multiscale descent but do not justify iterating uniformly sampled laws.
  [Tao's account of the results](https://terrytao.wordpress.com/2019/09/10/almost-all-collatz-orbits-attain-almost-bounded-values/).
- Tao proves that for every function tending to infinity, almost every orbit
  goes below that function, in logarithmic density. His transport argument
  addresses the changing landing distribution, which can concentrate in a
  later exceptional set. [Paper](https://arxiv.org/abs/1909.03562).
- Krasikov and Lagarias prove a lower bound with exponent 0.84 for the number
  of inputs below a cutoff that reach 1, using difference inequalities and a
  computer-assisted argument. [Paper](https://arxiv.org/abs/math/0205002).
- Barina's project reports verification below 2075 * 2^60 as accessed on
  5 October 2026. This external computation is not imported as a Lean theorem.
  [Project and source links](https://pcbarina.fit.vut.cz/).

These are established results to guide exploration. This batch does not
formalize their full analytic or computational proofs.

## Formal results added

For T(n)=n/2 on even inputs and (3n+1)/2 on odd inputs:

1. An odd input maps to 2 modulo 3.
2. `(3*m) | T(n)` iff `(6*m) | n`, including m=0.
3. `3 | T^k(n)` iff `(3*2^k) | n`, for every natural n and k.
4. For `[0,N)`, the count of surviving inputs is exactly
   `N/(3*2^k) + indicator(N % (3*2^k) != 0)`.
5. Every positive input eventually leaves the multiples of three permanently.
6. At every fixed deadline, arbitrarily large inputs still survive.
7. Zero never escapes; positivity is essential in statement 5.

The counts refer to initial values with their multiplicities. They do not
count distinct orbit outputs. The half-open interval includes zero.

The structural exclusion after an odd step is already present in
`AccumulatorArith` and `ThreeResidue`. The contribution here is a short,
independent divisibility equivalence, its exact population counts, and an
explicit formal separation of individual escape from uniform escape.
No historical novelty is asserted.

## Implication for universal descent

Escape from residue zero is automatic. Any attempt to force an arbitrary
orbit back into the multiples of three contradicts the persistent exclusion
lemma. This directs descent searches toward the two nonzero classes.

The survivor density at depth k is 1/(3*2^k), yet no fixed depth eliminates
all positive survivors. Vanishing finite-time density therefore cannot be
upgraded to uniform escape. In this example individual escape is provable by
an additional size argument; universal Collatz descent still needs its own
argument. None of these statements supplies that missing argument.

## Reproduction and evidence

```
lake build Collatz.Strategy.ThreeAdicEscapeCount Collatz.Strategy.ThreeAdicEscapeTime
lake env lean scripts/audit_three_adic_escape.lean
python3 scripts/three_adic_escape_probe.py --output Research/ThreeAdicEscapeProbe.json
```

The Python regression directly iterates the integer map for 100,000 inputs
through depth 20, compares 2,100,000 orbit/divisibility outcomes, checks 315
large-integer boundary cases, checks exact finite counts and persistent escape,
and checks the coarse individual deadline on positive inputs below 1,000.
It supplements the universal Lean proofs and is not a proof by itself.

The axiom audit lists every named theorem in all three modules. Validation
covers these modules; no full-repository build is claimed.

## Next research questions

Derive exact counts for residues one and two at every depth, and compare their
finite-time limiting bias with the Syracuse distribution in Tao's analysis.
Then test conditional distributions at first descent rather than fixed times:
the sampling rule itself changes the law, which is the relevant obstacle to
concatenating typical-descent theorems.
