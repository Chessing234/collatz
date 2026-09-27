# Counting predecessors using the exact Syracuse energy

2026-09-08. Collatz remains unproved. This development replaces the
worst-case pointwise bound in the terminal comparison with a bound involving
the actual finite collision energy. It does not assert an upper growth
rate for that energy beyond the elementary exponential bound below.
The subsequent [energy upper-bound argument](SyracuseEnergyUpper.md)
improves that bound to E_n<=(5/3)^n. The subsequent
[residue-class refinement](SyracuseEnergyClasses.md) proves
E_n<=(35/27)(9/7)^n, still exponential.

Let mu_m be the actual imported Syracuse probability law on Z/3^m Z and set

    E_m = 3^m sum_r mu_m(r)^2.

For the ordinary Collatz map, let P_a(X) count positive integers below X
whose orbit reaches a. The new unconditional Lean endpoint is
`energy_target_density`:

    For every integer A>=1, there exist K>=1 and d>0 such that
    for every positive a with 3 not dividing a,
    every t>=1 with a<=t^A,
    and every sufficiently large X,

        P_a(X) >= d X / (a^2 E_(K t)).

K,d are independent of a,t; the cutoff in X may depend on a,t. The theorem
keeps the energy of the literal Syracuse law in its conclusion. There is
no hypothesis asserting that this energy grows linearly or polynomially.
The count uses the ordinary map and has no imposed hitting-time cutoff.

## The comparison

Write P for the physical source potential, F for the full terminal mass,
and T for the marked terminal mass. The earlier proof used the maximum of
a density at coarse conductor m. Instead, for every H>0, the elementary
inequality

    f <= H + f^2/(4H)

follows from (f-2H)^2>=0. Applying the existing weighted residue census to
f^2 gives the new terminal estimate

    T <= (4/3) H F + (44/9) P E_m/H + 44 P epsilon,

where epsilon bounds the L1 difference between the fine and coarse
Syracuse densities. The density normalized against units has full-Haar
second moment (4/9)E_m; this factor is kept explicitly in Lean. Every
affine fan map preserves full-Haar mean, and the sum of its geometric
coefficients is at most 4/3.

The previously proved activation supplies T>=alpha>0 and a nonperiodic
seed with P=M<=Ca, using the same alpha,C for all odd eligible targets.
Taking m=Kt pays 44P epsilon<=alpha/2 whenever a<=t^A. Choosing

    H = 24 P E_m/alpha

then proves the convenient lower bound

    F >= alpha^2/(256 P E_m).

The existing count assembly divides this by 32P. Thus the odd-target
density is at least alpha^2/(8192 C^2 a^2 E_m). An odd fertile ordinary
predecessor c<=9a transfers the conclusion to even targets, adjusting
K,d by fixed factors. The square in a records this additional source
potential cost; it has not been dropped from the conclusion.

## What would improve this, and what remains beyond it

The new module also proves E_m<=2^m from the imported atom-height bound
mu_m(r)<=(2/3)^m. Together with the previous lower bound, the proved
range is

    1+c m <= E_m <= 2^m    (bound at this stage)

for some absolute c>0. The lower bound rules out uniformly bounded E_m.
It does not rule out an upper bound E_m<=B m.
The later upper bounds (5/3)^m and then (35/27)(9/7)^m improve the
upper end of this proved range.

`cubic_target_density_of_linear_energy` proves the conditional implication

    (exists B>0, forall m>=1, E_m<=B m)
        implies
    (exists d>0, forall eligible a, eventually P_a(X)>=d X/a^3).

The energy hypothesis is displayed in the theorem's Lean signature and
remains unproved. For the unrestricted exponent A, a polynomial energy
estimate E_m<=B m^s would similarly give denominator a^2 t^s, with constants
depending on A,s,B. None of these density conclusions alone establishes
descent of every positive integer greater than one. Eliminating all
exceptional deterministic orbits remains a separate unresolved obligation.

The finite probe through m=14 gives E_14 approximately 7.74276829 and
E_14-E_13 approximately 0.47025433. The first five energies are checked
against full-period rational laws; later values are floating-point
exploration, with rounding not certified. Neither these values nor the
apparent growth pattern prove a bound for all m. The probe is reproducible
with `python3 scripts/syracuse_energy_probe.py --levels 14`; its saved output
is [SyracuseEnergyProbe.jsonl](SyracuseEnergyProbe.jsonl).

A related primary
[Lean repository by Nathan Humphrey](https://github.com/mrnathanhumphrey-droid/Collatz_Repo_Lean_Proofs)
records small-level Plancherel increments and explicitly leaves its proposed
limit 7/15 and convergence rate unproved. A subsequent check of the author's
[main research repository](https://github.com/mrnathanhumphrey-droid/Collatz)
found that its July 28 update withdraws the 7/15 target and reports a different
candidate value near 0.475. That later asymptotic argument has not been
independently verified here. Neither value, nor any source from those
repositories, is imported or treated as an all-depth energy theorem.
In particular the author's [R9-C section](https://github.com/mrnathanhumphrey-droid/Collatz/blob/main/results/result_gamma_R9.md)
reports finite correlation columns; it does not prove their boundedness
at every depth. The new local exponential bound has its own Lean proof.
No historical priority is claimed for the local energy comparison.

The analytic dependencies remain the pinned Tao–Mazur development, including
Mazur's [positive-density source package](https://www.proofatlas.ai/sources/positive-density-log-time-collatz/).
The distinction between such distributional estimates and full convergence
is also present in Tao's
[discussion of Syracuse laws and preimages](https://terrytao.wordpress.com/2020/01/25/equidistribution-of-syracuse-random-variables-and-density-of-collatz-preimages/).

## Formal files and verification

- [Energy comparison and normalization](../ProofAtlasAttack/CollatzTargetDensity/EnergyUnmark.lean)
- [Ordinary predecessor-count bound](../ProofAtlasAttack/CollatzTargetDensity/EnergyTargets.lean)
- [Literal endpoints and transitive axiom audit](../ProofAtlasAttack/Verification/EnergyTargets.lean)

Run `LEAN_NUM_THREADS=4 python3 scripts/verify.py` from `ProofAtlasAttack`.
That stage's complete build and axiom audit passed: 69 endpoints, including ten added
here, and all 1,485 upstream source hashes unchanged. The audited statements
use only `propext`, `Classical.choice`, and `Quot.sound`. There are no
unfinished proofs or added mathematical axioms in these modules. The current
extension hashes were matched against that stage's successful report at
`ProofAtlasAttack/verification/local-report.json`; the new transcript is
`ProofAtlasAttack/verification/energy-targets-axioms.log`. This is local Lean
verification, not an independent mathematical review.
