# Proof attempt: a logarithmic descent bound

Date: 2026-09-28. Outcome: Collatz remains unproved. A proposed sufficient
hypothesis in this repository was refuted, not established.

## Attempt and exact result

For the accelerated map T(n)=n/2 on even inputs and (3n+1)/2 on odd inputs,
try to prove that each n>1 has some k ≤ C floor(log₂ n) with T^k(n)<n.
Such a bound would imply Collatz by strong induction, as already formalized
in `DriftSurvivors.collatz_of_logBlockDescentWithin`.

The repository listed C=17 as a live candidate. Checking published glide
records supplies n=1008932249296231, for which Lean proves:

- floor(log₂ n)=49;
- T^j(n)≥n for every j≤885;
- T^886(n)=1004771328803533<n.

Since 18×49=882<886, the proposed bound is false for every natural C≤18.
The same witness refutes the tail-only hypothesis above 3998720. The
conditional theorem “that hypothesis implies Collatz” remains valid; its
hypothesis cannot be supplied.

## Proof mechanism

`staysAbove threshold fuel x` checks a single trajectory once, including its
initial and terminal states. An inductive soundness theorem converts its
Boolean result into a universal inequality for every iterate through fuel.
The 885-step certificate and the 886th iterate are computed by ordinary
Lean `decide`, checked by the kernel. No external computation is assumed in
the theorem. `not_log_bound` and `not_tail_bound` then follow by arithmetic.

Source: `Collatz/Strategy/LogBlockRecord.lean`.
Audit: `scripts/audit_log_block_record.lean`.
Axiom output: `Research/LogBlockRecordAxioms.txt`.

## Follow-up search and remaining gap

A deterministic perturbation search changed the published seed by
δ·2^b for 1≤b≤80 and −512≤δ≤512, retaining positive inputs greater than one
and deduplicating them. All 31435 candidates descended within the 10000-step
cap. None refuted constant 19. The largest observed ratio was 886/49.
The script uses Python arbitrary-precision integers; it is an exploratory
search, not a Lean certificate or exhaustive range verification.

Reproduce with `python3 scripts/log_bound_probe.py`; exact output is in
`Research/LogBlockRecordProbe.json`.

The remaining proof obligation is still a universal descent estimate. A
finite collection of successful trajectories, an average negative drift,
or a density-one result cannot discharge it. In particular, this attempt
does not prove that C=19 works or that any universal constant exists.

## Literature and novelty audit

The seed, glide 1445, and accelerated stopping time 886 already occur as g_30
in Table 3 of Eliahou and Simonetto's
[arXiv:2107.11160v2](https://arxiv.org/html/2107.11160v2#S2.SS1).
It is also in [Roosendaal's glide-record table](http://www.ericr.nl/wondrous/glidrecs.html),
retrieved during this attempt. Python recomputation of all 34 listed seeds
agreed with the listed glides after accounting for omitted forced even steps.
No new mathematical record or historical novelty is claimed.

The repository previously misattributed that paper to O. Rozier and equated
its falling-time conjecture with the present fixed-logarithm bound. The
paper's jump lengths depend on the current iterate, not just the starting
number; these are distinct statements. The literature screen here is narrow:
this paper and glide table establish prior art for the witness, not a
comprehensive survey of all possible logarithmic bounds.

## Verification scope

`lake build Collatz.Strategy.LogBlockRecord` passed (3 jobs).
`lake env lean scripts/audit_log_block_record.lean` passed. The computational
certificates use no axioms; the soundness and final results use only
`propext` and `Quot.sound`. No Mathlib or proof placeholders are used.

The full repository build/integrity check was not completed for this attempt.
Only the narrow new target and its explicit audit were run. Existing unrelated
work and the concurrently present PeriodicTwoDefectAll module were not changed.
