# Terminal dependence and the finite-to-infinite gap

2026-09-28. These are finite algebraic identities and explicit examples,
not a proof of universal descent. No research novelty is claimed.

Let c_i be the division coefficients and let
P_L = product_{i<L}(c_i/3). Backward propagation uses
e_i=(c_i e_(i+1)+1)/3. If B_L(z) denotes the initial value obtained from
terminal value z, then

    B_L(z)-B_L(w) = P_L (z-w).

The existing terminal-one encoder E_L=B_L(1) also satisfies, on an actual
finite integer trajectory c_i x_(i+1)=3x_i+1,

    x_0 + E_L = P_L (x_L+1).

Both identities are now checked in core Lean in
`Collatz/Strategy/ShadowTerminal.lean`. They explicitly preserve the terminal
term; a limiting argument must justify how it behaves. Neither identity
supplies a bound uniform in L.

Two exact tests prevent invalid implications:

* All c_i=2: E_L=1 for every L. The constant infinite shadow e_i=1 is
  perfectly compatible. Nevertheless no infinite natural-number trajectory
  can obey 2x_(i+1)=3x_i+1. Such a trajectory would make every 2^L divide
  x_0+1, a fixed positive integer. Thus even compatible bounded shadow
  data do not imply natural-number realizability.
* All c_i=4: the actual Syracuse fixed orbit x_i=1 satisfies the integer
  recurrence, but E_L=2(4/3)^L-1. Thus finite integer realizability, even
  infinite realizability, does not automatically bound terminal-one encodings.

These examples do not exclude an injective positive integer orbit, nor do
they refute a claim made specifically under injectivity. In the earlier
Mathlib development, bounded inverse sums on injective orbits required a
separate reciprocal-summability theorem. That development has not been
rebuilt here; this result uses no dependency on it.

The new conclusion for the current research direction is that three distinct
requirements must not be conflated: finite certificate existence, compatible
infinite shadow data, and realization by one natural-number start. A proof
must bridge the last requirement using arithmetic beyond these examples.
This is an audit of one approach, not a general impossibility theorem.

Verification:

    lake build Collatz.Strategy.ShadowTerminal
    lake env lean scripts/audit_shadow_terminal.lean

Evidence is in `Research/ShadowTerminalBuild.txt` and
`Research/ShadowTerminalAudit.txt`. Seven theorem endpoints are audited;
only standard Lean axioms are allowed. No new axioms or proof placeholders.
