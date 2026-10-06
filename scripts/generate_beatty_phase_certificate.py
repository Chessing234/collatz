#!/usr/bin/env python3
"""Reproduce the rational phase partition used in BeattyBlockPotential.lean.

Run with --check to compare the checked-in proof, or --write to replace its
marked generated section. Without an option, print the generated Lean text.
The generator is not trusted: each resulting region and the covering theorem
are checked by Lean's kernel using exact integer arithmetic.
"""
from argparse import ArgumentParser
from fractions import Fraction
from pathlib import Path


def certificate() -> str:
    # Each phase y/x lies in (low, high].  y_j = multiplier*y, while the
    # Horner accumulator before step j is accumulator*y.
    states = [(Fraction(1, 2), Fraction(1), 1, 0, [])]
    for j in range(11):  # the twelfth summand needs eleven transitions
        following = []
        for low, high, multiplier, accumulator, history in states:
            cut = Fraction(3 ** (j + 1), 4 * multiplier)
            for left, right, factor in (
                (low, min(high, cut), 4),
                (max(low, cut), high, 2),
            ):
                if left < right:
                    following.append((
                        left, right, factor * multiplier,
                        3 * accumulator + multiplier,
                        history + [(3**j, multiplier, factor * multiplier)],
                    ))
        states = sorted(following)

    lines = []
    for index, (low, high, _, _, history) in enumerate(states):
        lines.extend([
            f"private theorem phase_interval_{index} (x y : Nat)",
            f"    (hl : {low.numerator}*x < {low.denominator}*y) "
            f"(hh : {high.denominator}*y ≤ {high.numerator}*x) :",
            "    phaseRun 12 x y 0 < 1594323*x := by",
        ])
        for j, (power_three, before, after) in enumerate(history):
            lines.extend([
                f"  have e{j} : nextPhase ({power_three}*x) ({before}*y) = {after}*y := by",
                "    unfold nextPhase",
                "    split <;> omega",
            ])
        lines.append("  have hc : phaseRun 12 (1*x) (1*y) (0*y) < 1594323*x := by")
        rewrites = ", ".join(f"phaseRun_scaled_step e{j}" for j in range(11))
        lines.extend([
            f"    rw [{rewrites}]",
            "    simp only [phaseRun]",
            "    omega",
            "  simpa only [Nat.one_mul, Nat.zero_mul] using hc",
            "",
        ])

    for index, (low, high, _, _, history) in enumerate(states):
        lines.extend([
            f"private theorem phase_prefix_interval_{index} (x y : Nat)",
            f"    (hl : {low.numerator}*x < {low.denominator}*y) "
            f"(hh : {high.denominator}*y ≤ {high.numerator}*x) :",
            "    ∀ k : Fin 12, 108*phaseRun k.val x y 0 ≤ (27*k.val+11)*3^k.val*x := by",
        ])
        for j, (power_three, before, after) in enumerate(history):
            lines.extend([
                f"  have e{j} : nextPhase ({power_three}*x) ({before}*y) = {after}*y := by",
                "    unfold nextPhase",
                "    split <;> omega",
            ])
        lines.extend([
            "  intro k",
            "  have hk := k.isLt",
            "  have cases : " + " ∨ ".join(f"k.val={j}" for j in range(12)) + " := by omega",
            "  have hc : 108*phaseRun k.val (1*x) (1*y) (0*y) ≤ (27*k.val+11)*3^k.val*x := by",
            "    rcases cases with " + " | ".join("hk" for _ in range(12)),
            "    all_goals rw [hk]",
            "    all_goals repeat first",
        ])
        lines.extend(f"      | rw [phaseRun_scaled_step e{j}]" for j in range(11))
        lines.extend([
            "    all_goals simp only [phaseRun]",
            "    all_goals omega",
            "  simpa only [Nat.one_mul, Nat.zero_mul] using hc",
            "",
        ])

    lines.extend([
        "/-- Every phase has strictly less than nine units of mass in twelve steps.",
        "All phase branches are discharged by exact integer linear arithmetic. -/",
        "theorem phase_twelve_bound (x y : Nat) (hlo : x < 2*y) (hhi : y ≤ x) :",
        "    phaseRun 12 x y 0 < 3*3^12*x := by",
    ])
    for index, (_, high, _, _, _) in enumerate(states[:-1]):
        lines.extend([
            f"  by_cases h{index} : {high.denominator}*y ≤ {high.numerator}*x",
            f"  · exact phase_interval_{index} x y (by omega) h{index}",
        ])
    lines.append(f"  exact phase_interval_{len(states)-1} x y (by omega) (by omega)")
    lines.extend([
        "",
        "/-- The same optimal intercept controls every phase for the initial block. -/",
        "theorem phase_initial_bound (x y : Nat) (hlo : x<2*y) (hhi : y≤x) :",
        "    ∀ k : Fin 12, 108*phaseRun k.val x y 0 ≤ (27*k.val+11)*3^k.val*x := by",
    ])
    for index, (_, high, _, _, _) in enumerate(states[:-1]):
        lines.extend([
            f"  by_cases h{index} : {high.denominator}*y ≤ {high.numerator}*x",
            f"  · exact phase_prefix_interval_{index} x y (by omega) h{index}",
        ])
    lines.append(f"  exact phase_prefix_interval_{len(states)-1} x y (by omega) (by omega)")
    return "\n".join(lines) + "\n\n"


def main() -> None:
    parser = ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    generated = certificate()
    if not (args.check or args.write):
        print(generated, end="")
        return
    source = Path(__file__).resolve().parents[1] / "Collatz/Strategy/BeattyBlockPotential.lean"
    start = "-- BEGIN GENERATED PHASE CERTIFICATE\n"
    end = "-- END GENERATED PHASE CERTIFICATE"
    prefix, rest = source.read_text().split(start, 1)
    checked_in, suffix = rest.split(end, 1)
    if args.check:
        if checked_in != generated:
            raise SystemExit("Generated phase certificate differs from checked-in source")
        print("Phase certificate reproduces exactly (12 rational intervals)")
    else:
        source.write_text(prefix + start + generated + end + suffix)


if __name__ == "__main__":
    main()
