#!/usr/bin/env python3
"""Exact-rational checks for the finite inequalities in the one-step hard estimate.

The script verifies:
  * the two elementary Vigoda-profile inequalities;
  * the piecewise-linear residual-probability inequality;
  * the regular-colour maxima for m = 0, 1, 2;
  * the one-neighbour root-colour bounds used at the end of the proof.

All arithmetic uses fractions.Fraction.  The regular-colour enumeration is
intentionally enlarged: it ranges over every set partition of N_c,
component sizes up to 7, and all feasible/infeasible choices.  Sizes at least
7 carry zero flip probability, so this truncation is exact for the enlarged
state set.  One realizability constraint is retained exactly: when the colour
is available at the root, a root swap is feasible if and only if all of its
constituent off-root swaps are feasible.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from typing import Iterable, Sequence


PROFILE: tuple[Fraction, ...] = (
    Fraction(0),       # p_0
    Fraction(1),       # p_1
    Fraction(13, 42),  # p_2
    Fraction(1, 6),    # p_3
    Fraction(2, 21),   # p_4
    Fraction(1, 21),   # p_5
    Fraction(1, 84),   # p_6
)


def require(condition: bool, message: object) -> None:
    """Fail explicitly even when Python is run with optimization enabled."""
    if not condition:
        raise RuntimeError(f"certificate verification failed: {message}")


def p(size: int) -> Fraction:
    """Return the Vigoda profile value p_size."""
    if size < 0:
        raise ValueError("component size must be nonnegative")
    return PROFILE[size] if size < len(PROFILE) else Fraction(0)


def set_partitions(n: int) -> list[tuple[tuple[int, ...], ...]]:
    """All set partitions of {0,...,n-1}, canonically ordered."""
    if n == 0:
        return [tuple()]

    result: list[tuple[tuple[int, ...], ...]] = []

    def rec(i: int, blocks: list[list[int]]) -> None:
        if i == n:
            canonical = tuple(tuple(block) for block in blocks)
            result.append(canonical)
            return
        for block in blocks:
            block.append(i)
            rec(i + 1, blocks)
            block.pop()
        blocks.append([i])
        rec(i + 1, blocks)
        blocks.pop()

    rec(0, [])
    return result


def component_size_vectors(
    partition: Sequence[Sequence[int]], max_size: int = 7
) -> Iterable[tuple[int, ...]]:
    """Enumerate sizes at least the number of N_c vertices in each component."""
    ranges = [range(len(block), max_size + 1) for block in partition]
    return product(*ranges)


def distinguished_component(
    partition: Sequence[Sequence[int]], sizes: Sequence[int]
) -> int:
    """Largest component, ties broken by its least N_c index."""
    if not partition:
        raise ValueError("a distinguished component requires a nonempty partition")
    return min(
        range(len(partition)),
        key=lambda idx: (-sizes[idx], min(partition[idx])),
    )


def block_index(partition: Sequence[Sequence[int]], vertex: int) -> int:
    for idx, block in enumerate(partition):
        if vertex in block:
            return idx
    raise ValueError(f"vertex {vertex} is not present in the partition")


def root_is_feasible(allowed_at_root: bool, offroot_feasible: Sequence[int]) -> int:
    """The root/off-root feasibility equivalence used in the proof."""
    return int(allowed_at_root and all(offroot_feasible))


def regular_colour_charge(
    m: int,
    allowed_at_root: bool,
    part_a: Sequence[Sequence[int]],
    sizes_a: Sequence[int],
    feasible_a: Sequence[int],
    part_b: Sequence[Sequence[int]],
    sizes_b: Sequence[int],
    feasible_b: Sequence[int],
) -> Fraction:
    """Evaluate the enlarged right-hand side of the regular-colour bound."""
    if m == 0:
        return Fraction(-1 if allowed_at_root else 0)

    star_a = distinguished_component(part_a, sizes_a)
    star_b = distinguished_component(part_b, sizes_b)
    root_a = 1 + sum(sizes_a)
    root_b = 1 + sum(sizes_b)

    root_feasible_a = root_is_feasible(allowed_at_root, feasible_a)
    root_feasible_b = root_is_feasible(allowed_at_root, feasible_b)

    alpha = [
        feasible_a[idx] * p(size)
        - root_feasible_a * int(idx == star_a) * p(root_a)
        for idx, size in enumerate(sizes_a)
    ]
    beta = [
        feasible_b[idx] * p(size)
        - root_feasible_b * int(idx == star_b) * p(root_b)
        for idx, size in enumerate(sizes_b)
    ]

    if any(value < 0 for value in alpha + beta):
        raise AssertionError("a monotone-profile residual probability became negative")

    charge = (
        root_feasible_a * (root_a - sizes_a[star_a] - 1) * p(root_a)
        + root_feasible_b * (root_b - sizes_b[star_b] - 1) * p(root_b)
        + sum(size * mass for size, mass in zip(sizes_a, alpha))
        + sum(size * mass for size, mass in zip(sizes_b, beta))
    )

    for vertex in range(m):
        idx_a = block_index(part_a, vertex)
        idx_b = block_index(part_b, vertex)
        share_a = alpha[idx_a] / len(part_a[idx_a])
        share_b = beta[idx_b] / len(part_b[idx_b])
        charge -= min(share_a, share_b)

    return charge


def maximum_regular_colour_charge(
    m: int, allowed_at_root: bool
) -> tuple[Fraction, tuple[object, ...] | None]:
    if m == 0:
        return Fraction(-1 if allowed_at_root else 0), None

    maximum: Fraction | None = None
    witness: tuple[object, ...] | None = None
    partitions = set_partitions(m)

    for part_a in partitions:
        for part_b in partitions:
            for sizes_a in component_size_vectors(part_a):
                for sizes_b in component_size_vectors(part_b):
                    for feasible_a in product((0, 1), repeat=len(part_a)):
                        for feasible_b in product((0, 1), repeat=len(part_b)):
                            value = regular_colour_charge(
                                m,
                                allowed_at_root,
                                part_a,
                                sizes_a,
                                feasible_a,
                                part_b,
                                sizes_b,
                                feasible_b,
                            )
                            if maximum is None or value > maximum:
                                maximum = value
                                witness = (
                                    part_a,
                                    sizes_a,
                                    feasible_a,
                                    part_b,
                                    sizes_b,
                                    feasible_b,
                                )

    if maximum is None:
        raise AssertionError("empty finite enumeration")
    return maximum, witness


def regular_state_count(m: int) -> int:
    """Number of enlarged states searched for either value of root availability."""
    if m == 0:
        return 1
    side_count = 0
    for partition in set_partitions(m):
        for _sizes in component_size_vectors(partition):
            for _feasible in product((0, 1), repeat=len(partition)):
                side_count += 1
    return side_count**2


def candidates_for_piecewise_box(
    upper_alpha: Fraction,
    upper_beta: Fraction,
    j: int,
    k: int,
) -> set[tuple[Fraction, Fraction]]:
    """Corners and intersections of alpha/j = beta/k with the box boundary."""
    candidates = {
        (Fraction(0), Fraction(0)),
        (upper_alpha, Fraction(0)),
        (Fraction(0), upper_beta),
        (upper_alpha, upper_beta),
    }

    beta_at_alpha_max = Fraction(k, j) * upper_alpha
    if beta_at_alpha_max <= upper_beta:
        candidates.add((upper_alpha, beta_at_alpha_max))

    alpha_at_beta_max = Fraction(j, k) * upper_beta
    if alpha_at_beta_max <= upper_alpha:
        candidates.add((alpha_at_beta_max, upper_beta))

    return candidates


def format_regular_witness(
    m: int,
    allowed_at_root: bool,
    witness: tuple[object, ...] | None,
) -> str:
    """Format every state variable, including the derived root-feasibility bits."""
    if m == 0:
        return "empty component families"
    if witness is None:
        raise AssertionError("a nonempty state must have a witness")

    part_a, sizes_a, feasible_a, part_b, sizes_b, feasible_b = witness
    display_part_a = tuple(tuple(vertex + 1 for vertex in block) for block in part_a)
    display_part_b = tuple(tuple(vertex + 1 for vertex in block) for block in part_b)
    root_a = root_is_feasible(allowed_at_root, feasible_a)
    root_b = root_is_feasible(allowed_at_root, feasible_b)
    return (
        f"C(partition={display_part_a}, sizes={sizes_a}, "
        f"offroot={feasible_a}, root={root_a}); "
        f"D(partition={display_part_b}, sizes={sizes_b}, "
        f"offroot={feasible_b}, root={root_b})"
    )


def verify_profile_inequalities() -> None:
    max_reduced = max((r - 2) * p(r) for r in range(1, 8))
    max_size_mass = max(r * p(r) for r in range(1, 8))
    reduced_witness = next(r for r in range(1, 8) if (r - 2) * p(r) == max_reduced)
    size_mass_witness = next(r for r in range(1, 8) if r * p(r) == max_size_mass)
    require(max_reduced == Fraction(4, 21), max_reduced)
    require(max_size_mass == Fraction(1), max_size_mass)

    maximum = Fraction(-10**9)
    witness: tuple[int, int, int, int, Fraction, Fraction] | None = None
    for r in range(1, 8):
        for s in range(1, 8):
            for j in range(1, r + 1):
                for k in range(1, s + 1):
                    for alpha, beta in candidates_for_piecewise_box(p(r), p(s), j, k):
                        value = (
                            Fraction(r, j) * alpha
                            + Fraction(s, k) * beta
                            - min(alpha / j, beta / k)
                        )
                        if value > maximum:
                            maximum = value
                            witness = (r, s, j, k, alpha, beta)
    require(maximum == Fraction(4, 3), (maximum, witness))

    max_hold = max((t - 1) * p(t + 1) for t in range(1, 8))
    max_paired = max(t * p(t) - (t + 1) * p(t + 1) for t in range(1, 8))
    hold_witness = next(
        t for t in range(1, 8) if (t - 1) * p(t + 1) == max_hold
    )
    paired_witness = next(
        t
        for t in range(1, 8)
        if t * p(t) - (t + 1) * p(t + 1) == max_paired
    )
    require(max_hold == Fraction(4, 21), max_hold)
    require(max_paired == Fraction(8, 21), max_paired)

    print(f"(r-2)p_r maximum: {max_reduced} at r={reduced_witness}")
    print(f"r p_r maximum:       {max_size_mass} at r={size_mass_witness}")
    print(f"piecewise maximum:   {maximum} at {witness}")
    print(f"root hold maximum:   {max_hold} at t={hold_witness}")
    print(f"root paired maximum: {max_paired} at t={paired_witness}")


def verify_regular_colour_table() -> None:
    expected = {
        (0, True): Fraction(-1),
        (1, True): Fraction(5, 6),
        (2, True): Fraction(8, 3),
        (0, False): Fraction(0),
        (1, False): Fraction(4, 3),
        (2, False): Fraction(8, 3),
    }

    print("\nregular-colour enlarged-state maxima:")
    for allowed in (True, False):
        for m in (0, 1, 2):
            value, witness = maximum_regular_colour_charge(m, allowed)
            require(
                value == expected[(m, allowed)],
                (m, allowed, value, witness),
            )
            status = "yes" if allowed else "no"
            print(
                f"  m={m}, c in both root lists={status}: {value} "
                f"over {regular_state_count(m)} states"
            )
            print(f"    witness: {format_regular_witness(m, allowed, witness)}")


def main() -> None:
    verify_profile_inequalities()
    verify_regular_colour_table()
    print("\nAll exact-rational certificate checks passed.")


if __name__ == "__main__":
    main()
