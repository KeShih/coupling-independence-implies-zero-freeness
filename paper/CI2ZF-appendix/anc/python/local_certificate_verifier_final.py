from fractions import Fraction
from itertools import product


def require(condition, message):
    """Fail explicitly when an exact certificate condition is not met."""
    if not condition:
        raise RuntimeError(f"certificate verification failed: {message}")


p = {
    1: Fraction(1, 1),
    2: Fraction(13, 42),
    3: Fraction(1, 6),
    4: Fraction(2, 21),
    5: Fraction(1, 21),
    6: Fraction(1, 84),
    7: Fraction(0, 1),   # represents all sizes >= 7
}

def P(r):
    return p.get(r, Fraction(0, 1))

def partitions(n):
    out = []
    def rec(i, blocks):
        if i == n:
            out.append([frozenset(b) for b in blocks])
            return
        for b in blocks:
            b.append(i)
            rec(i+1, blocks)
            b.pop()
        blocks.append([i])
        rec(i+1, blocks)
        blocks.pop()
    rec(0, [])
    return out

def regular_side_states(m):
    """Enumerate one side of the exact m-port local box."""
    for blocks in partitions(m):
        size_ranges = [range(len(block), 8) for block in blocks]
        for sizes in product(*size_ranges):
            for active in product([0, 1], repeat=len(blocks)):
                yield blocks, sizes, active

def h_regular_port(m, left_blocks, right_blocks, r_sizes, s_sizes, xi, zeta, c_in_list=True):
    """Upper bound for the regular-colour port-component coupling.

    left_blocks are the Y-side a/c branch components. right_blocks are the
    X-side b/c branch components. The ports are labelled 0,...,m-1.
    xi/zeta zero branch masses failing the list check. If c_in_list is true,
    central masses are present exactly when all corresponding branch masses pass.
    """
    if m == 0:
        return Fraction(-1 if c_in_list else 0, 1)

    A = 1 + sum(r_sizes)
    B = 1 + sum(s_sizes)
    Xi = all(xi) if c_in_list else False
    Zeta = all(zeta) if c_in_list else False
    val = Fraction(0, 1)

    alpha = [P(r_sizes[j]) if xi[j] else Fraction(0, 1) for j in range(len(left_blocks))]
    beta = [P(s_sizes[k]) if zeta[k] else Fraction(0, 1) for k in range(len(right_blocks))]

    if Xi:
        j_star = max(range(len(left_blocks)), key=lambda j: r_sizes[j])
        val += (A - r_sizes[j_star] - 1) * P(A)
        alpha[j_star] -= P(A)
        require(alpha[j_star] >= 0, "negative left residual mass")
    if Zeta:
        k_star = max(range(len(right_blocks)), key=lambda k: s_sizes[k])
        val += (B - s_sizes[k_star] - 1) * P(B)
        beta[k_star] -= P(B)
        require(beta[k_star] >= 0, "negative right residual mass")

    for j, r in enumerate(r_sizes):
        val += r * alpha[j]
    for k, s in enumerate(s_sizes):
        val += s * beta[k]

    left_index = {}
    for j, block in enumerate(left_blocks):
        for port in block:
            left_index[port] = j
    right_index = {}
    for k, block in enumerate(right_blocks):
        for port in block:
            right_index[port] = k
    for port in range(m):
        j = left_index[port]
        k = right_index[port]
        val -= min(alpha[j] / len(left_blocks[j]), beta[k] / len(right_blocks[k]))
    return val

def check_elementary():
    worst_pair = (Fraction(-10, 1), None)
    for r in range(1, 8):
        for s in range(1, 8):
            # k,l are port multiplicities inside components. If a component has
            # size 7, it represents any size >=7 and has zero mass.
            for k in range(1, r + 1):
                for l in range(1, s + 1):
                    # Verify the stronger box inequality for all residual masses
                    # 0 <= alpha <= P(r), 0 <= beta <= P(s). The objective is
                    # piecewise linear, so maxima occur at rectangle corners or
                    # at endpoints of the break line alpha/k = beta/l.
                    candidates = [(Fraction(0), Fraction(0)), (P(r), Fraction(0)),
                                  (Fraction(0), P(s)), (P(r), P(s))]
                    beta_on_line = P(r) * Fraction(l, k)
                    if Fraction(0) <= beta_on_line <= P(s):
                        candidates.append((P(r), beta_on_line))
                    alpha_on_line = P(s) * Fraction(k, l)
                    if Fraction(0) <= alpha_on_line <= P(r):
                        candidates.append((alpha_on_line, P(s)))
                    for alpha, beta in candidates:
                        val = Fraction(r, k) * alpha + Fraction(s, l) * beta - min(alpha / k, beta / l)
                        if val > worst_pair[0]:
                            worst_pair = (val, (r, s, k, l, alpha, beta))
    require(
        worst_pair[0] <= Fraction(4, 3),
        f"elementary port-pair bound failed at {worst_pair}",
    )

    worst_central = (Fraction(-10, 1), None)
    for r in range(1, 8):
        val = (r - 2) * P(r)
        if val > worst_central[0]:
            worst_central = (val, r)
    require(
        worst_central[0] <= Fraction(4, 21),
        f"central bound failed at {worst_central}",
    )

    worst_branch = (Fraction(-10, 1), None)
    for r in range(1, 8):
        val = r * P(r)
        if val > worst_branch[0]:
            worst_branch = (val, r)
    require(
        worst_branch[0] <= Fraction(1, 1),
        f"branch bound failed at {worst_branch}",
    )
    return worst_pair, worst_central, worst_branch

def check_regular_small():
    rows = []
    for m in [0, 1, 2]:
        target = Fraction(11 * m, 6) - 1
        if m == 0:
            val = h_regular_port(0, [], [], [], [], [], [], True)
            rows.append((m, val, target, 'empty'))
            require(val <= target, f"regular in-list bound failed for m=0: {val} > {target}")
            continue
        side_states = list(regular_side_states(m))
        expected_sides = {1: 14, 2: 208}
        expected_pairs = {1: 196, 2: 43264}
        require(
            len(side_states) == expected_sides[m],
            f"regular in-list m={m} side count was {len(side_states)}, "
            f"expected {expected_sides[m]}",
        )
        worst = (Fraction(-10**9, 1), None)
        pair_count = 0
        for left_blocks, r_sizes, xi in side_states:
            for right_blocks, s_sizes, zeta in side_states:
                pair_count += 1
                val = h_regular_port(m, left_blocks, right_blocks, r_sizes, s_sizes, xi, zeta, True)
                if val > worst[0]:
                    worst = (val, (left_blocks, right_blocks, r_sizes, s_sizes, xi, zeta))
        require(
            pair_count == expected_pairs[m],
            f"regular in-list m={m} pair count was {pair_count}, "
            f"expected {expected_pairs[m]}",
        )
        rows.append((m, worst[0], target, worst[1]))
        require(
            worst[0] <= target,
            f"regular in-list bound failed for m={m} at {worst}",
        )
    return rows

def check_regular_not_in_list_small():
    rows = []
    for m in [0, 1, 2]:
        target = Fraction(11 * m, 6)
        if m == 0:
            val = h_regular_port(0, [], [], [], [], [], [], False)
            rows.append((m, val, target, 'empty'))
            require(val <= target, f"regular out-of-list bound failed for m=0: {val} > {target}")
            continue
        side_states = list(regular_side_states(m))
        expected_sides = {1: 14, 2: 208}
        expected_pairs = {1: 196, 2: 43264}
        require(
            len(side_states) == expected_sides[m],
            f"regular out-of-list m={m} side count was {len(side_states)}, "
            f"expected {expected_sides[m]}",
        )
        worst = (Fraction(-10**9, 1), None)
        pair_count = 0
        for left_blocks, r_sizes, xi in side_states:
            for right_blocks, s_sizes, zeta in side_states:
                pair_count += 1
                val = h_regular_port(m, left_blocks, right_blocks, r_sizes, s_sizes, xi, zeta, False)
                if val > worst[0]:
                    worst = (val, (left_blocks, right_blocks, r_sizes, s_sizes, xi, zeta))
        require(
            pair_count == expected_pairs[m],
            f"regular out-of-list m={m} pair count was {pair_count}, "
            f"expected {expected_pairs[m]}",
        )
        rows.append((m, worst[0], target, worst[1]))
        require(
            worst[0] <= target,
            f"regular out-of-list bound failed for m={m} at {worst}",
        )
    return rows

def special_m1_value(t, R, branch_contains_v, central_active=True, branch_active=True):
    """Exact two-atom upper bound for one special port.

    t is the size of the outside component attached to the central Y flip, so
    central size is B=t+1. R is the actual X-side branch size. If the branch
    does not contain v then necessarily R=t in the intended local geometry.
    """
    C = P(t + 1) if central_active else Fraction(0, 1)
    D = P(R) if branch_active else Fraction(0, 1)
    central_alone = t - 1
    if branch_contains_v:
        branch_alone = R - 2
        matched = R - t - 1
    else:
        branch_alone = R
        matched = -1
    return C * central_alone + D * branch_alone - min(C, D) * (central_alone + branch_alone - matched)

def check_special_m1():
    target = Fraction(5, 6)
    worst = (Fraction(-10, 1), None)
    # central active, branch inactive: central-alone contribution
    for t in range(1, 7):
        val = special_m1_value(t, t, False, True, False)
        if val > worst[0]:
            worst = (val, ('central_only', t))
    # central and branch active; branch excludes v, then R=t
    for t in range(1, 7):
        val = special_m1_value(t, t, False, True, True)
        if val > worst[0]:
            worst = (val, ('branch_excludes_v', t))
    # central and branch active; branch contains v and has R>=t+1
    for t in range(1, 6):
        for R in range(t + 1, 8):
            val = special_m1_value(t, R, True, True, True)
            if val > worst[0]:
                worst = (val, ('branch_contains_v', t, R))
    # central inactive implies the unique outside branch is blocked as well;
    # contribution is zero. Include the row explicitly.
    if Fraction(0, 1) > worst[0]:
        worst = (Fraction(0, 1), ('central_inactive',))
    require(worst[0] <= target, f"special one-port bound failed at {worst}")
    return worst, target

if __name__ == '__main__':
    wp, wc, wb = check_elementary()
    print('elementary port-pair box max:', wp)
    print('central max:', wc)
    print('branch max:', wb)
    print('regular c in list small cases:')
    for row in check_regular_small():
        print('  m=%s max=%s target=%s witness=%s' % row)
    print('regular c not in list small cases:')
    for row in check_regular_not_in_list_small():
        print('  m=%s max=%s target=%s witness=%s' % row)
    ws, target = check_special_m1()
    print('special m=1 max:', ws, 'target:', target)
    print('all exact checks passed')
