# Soft Carlson--Vigoda core certificate

This document specifies the exact finite certificate for active multiplicity
`d = 1, 2` in the soft Carlson--Vigoda appendix.  The Python verifier
[`python/soft_cv_certificate_verifier.py`](python/soft_cv_certificate_verifier.py)
enumerates the states and checks the inequalities described below using
exact rational arithmetic.

## Exact data

The flip probabilities, at scale `P_SCALE = 1000`, are

```text
P(0) = 0
P(1) = 1000
P(2) = 324
P(3) = 154
P(4) = 88
P(5) = 44
P(6) = 11
P(j) = 0 for j >= 7.
```

The coefficient scale is `C_SCALE = 1809000`.  The eleven rows below are
`(gamma_alpha, gamma_beta, lambda)` at that common scale:

```text
67405   0       3272009
67405   238788  3272009
67405   240125  3272009
67405   267665  3299549
68742   0       3270672
68742   238788  3270672
68742   267665  3299549
153765  0       3270672
153765  153765  3270672
153765  238788  3270672
153765  267665  3299549
```

They are exactly the arrangement vertices of the three affine branches on
the coefficient rectangle in that appendix.  The unscaled value of each entry is
the displayed integer divided by `C_SCALE`.

## Frozen checker names and paper notation

The checker retains its original field names so that this
documentation update does not change the certified computation.  The
crosswalk to the semantic notation in the paper is

```text
d            = k_c
A            = R_X
B            = R_Y
H            = H_c
d0           = N11(c)
d1           = N12(c)
gamma_alpha  = gamma_gain
gamma_beta   = gamma_loss
lambda       = Lambda_low
```

Thus names such as `d0`, `d1`, `gamma_alpha`, and `gamma_beta` below are
frozen checker names, not additional mathematical notation.

## Graph-to-state map and oriented matching

The core certificate concerns a root-available regular colour `c`.  Let the
two configurations disagree at the root `v`, with colours `a` on the left
configuration `X` and `b` on the right configuration `Y`.  Fix one common
ordering `u_1,...,u_d` of the active `c`-neighbours.

The two occurrence vectors have the following fixed orientation.

- The left-size entry `a_i` records the off-root `(a,c)` component in `Y`
  through `u_i`.  It is matched against the root-containing `(a,c)` flip
  through `v` in `X`.
- The right-size entry `b_i` records the off-root `(b,c)` component in `X`
  through `u_i`.  It is matched against the root-containing `(b,c)` flip
  through `v` in `Y`.

Scan the same neighbour ordering on both sides.  A component is recorded with
its size at the first active `c`-neighbour it contains and with size `0` at
every later such neighbour.
Thus `0` is a duplicate-component marker, not an empty component; it has no
associated accepted flip and both of its flags are false.  Every positive
size at least seven is recorded as `7`.  This preserves every charge term
because its off-root flip rate is zero, and a root-containing component
containing such an off-root component also has zero rate.

For a positive left occurrence, `available` means that its target colour
`a` belongs to the common off-root active list at its canonical neighbour;
for a positive right occurrence it means the analogous statement for `b`.
The `feasible` flag means that the entire off-root component swap passes
every post-swap list check.  Consequently,

```text
feasible implies available;
at size 1, feasible is equivalent to available.
```

The first implication holds because a feasible swap must place its target
colour legally at the canonical neighbour.  For a singleton this is the only
post-swap list check, proving the equivalence.  These are logical
restrictions on states, not empirical pruning by an implementation.

Let `I_A` and `I_B` be the maximum-index sets of the left and right size
vectors.  If they intersect, choose a common maximum index on both sides;
otherwise choose one maximum index from each set.  Match the whole
root-containing `(a,c)` flip mass in `X` across the chains to the selected
left off-root flip in `Y`, and the whole root-containing `(b,c)` flip mass
in `Y` to the selected right off-root flip in `X`.  A feasible
root-containing flip makes every positive off-root flip feasible, and
monotonicity of `P` ensures that neither subtraction overdraws the selected
off-root flip.  At every canonical neighbour, maximally match the two
residual off-root flip masses.  Their flipped sets share that neighbour, so
this match saves at least one unit relative to their two one-sided size
charges.  Residual one-sided mass is handled by the holding-probability
completion.

This algorithm and the formulas below are defined for every multiplicity
`d >= 1`.  The finite computer-assisted certificate is used only for
`d = 1, 2`; higher multiplicities are bounded analytically in the paper.

## Structural states

An occurrence has a size and two Boolean flags, `available` and `feasible`.
The permitted states at a given size are

```text
size 0: (false, false)
size 1: (false, false), (true, true)
size 2,...,7: (false, false), (true, false), (true, true).
```

Size `0` is the duplicate-component marker.  Size `7` represents every
positive size at least seven, since its flip probability is zero.

For `d = 1`, size zero is forbidden.  Thus each side has 20 states and there
are `20^2 = 400` two-sided structural states.

For `d = 2`, each occurrence has 21 states and the all-zero size vector is
forbidden.  Thus each side has `21^2 - 1 = 440` states and there are
`440^2 = 193600` two-sided structural states.

## Charge and tie convention

For left and right size vectors `a`, `b`, let

```text
A = 1 + sum(a_i),       B = 1 + sum(b_i).
```

The associated root-containing flip is feasible precisely when every
positive off-root component flip on its side is feasible.  Write
`pA = P(A)` or `0` according as the `X`-side root-containing flip is
feasible or infeasible, and define `pB` analogously for the `Y` side.

Let `I_A`, `I_B` be the sets of indices attaining the largest size on their
respective sides.  If `I_A` and `I_B` intersect, the permitted maximum-component
choices are `(i,i)` for every index in the intersection.  Otherwise every
pair in `I_A x I_B` is permitted.  The certificate takes the largest charge
over all permitted choices.

For a permitted pair `(i_A,i_B)`, put

```text
alpha_i = feasibleLeft_i  * P(a_i) - 1(i=i_A) * pA,
beta_i  = feasibleRight_i * P(b_i) - 1(i=i_B) * pB.
```

All masses here are at scale `P_SCALE`.  The raw scaled charge is

```text
H =
  (A - max(a) - 1) * pA
  + (B - max(b) - 1) * pB
  + sum_i [a_i alpha_i + b_i beta_i - min(alpha_i,beta_i)],
```

Thus the corresponding root-containing term and subtraction both vanish when a
root-containing flip is infeasible.

Let `d0` count active `c`-neighbours whose two occurrences are available
singletons, and let `d1` count active `c`-neighbours whose two occurrences
are available and have sizes `{1,2}`.
A duplicate marker is never counted by `d0`.  Omitting a possible `d1`
credit at a duplicate neighbour is conservative because the `d1` term has a
negative coefficient.

For a coefficient row `(ga,gb,lambda)`, the certificate excess, scaled by
`P_SCALE * C_SCALE`, is

```text
E =
  H * C_SCALE
  + P_SCALE * (d0 * gb - d1 * ga + C_SCALE - d * lambda).
```

The theorem to be checked is

```text
E <= 0
```

for every structural state, every permitted maximum-component choice, and all
eleven coefficient rows.

## Required output

The Python verifier checks the 400 and 193600 structural-state counts.
It must also check 400 and 196964 permitted maximum-component choices,
respectively; in the two-neighbour scan, 3364 states have two permitted choices.
It must report maximum excess zero for both multiplicities and recover
equality witnesses equivalent to

```text
d = 1:
  left sizes = [1], right sizes = [1],
  all occurrences available and feasible,
  gamma_alpha = 153765 / 1809000,
  gamma_beta  = 267665 / 1809000.

d = 2:
  left sizes = [2,2], right sizes = [1,1],
  all occurrences available and feasible,
  gamma_alpha = 67405 / 1809000,
  gamma_beta  = 240125 / 1809000.
```

The dense rational grids and the small integer-reduction checks in the
Python program are regression tests only.  They are intentionally
outside this core certificate.
