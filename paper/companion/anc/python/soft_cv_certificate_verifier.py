#!/usr/bin/env python3
"""Self-contained exact-rational verifier for the geometric soft-CV closure
using the literal Carlson--Vigoda coefficient eta=(P2-P3)/(2r),
for the full half-plane r=q/Delta >= 1.809.

This script uses only the Python standard library.  It checks the finite
hard/list algebra (d_c=1,2), the d_c>=3 analytic box, the boundary and
special-colour constants, and the final 1.809 scalar gaps.  It also records
a redundant exact check of the critical-line integer reduction proved in the
additional Potts appendix.

It does not prove the graph-theoretic transition or coupling lemmas; those
are proved in the paper.  It verifies the finite and scalar inequalities explicitly
represented below.  The general d_c>=3 implication follows from the exact
algebraic identities and sign conditions checked below; scans over
d=3,...,125 are regression guards only.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass, asdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json


def require(condition, message):
    """Fail explicitly when an exact certificate condition is not met."""
    if not condition:
        raise RuntimeError(f"certificate verification failed: {message}")


# Carlson--Vigoda parameters.
P = {1:Q(1), 2:Q(81,250), 3:Q(77,500), 4:Q(11,125),
     5:Q(11,250), 6:Q(11,1000)}
def p(j:int)->Q: return P.get(j,Q(0))
P2,P3,P4=P[2],P[3],P[4]
AETA=Q(17,200)  # (P2-P3)/2; eta(r)=AETA/r
R0=Q(1809,1000)
R1=Q(11,6)
DELTA0=125
C=1+P2
KAPPA=Q(4,3)+P2+Q(4,3)*P4
TARGET=Q(1,100000)

# Repaired geometric coefficients on the whole half-plane.
# eta(r)=AETA/r.  gamma_alpha is increasing in r and Delta;
# gamma_beta is maximized at r=R0, Delta=125, theta*t=0;
# gamma_alpha tends to AETA as r tends to infinity.
GAMMA_ALPHA=AETA*(1-(1+Q(2,DELTA0))/R0)
GAMMA_ALPHA_MAX=AETA  # limiting value as r -> infinity
GAMMA_BETA_PLUS=AETA*(1+(C+Q(2,DELTA0))/R0)


def rec(x:Q):
    return {"exact":f"{x.numerator}/{x.denominator}","decimal":float(x)}


def allowed_max_pairs(a,b):
    ma,mb=max(a),max(b)
    ia=[i for i,v in enumerate(a) if v==ma]
    ib=[i for i,v in enumerate(b) if v==mb]
    common=sorted(set(ia)&set(ib))
    if common:
        return tuple((i,i) for i in common)
    return tuple(product(ia,ib))


def structured_charge_for_maxima(a,b,fa,fb,root_a,root_b,ia,ib):
    A=1+sum(a); B=1+sum(b)
    ca=bool(root_a and all(ok for size,ok in zip(a,fa) if size>0))
    cb=bool(root_b and all(ok for size,ok in zip(b,fb) if size>0))
    pa=p(A) if ca else Q(0); pb=p(B) if cb else Q(0)
    qa=[Q(int(ok))*p(s)-(pa if i==ia else 0) for i,(s,ok) in enumerate(zip(a,fa))]
    qb=[Q(int(ok))*p(s)-(pb if i==ib else 0) for i,(s,ok) in enumerate(zip(b,fb))]
    require(
        min(qa+qb)>=0,
        f"negative structured residual charge for maxima ({ia}, {ib})",
    )
    value=Q(int(ca))*(A-max(a)-1)*p(A)
    value+=Q(int(cb))*(B-max(b)-1)*p(B)
    value+=sum(ai*l+bi*r-min(l,r) for ai,bi,l,r in zip(a,b,qa,qb))
    return value


def structured_charge(a,b,fa,fb,root_a=True,root_b=True):
    # Certify the worst permitted choice when maximum branches are tied.
    return max(structured_charge_for_maxima(a,b,fa,fb,root_a,root_b,ia,ib)
               for ia,ib in allowed_max_pairs(a,b))


@dataclass(frozen=True)
class AF:
    available:bool
    feasible:bool


def branch_states(size):
    # 0 is the Carlson--Vigoda duplicate-component marker; 7 denotes every
    # zero-rate positive size >=7.  A zero occurrence has no separate atom.
    if size==0:
        return (AF(False,False),)
    if size==1:
        return (AF(False,False),AF(True,True))
    return (AF(False,False),AF(True,False),AF(True,True))


def port_state_vectors(ls,rs):
    per=tuple(tuple(product(branch_states(l),branch_states(r)))
              for l,r in zip(ls,rs))
    for states in product(*per):
        yield (tuple(x.available for x,_ in states),
               tuple(y.available for _,y in states),
               tuple(x.feasible for x,_ in states),
               tuple(y.feasible for _,y in states))


def safe_counts(ls,rs,al,ar):
    d0=d1=0
    for l,r,x,y in zip(ls,rs,al,ar):
        if not(x and y): continue
        if l==r==1: d0+=1
        elif l>0 and r>0 and sorted((l,r))==[1,2]: d1+=1
        # If l=0 or r=0, this port shares a previously counted component.
        # It cannot be unblocked.  It may be singly blocked, but omitting the
        # negative alpha correction is conservative for an upper bound.
    return d0,d1


def coefficients():
    return {
      "unblocked":2-P2+GAMMA_BETA_PLUS,
      "singly":2-P3-GAMMA_ALPHA,
      "multi":2-P2+2*(P3-P4),
      "dc_ge_3":KAPPA,
    }


def coefficient_vertices():
    """Vertices of the three-branch max arrangement on the coefficient box."""
    ga_lo,ga_hi=GAMMA_ALPHA,GAMMA_ALPHA_MAX
    gb_lo,gb_hi=Q(0),GAMMA_BETA_PLUS
    A0=2-P2; B0=2-P3; C0=2-P2+2*(P3-P4)
    # Branch-equality lines: A=B, A=C, B=C.
    s=B0-A0; gb_c=C0-A0; ga_c=B0-C0
    pts={(ga_lo,gb_lo),(ga_lo,gb_hi),(ga_hi,gb_lo),(ga_hi,gb_hi)}
    for ga in (ga_lo,ga_hi,ga_c):
        for gb in (gb_lo,gb_hi,gb_c,s-ga):
            if ga_lo<=ga<=ga_hi and gb_lo<=gb<=gb_hi: pts.add((ga,gb))
    for gb in (gb_lo,gb_hi,gb_c):
        ga=s-gb
        if ga_lo<=ga<=ga_hi and gb_lo<=gb<=gb_hi: pts.add((ga,gb))
    return tuple(sorted(pts))


def scan_regular(d):
    # For fixed structural state, excess is affine minus d times the maximum
    # of three affine functions, hence concave piecewise affine.  Its maximum
    # over the coefficient rectangle occurs at one of these arrangement
    # vertices.  This checks the entire coefficient region, not only one
    # half-plane corner.
    points=coefficient_vertices()
    A0=2-P2; B0=2-P3; C0=2-P2+2*(P3-P4)
    worst=None; checked=0
    tie_choices=0
    multi_tie_states=0
    size_range=range(1,8) if d==1 else range(0,8)
    for ls in product(size_range,repeat=d):
      if sum(ls)==0: continue
      for rs in product(size_range,repeat=d):
       if sum(rs)==0: continue
       for al,ar,fl,fr in port_state_vectors(ls,rs):
        d0,d1=safe_counts(ls,rs,al,ar)
        maximum_pairs=allowed_max_pairs(ls,rs)
        tie_choices+=len(maximum_pairs)
        if len(maximum_pairs)>1:
            multi_tie_states+=1
        raw=max(
            structured_charge_for_maxima(
                ls,rs,fl,fr,True,True,ia,ib
            )
            for ia,ib in maximum_pairs
        )
        for ga,gb in points:
            lam=max(A0+gb,B0-ga,C0)
            corrected=raw+d0*gb-d1*ga
            row=(corrected-(-1+d*lam),corrected,ga,gb,lam,ls,rs,al,ar,fl,fr,d0,d1,raw)
            if worst is None or row>worst: worst=row
        checked+=1
    expected_states=400 if d==1 else 193600
    expected_tie_choices=400 if d==1 else 196964
    expected_multi_ties=0 if d==1 else 3364
    require(len(points)==11, f"regular d={d} coefficient vertex count was {len(points)}")
    require(
        checked==expected_states,
        f"regular d={d} state count was {checked}, expected {expected_states}",
    )
    require(
        tie_choices==expected_tie_choices,
        f"regular d={d} tie-choice count was {tie_choices}, "
        f"expected {expected_tie_choices}",
    )
    require(
        multi_tie_states==expected_multi_ties,
        f"regular d={d} multi-tie count was {multi_tie_states}, "
        f"expected {expected_multi_ties}",
    )
    require(
        worst is not None and worst[0]==0,
        f"regular d={d} maximum excess was not exactly zero: {worst}",
    )
    if d==1:
        expected_witness=(
            Q(22247,27000), Q(17,200), Q(799,5400), Q(49247,27000),
            (1,), (1,), (True,), (True,), (True,), (True,),
            1, 0, Q(169,250),
        )
    else:
        expected_witness=(
            Q(2367509,904500), Q(13481,361800), Q(1921,14472),
            Q(3272009,1809000), (2,2), (1,1),
            (True,True), (True,True), (True,True), (True,True),
            0, 2, Q(673,250),
        )
    require(
        worst[1:]==expected_witness,
        f"regular d={d} equality witness differed: {worst[1:]}",
    )
    return {
      "d":d,"structural_states":checked,"coefficient_vertices":len(points),
      "permitted_maximum_branch_choices":tie_choices,
      "multi_tie_structural_states":multi_tie_states,
      "maximum_excess_over_full_rectangle":rec(worst[0]),
      "witness":{
        "corrected":rec(worst[1]),"gamma_alpha":rec(worst[2]),
        "gamma_beta":rec(worst[3]),"lambda":rec(worst[4]),
        "left_sizes":list(worst[5]),"right_sizes":list(worst[6]),
        "available_left":list(worst[7]),"available_right":list(worst[8]),
        "feasible_left":list(worst[9]),"feasible_right":list(worst[10]),
        "safe_d0":worst[11],"safe_d1":worst[12],"raw":rec(worst[13])
      }
    }


def verify_ordered_incidence_symbolic():
    # For m>=1, x^m-x^(2m)<=x; hence the difference is bounded below by
    # x[2P2+(1-P2)x].  We also scan a dense exact grid as regression.
    worst=None
    for m in range(0,65):
      for i in range(2001):
        x=Q(i,2000); th=1-x
        excess=th*(C+(1-P2)*(x**m-x**(2*m)))-C
        row=(excess,m,x)
        if worst is None or row>worst: worst=row
    require(
        worst is not None and worst[0]<=0,
        f"ordered-incidence regression failed at {worst}",
    )
    return {
      "symbolic":"(1-x)[C+(1-P2)(x^m-x^(2m))] <= C; use x^m-x^(2m)<=x",
      "grid_maximum_excess":rec(worst[0]),"grid_m":worst[1],"grid_x":rec(worst[2])
    }


def missing_ordinary():
    best=None
    for a,b,fa,fb in product(range(0,8),range(0,8),(0,1),(0,1)):
        qa=fa*p(a); qb=fb*p(b)
        val=a*qa+b*qb-min(qa,qb)
        row=(val,a,b,fa,fb)
        if best is None or row>best: best=row
    require(
        best is not None and best[0]==C,
        f"missing-ordinary branch maximum was {best}, expected {C}",
    )
    corrected=C+GAMMA_BETA_PLUS
    require(
        corrected<KAPPA,
        f"missing-ordinary corrected value {corrected} is not below {KAPPA}",
    )
    return {
      "branch_max":rec(best[0]),"witness":{"a":best[1],"b":best[2],"fa":best[3],"fb":best[4]},
      "duplicate_markers_included":True,
      "with_metric":rec(corrected),"slack_to_kappa":rec(KAPPA-corrected)
    }


def special_constants():
    max_j=max(Q(j)*p(j) for j in range(1,30))
    max_c=max(Q(j-2)*p(j) for j in range(1,30))
    max_pair=max(Q(s)*p(s)-Q(s+1)*p(s+1) for s in range(1,30))
    max_central=max(Q(s-1)*p(s+1) for s in range(1,30))
    require(
        (max_j,max_c,max_pair,max_central)
        ==(Q(1),Q(22,125),Q(44,125),Q(22,125)),
        "special-colour scalar maxima differ from their certified values",
    )
    for m in range(1001):
        if m==0:
            require(-1<=KAPPA*m-1, f"special-side m=0 bound failed")
        elif m==1:
            require(max_pair<=KAPPA*m-1, "special-side paired m=1 bound failed")
            require(max_central<=KAPPA*m-1, "special-side central m=1 bound failed")
            require(0<=KAPPA*m-1, "special-side remote-zero m=1 bound failed")
        else:
            require(Q(m)+max_c<=KAPPA*m-1, f"special-side central bound failed for m={m}")
            require(Q(m)<=KAPPA*m-1, f"special-side remote-zero bound failed for m={m}")
        require(Q(m)<=KAPPA*m, f"special-side unavailable-target bound failed for m={m}")
    return {
      "max_jPj":rec(max_j),"max_(j-2)Pj":rec(max_c),
      "max_one_port_paired":rec(max_pair),"max_one_port_central":rec(max_central),
      "m1_slack":rec(KAPPA-1-max_pair),
      "m2_central_on_slack":rec(2*KAPPA-1-(2+max_c)),
      "m2_remote_zero_slack":rec(2*KAPPA-1-2),
      "bound":"C_t <= -1_{target available} + kappa*m_t"
    }


def scalar_closure():
    eta0=AETA/R0
    l1=2-P2+eta0*(R0-P2+1+P2+Q(2,DELTA0))
    l2=2-P3-eta0*(R0-1-Q(2,DELTA0))
    l3=2-P2+2*P3-2*P4
    gaps=(R0-l1,R0-l2,R0-l3)
    require(
        gaps==(Q(59,226125),Q(59,226125),Q(1,1000)),
        f"scalar closure gaps differ from their certified values: {gaps}",
    )
    require(
        min(gaps)>TARGET,
        f"scalar closure reserve {min(gaps)} is not above {TARGET}",
    )
    return {
      "lambda1_plus":rec(l1),"lambda2":rec(l2),"lambda3":rec(l3),
      "eta_at_r0":rec(eta0),
      "branch1_t_derivative_at_worst_corner":rec(-KAPPA+(2-P2+AETA+AETA*(C+Q(2,DELTA0))/R0)-2*AETA*P2/R0),
      "branch2_lambda_minus_kappa_at_worst_r":rec((2-P3-AETA+AETA*(1+Q(2,DELTA0))/R0)-KAPPA),
      "gaps":[rec(g) for g in gaps],"worst_gap":rec(min(gaps)),
      "reserve_beyond_1e-5":rec(min(gaps)-TARGET)
    }



def high_multiplicity_thinning():
    bar_lambda=2-P2+GAMMA_BETA_PLUS
    slack=KAPPA-2*(bar_lambda-KAPPA)
    require(
        bar_lambda==Q(49247,27000),
        f"high-multiplicity bar_lambda was {bar_lambda}",
    )
    require(
        slack==Q(22627,13500) and slack>0,
        f"high-multiplicity slack was {slack}",
    )
    # The analytic envelope uses
    # theta*x^(m-3)*(1+(m-2)*theta) <= 2 for m>=3.
    # Dense exact regression is included as a guard against transcription.
    worst=None
    for m in range(3,129):
        for i in range(2001):
            x=Q(i,2000); th=1-x
            envelope=th*(x**(m-3))*(1+Q(m-2)*th)
            row=(envelope,m,x)
            if worst is None or row>worst: worst=row
    require(
        worst is not None and worst[0]<=2,
        f"high-multiplicity grid regression failed at {worst}",
    )
    return {
      "bar_lambda":rec(bar_lambda),
      "analytic_envelope":"theta*x^(m-3)*(1+(m-2)theta) <= 2 for m>=3",
      "grid_maximum":rec(worst[0]),"grid_m":worst[1],"grid_x":rec(worst[2]),
      "slack_kappa_minus_2_times_excess":rec(slack)
    }


def boundary_effective_low_mass():
    # Symbolic resource identity used in the proof.  If L is physical low
    # regular mass, H is all remaining physical root-port mass, B_v is root
    # boundary-copy count, and L_x=sum_{m_c<=2} m_c*x^{b_v(c)}, then
    # 0<=L_x<=L and L+H+B_v<=Delta imply
    # (L-L_x)+H+B_v<=Delta-L_x.
    # We exhaust a finite integer box and a rational grid for L_x as a
    # transcription/regression check; the implication itself is algebraic.
    worst=None
    for Delta in range(1,31):
      for L in range(Delta+1):
       for H in range(Delta-L+1):
        for B in range(Delta-L-H+1):
         for j in range(21):
          Lx=Q(L*j,20)
          excess=(Q(L)-Lx)+H+B-(Q(Delta)-Lx)
          row=(excess,Delta,L,H,B,Lx)
          if worst is None or row>worst: worst=row
    require(
        worst is not None and worst[0]<=0,
        f"boundary bookkeeping regression failed at {worst}",
    )
    return {
      "definition":"L_x=sum_{c:m_c in {1,2}} m_c*x^{b_v(c)}",
      "root_event_saving":"q-P2*(1-x)*L_x",
      "resource_inequality":"(L-L_x)+H+B_v <= Delta-L_x",
      "grid_maximum_excess":rec(worst[0]),
      "bookkeeping":"root-missing low mass is moved from the P2-saving branch into the kappa budget; no second factor (1-x) is inserted"
    }


def near_vigoda_arithmetic():
    eps0=Q(1,84000)
    alpha=Q(11,6)-eps0
    require(alpha==Q(51333,28000), f"near-Vigoda alpha was {alpha}")
    require(alpha>R0, f"near-Vigoda alpha {alpha} is not above {R0}")
    exceptional=[]
    for Delta in range(3,125):
        a=alpha*Delta
        qmin=(a.numerator+a.denominator-1)//a.denominator
        if Q(qmin)>Q(11*Delta,6):
            continue
        require(Delta%6==0, f"unexpected exceptional degree {Delta}")
        require(
            qmin==11*Delta//6,
            f"unexpected exceptional pair ({Delta}, {qmin})",
        )
        exceptional.append((Delta,qmin))
    expected=[(6*j,11*j) for j in range(1,21)]
    require(
        exceptional==expected,
        f"exceptional-pair list differs: {exceptional}",
    )
    # At q=11 Delta/6 the expected Hamming drift is at most -xq,
    # hence the adjacent contraction factor is 1-x/n.  The child-middle
    # perturbation is Delta/(nq)=6/(11n), so stationary comparison gives
    # 6/(11x) to the middle and 12/(11x) between two children.
    return {
      "epsilon0":rec(eps0),
      "alpha":rec(alpha),
      "alpha_minus_1_809":rec(alpha-R0),
      "small_degree_exceptional_pairs":[{"Delta":D,"q":q} for D,q in exceptional],
      "critical_line":"q=11 Delta/6",
      "adjacent_contraction":"W_Ham(K sigma,K tau) <= 1-x/n",
      "child_middle_CI":"6/(11x)",
      "child_child_CI":"12/(11x)"
    }


def build_payload():
    require(
        GAMMA_BETA_PLUS<=P2,
        f"gamma_beta_plus {GAMMA_BETA_PLUS} exceeds P2={P2}",
    )
    scans=[scan_regular(1),scan_regular(2)]
    d3=[]
    for d in range(3,DELTA0+1):
        upper=4*P4+d*C
        target=-1+d*KAPPA
        slack=target-upper
        require(
            slack==Q(d-3,3)*(1+4*P4) and slack>=0,
            f"d_c>=3 slack identity failed for d={d}: {slack}",
        )
        if d in (3,4,125): d3.append({"d":d,"slack":rec(slack)})
    return {
      "status":"all exact checks for the soft-CV certificate passed",
      "result_I_geometric_soft_CV":{
        "parameters":{
          "P2":rec(P2),"P3":rec(P3),"P4":rec(P4),"eta_formula":"17/(200r)","eta_at_r0":rec(AETA/R0),
          "kappa":rec(KAPPA),"gamma_alpha_min":rec(GAMMA_ALPHA),
          "gamma_alpha_max":rec(GAMMA_ALPHA_MAX),
          "gamma_beta_plus_max":rec(GAMMA_BETA_PLUS),
          "gamma_beta_plus_le_P2":GAMMA_BETA_PLUS<=P2
        },
        "boundary_effective_low_mass":boundary_effective_low_mass(),
        "repaired_G2_plus":{
          "beta":"q-P2*(1-x)*L_x+(1+P2)*Delta+2",
          "self_port_addition":rec(Q(2)),
          "ordered_incidence":verify_ordered_incidence_symbolic()
        },
        "regular_available_colour_scans":scans,
        "duplicate_component_convention":{
          "marker":"a_i=0 or b_i=0 for a component already represented at an earlier port",
          "metric_treatment":"zero-marked ports receive no positive unblocked correction; any omitted singly-blocked negative correction is conservative"
        },
        "regular_dc_ge_3_samples":d3,
        "physical_high_multiplicity_thinning":high_multiplicity_thinning(),
        "missing_ordinary_colour":missing_ordinary(),
        "special_side":special_constants(),
        "virtual_port":{
          "token_cost":rec(Q(1)),"token_cost_le_kappa":Q(1)<KAPPA,
          "bookkeeping":"distinct missing root colour -> distinct active physical boundary copy"
        },
        "scalar_closure":scalar_closure()
      },
      "result_II_near_11_over_6":near_vigoda_arithmetic(),
      "scope":"exact finite/scalar certificate; the graph-theoretic coupling and coupling-independence arguments are proved in the paper"
    }


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).with_name("soft_cv_certificate.json"),
        help="certificate path (default: beside this script)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="verify that --output already equals the generated certificate",
    )
    args=parser.parse_args()
    payload=build_payload()
    rendered=json.dumps(payload,ensure_ascii=False,indent=2)+'\n'
    if args.check:
        if not args.output.exists() or args.output.read_text(encoding="utf-8") != rendered:
            raise SystemExit(f"certificate mismatch: {args.output}")
        print("certificate matches",args.output)
    else:
        args.output.write_text(rendered,encoding='utf-8')
        print("wrote",args.output)
    print(payload["status"])

if __name__=='__main__': main()
