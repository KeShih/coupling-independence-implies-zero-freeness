import ZeroFreeness.Potts.Model.Real.Pinning
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic

/-!
# Complex normalized pinned Potts polynomials

The finite graph and arbitrary partial-colouring semantics are those of
`PottsCI.Potts.Pinning`.  In particular no properness hypothesis is imposed on
the pinned domain, and normalization is defined by omitting pinned-only
conflicts, never by division by the activity.  This file adds genuine complex
polynomials and strengthens the inherited hard-feasibility bound to `q ≥ Δ+1`.
-/

namespace ZeroFreeness.Potts

open Finset PottsCI

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

/-- The normalized polynomial is a finite sum of monomials counting exactly
free--pinned and free--free monochromatic edges. -/
noncomputable def normalizedPolynomial (tau : PartialColouring V C) (G : SimpleGraph V) :
    Polynomial ℂ :=
  ∑ sigma : tau.FreeVertex → C,
    Polynomial.X ^ (tau.boundaryConflictCount G sigma + tau.freeConflictCount G sigma)

/-- Complex evaluation of the normalized pinned partition polynomial. -/
noncomputable def normalizedPartition (tau : PartialColouring V C) (G : SimpleGraph V)
    (z : ℂ) : ℂ :=
  (normalizedPolynomial tau G).eval z

/-- The ordinary pinned polynomial includes the monochromatic pinned-only edges. -/
noncomputable def fullPolynomial (tau : PartialColouring V C) (G : SimpleGraph V) :
    Polynomial ℂ :=
  ∑ sigma : tau.FreeVertex → C, Polynomial.X ^ tau.fullConflictCount G sigma

noncomputable def fullPartition (tau : PartialColouring V C) (G : SimpleGraph V)
    (z : ℂ) : ℂ :=
  (fullPolynomial tau G).eval z

lemma normalizedPartition_eq_sum (tau : PartialColouring V C) (G : SimpleGraph V)
    (z : ℂ) :
    normalizedPartition tau G z =
      ∑ sigma : tau.FreeVertex → C,
        z ^ (tau.boundaryConflictCount G sigma + tau.freeConflictCount G sigma) := by
  simp [normalizedPartition, normalizedPolynomial, Polynomial.eval_finsetSum]

lemma fullPartition_eq_sum (tau : PartialColouring V C) (G : SimpleGraph V) (z : ℂ) :
    fullPartition tau G z =
      ∑ sigma : tau.FreeVertex → C, z ^ tau.fullConflictCount G sigma := by
  simp [fullPartition, fullPolynomial, Polynomial.eval_finsetSum]

/-- At a real activity this is exactly the inherited real Potts partition. -/
lemma normalizedPartition_ofReal (tau : PartialColouring V C) (G : SimpleGraph V)
    (x : ℝ) :
    normalizedPartition tau G (x : ℂ) = ((tau.toPinningData G).partition x : ℂ) := by
  rw [normalizedPartition_eq_sum, PinningData.partition]
  push_cast
  apply Finset.sum_congr rfl
  intro sigma _
  rw [tau.childWeight_eq_pow G x sigma]
  push_cast
  rw [pow_add]

/-- Exact polynomial normalization, including at activity zero. -/
lemma fullPolynomial_eq (tau : PartialColouring V C) (G : SimpleGraph V) :
    fullPolynomial tau G =
      Polynomial.X ^ tau.pinnedConflictCount G * normalizedPolynomial tau G := by
  unfold fullPolynomial normalizedPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [tau.fullConflictCount_add G sigma, pow_add, pow_add, pow_add, mul_assoc]

lemma fullPartition_eq (tau : PartialColouring V C) (G : SimpleGraph V) (z : ℂ) :
    fullPartition tau G z =
      z ^ tau.pinnedConflictCount G * normalizedPartition tau G z := by
  simp [fullPartition, fullPolynomial_eq, normalizedPartition]

@[simp]
lemma normalizedPartition_one (tau : PartialColouring V C) (G : SimpleGraph V) :
    normalizedPartition tau G 1 =
      (Fintype.card C : ℂ) ^ Fintype.card tau.FreeVertex := by
  simp [normalizedPartition_eq_sum]

lemma normalizedPartition_ofReal_ne_zero [Nonempty C]
    (tau : PartialColouring V C) (G : SimpleGraph V) {x : ℝ} (hx : 0 < x) :
    normalizedPartition tau G (x : ℂ) ≠ 0 := by
  rw [normalizedPartition_ofReal]
  exact_mod_cast ((tau.toPinningData G).partition_pos_of_parameter_pos hx).ne'

/-- The inherited boundary-count argument only needs one colour of slack. -/
lemma card_hardList_of_succ_le (I : PinningData V C) {Δ : ℕ}
    (hdegree : I.DegreeBound Δ) (hcolours : Δ + 1 ≤ Fintype.card C) (u : V) :
    I.graph.degree u + 1 ≤ (I.hardList u).card := by
  have hsplit : (Finset.univ.filter fun c => I.boundaryCount u c = 0).card +
      (Finset.univ.filter fun c => ¬ I.boundaryCount u c = 0).card = Fintype.card C := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hforbidden : (Finset.univ.filter fun c => ¬ I.boundaryCount u c = 0).card ≤
      ∑ c, I.boundaryCount u c := by
    calc
      (Finset.univ.filter fun c => ¬ I.boundaryCount u c = 0).card =
          ∑ c ∈ Finset.univ.filter (fun c => ¬ I.boundaryCount u c = 0), 1 := by
            rw [Finset.card_eq_sum_ones]
      _ ≤ ∑ c ∈ Finset.univ.filter (fun c => ¬ I.boundaryCount u c = 0),
          I.boundaryCount u c := by
            refine Finset.sum_le_sum fun c hc => ?_
            have hcpos := (Finset.mem_filter.mp hc).2
            omega
      _ ≤ ∑ c, I.boundaryCount u c := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
            intro c _ _
            exact Nat.zero_le _
  have htotal := hdegree u
  unfold PinningData.constraintDegree at htotal
  unfold PinningData.hardList
  omega

lemma exists_hardAdmissible_of_succ_le [Nonempty C] (I : PinningData V C) {Δ : ℕ}
    (hdegree : I.DegreeBound Δ) (hcolours : Δ + 1 ≤ Fintype.card C) :
    ∃ sigma : V → C, I.HardAdmissible sigma := by
  obtain ⟨sigma, hproper, hlist⟩ := PinningData.exists_proper_listColoring I.graph I.hardList
    (card_hardList_of_succ_le I hdegree hcolours)
  refine ⟨sigma, hproper, fun u => ?_⟩
  exact (Finset.mem_filter.mp (hlist u)).2

lemma partition_zero_pos_of_succ_le [Nonempty C] (I : PinningData V C) {Δ : ℕ}
    (hdegree : I.DegreeBound Δ) (hcolours : Δ + 1 ≤ Fintype.card C) :
    0 < I.partition 0 := by
  obtain ⟨sigma, hsigma⟩ := exists_hardAdmissible_of_succ_le I hdegree hcolours
  have hweight : I.weight 0 sigma = 1 := by
    rw [I.weight_zero_eq, if_pos hsigma]
  have hle : I.weight 0 sigma ≤ I.partition 0 :=
    Finset.single_le_sum (f := fun eta => I.weight 0 eta)
      (fun eta _ => I.weight_nonneg le_rfl eta) (Finset.mem_univ sigma)
  rw [hweight] at hle
  linarith

lemma partition_pos_of_succ_le [Nonempty C] (I : PinningData V C) {Δ : ℕ} {x : ℝ}
    (hx : 0 ≤ x) (hdegree : I.DegreeBound Δ) (hcolours : Δ + 1 ≤ Fintype.card C) :
    0 < I.partition x := by
  rcases eq_or_lt_of_le hx with hzero | hpos
  · rw [← hzero]
    exact partition_zero_pos_of_succ_le I hdegree hcolours
  · exact I.partition_pos_of_parameter_pos hpos

/-- Hard feasibility for the actual arbitrary partial colouring, at the
paper's `q ≥ Δ+1` threshold. -/
lemma normalizedPartition_zero_ne_zero [Nonempty C] (tau : PartialColouring V C)
    (G : SimpleGraph V) {Δ : ℕ} (hdegree : ∀ v, G.degree v ≤ Δ)
    (hcolours : Δ + 1 ≤ Fintype.card C) :
    normalizedPartition tau G 0 ≠ 0 := by
  have hpos := partition_zero_pos_of_succ_le (tau.toPinningData G)
    (tau.degreeBound_of_original G hdegree) hcolours
  change normalizedPartition tau G ((0 : ℝ) : ℂ) ≠ 0
  rw [normalizedPartition_ofReal]
  exact_mod_cast hpos.ne'

lemma normalizedPartition_nonnegative_ne_zero [Nonempty C]
    (tau : PartialColouring V C) (G : SimpleGraph V) {Δ : ℕ}
    (hdegree : ∀ v, G.degree v ≤ Δ) (hcolours : Δ + 1 ≤ Fintype.card C)
    {x : ℝ} (hx : 0 ≤ x) : normalizedPartition tau G (x : ℂ) ≠ 0 := by
  rw [normalizedPartition_ofReal]
  exact_mod_cast (partition_pos_of_succ_le (tau.toPinningData G) hx
    (tau.degreeBound_of_original G hdegree) hcolours).ne'

/-- The exponent after conditioning the root and removing the root's old
boundary factor.  Original free edges incident to the root remain counted:
they become the new boundary interactions with the conditioned root. -/
noncomputable def rootChildExponent (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (sigma : tau.FreeVertex → C) : ℕ :=
  (∑ u ∈ Finset.univ.erase r, tau.boundaryCount G u (sigma u)) +
    tau.freeConflictCount G sigma

/-- A normalized root child, represented on complete free configurations with
the root colour fixed.  Removing the fixed root gives the usual child state
space.  The definition makes sense even when its parent coefficient is zero. -/
noncomputable def rootChildPolynomial (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) : Polynomial ℂ :=
  ∑ sigma : tau.FreeVertex → C,
    if sigma r = a then Polynomial.X ^ rootChildExponent tau G r sigma else 0

noncomputable def rootChildPartition (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) (z : ℂ) : ℂ :=
  (rootChildPolynomial tau G r a).eval z

lemma root_exponent_split (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (sigma : tau.FreeVertex → C) :
    tau.boundaryConflictCount G sigma + tau.freeConflictCount G sigma =
      tau.boundaryCount G r (sigma r) + rootChildExponent tau G r sigma := by
  have hsum := Finset.sum_erase_add (s := (Finset.univ : Finset tau.FreeVertex))
    (f := fun u => tau.boundaryCount G u (sigma u)) (Finset.mem_univ r)
  unfold PartialColouring.boundaryConflictCount rootChildExponent
  omega

/-- The exact one-vertex recursion as a polynomial identity. -/
lemma normalizedPolynomial_root_recursion (tau : PartialColouring V C)
    (G : SimpleGraph V) (r : tau.FreeVertex) :
    normalizedPolynomial tau G =
      ∑ a : C, Polynomial.X ^ tau.boundaryCount G r a * rootChildPolynomial tau G r a := by
  unfold normalizedPolynomial rootChildPolynomial
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sigma _
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [root_exponent_split tau G r sigma, pow_add]

lemma normalizedPartition_root_recursion (tau : PartialColouring V C)
    (G : SimpleGraph V) (r : tau.FreeVertex) (z : ℂ) :
    normalizedPartition tau G z =
      ∑ a : C, z ^ tau.boundaryCount G r a * rootChildPartition tau G r a z := by
  simp [normalizedPartition, normalizedPolynomial_root_recursion tau G r, rootChildPartition,
    Polynomial.eval_finsetSum]

lemma normalizedPartition_continuous (tau : PartialColouring V C) (G : SimpleGraph V) :
    Continuous (normalizedPartition tau G) :=
  (normalizedPolynomial tau G).continuous

/-- Add a root colour to the actual partial-colouring domain. -/
def pinVertex (tau : PartialColouring V C) (r : tau.FreeVertex) (a : C) :
    PartialColouring V C where
  domain := insert r.1 tau.domain
  colour := fun v => if h : v.1 = r.1 then a else
    tau.colour ⟨v.1, (Finset.mem_insert.mp v.2).resolve_left h⟩

@[simp] lemma pinVertex_domain (tau : PartialColouring V C) (r : tau.FreeVertex) (a : C) :
    (pinVertex tau r a).domain = insert r.1 tau.domain := rfl

noncomputable def childToParent (tau : PartialColouring V C) (r : tau.FreeVertex) (a : C)
    (eta : (pinVertex tau r a).FreeVertex → C) (v : tau.FreeVertex) : C :=
  if h : v.1 = r.1 then a else eta ⟨v.1, by
    change v.1 ∉ insert r.1 tau.domain
    exact fun hp => (Finset.mem_insert.mp hp).elim h v.2⟩

@[simp] lemma childToParent_root (tau : PartialColouring V C) (r : tau.FreeVertex) (a : C)
    (eta : (pinVertex tau r a).FreeVertex → C) : childToParent tau r a eta r = a := by
  simp [childToParent]

noncomputable def parentToChild (tau : PartialColouring V C) (r : tau.FreeVertex) (a : C)
    (sigma : tau.FreeVertex → C) (v : (pinVertex tau r a).FreeVertex) : C :=
  sigma ⟨v.1, fun h => v.2 (Finset.mem_insert_of_mem h)⟩

noncomputable def childConfigEquiv (tau : PartialColouring V C) (r : tau.FreeVertex) (a : C) :
    ((pinVertex tau r a).FreeVertex → C) ≃ {sigma : tau.FreeVertex → C // sigma r = a} where
  toFun eta := ⟨childToParent tau r a eta, childToParent_root tau r a eta⟩
  invFun sigma := parentToChild tau r a sigma.1
  left_inv eta := by
    funext v
    have hv : v.1 ≠ r.1 := fun h => v.2 (by simp [h])
    simp [parentToChild, childToParent, hv]
  right_inv sigma := by
    apply Subtype.ext
    funext v
    by_cases hv : v.1 = r.1
    · have hvr : v = r := Subtype.ext hv
      subst v
      simp [childToParent, sigma.2]
    · simp [childToParent, parentToChild, hv]

lemma extend_pinVertex (tau : PartialColouring V C) (r : tau.FreeVertex) (a : C)
    (eta : (pinVertex tau r a).FreeVertex → C) :
    (pinVertex tau r a).extend eta = tau.extend (childToParent tau r a eta) := by
  funext v
  by_cases hv : v ∈ tau.domain
  · have hvr : v ≠ r.1 := fun h => r.2 (h ▸ hv)
    simp [PartialColouring.extend, pinVertex, hv, hvr]
  · by_cases hvr : v = r.1
    · subst v
      simp [PartialColouring.extend, pinVertex, hv, childToParent]
    · simp [PartialColouring.extend, pinVertex, hv, hvr, childToParent]

lemma fullConflictCount_pinVertex (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) (eta : (pinVertex tau r a).FreeVertex → C) :
    (pinVertex tau r a).fullConflictCount G eta =
      tau.fullConflictCount G (childToParent tau r a eta) := by
  unfold PartialColouring.fullConflictCount PartialColouring.fullConflictEdges
  rw [extend_pinVertex]

lemma mem_pinnedConflictEdges_pinVertex (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) (u v : V) :
    s(u, v) ∈ (pinVertex tau r a).pinnedConflictEdges G ↔
      G.Adj u v ∧ ∃ hu : u ∈ (pinVertex tau r a).domain,
        ∃ hv : v ∈ (pinVertex tau r a).domain,
          (pinVertex tau r a).colour ⟨u, hu⟩ = (pinVertex tau r a).colour ⟨v, hv⟩ := by
  rw [PartialColouring.pinnedConflictEdges, Finset.mem_filter,
    SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, PartialColouring.pinnedSameColour_mk]

lemma pinnedConflictEdges_old_part (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) :
    ((pinVertex tau r a).pinnedConflictEdges G).filter tau.pinnedEdge =
      tau.pinnedConflictEdges G := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [Finset.mem_filter, mem_pinnedConflictEdges_pinVertex]
    have hr : r.1 ∉ tau.domain := r.2
    by_cases hu : u ∈ tau.domain <;> by_cases hv : v ∈ tau.domain <;>
      by_cases hur : u = r.1 <;> by_cases hvr : v = r.1 <;>
      simp_all [PartialColouring.pinnedConflictEdges, PartialColouring.pinnedSameColour,
        PartialColouring.pinnedEdge, pinVertex]

lemma pinnedConflictEdges_new_card (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) :
    (((pinVertex tau r a).pinnedConflictEdges G).filter (fun e => ¬ tau.pinnedEdge e)).card =
      tau.boundaryCount G r a := by
  symm
  unfold PartialColouring.boundaryCount
  apply Finset.card_bij (fun p _ => s(r.1, p.1))
  · intro p hp
    obtain ⟨hpneigh, hpcolour⟩ := Finset.mem_filter.mp hp
    have hadj : G.Adj r.1 p.1 := (Finset.mem_filter.mp hpneigh).2
    have hppin : p.1 ∈ tau.domain := p.2
    have hr : r.1 ∉ tau.domain := r.2
    have hpneq : p.1 ≠ r.1 := fun h => hr (h ▸ hppin)
    simp only [Finset.mem_filter, mem_pinnedConflictEdges_pinVertex]
    simp [PartialColouring.pinnedEdge, pinVertex, hr, hppin, hpneq, hpcolour, hadj]
  · intro p _ p' _ heq
    apply Subtype.ext
    rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨h, h'⟩
    · exact h
    · exact h'.trans h
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have hr : r.1 ∉ tau.domain := r.2
      have hadj : G.Adj u v := by
        have hedge := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hedge
      simp only [Finset.mem_filter, mem_pinnedConflictEdges_pinVertex] at he
      have hdiff : u ≠ v := hadj.ne
      by_cases hu : u = r.1
      · subst u
        have hv : v ≠ r.1 := Ne.symm hdiff
        have hinfo : ∃ hvpin : v ∈ tau.domain, a = tau.colour ⟨v, hvpin⟩ := by
          simpa [PartialColouring.pinnedConflictEdges, PartialColouring.pinnedSameColour,
            PartialColouring.pinnedEdge, pinVertex, hr, hv, hadj] using he
        obtain ⟨hvpin, hcolour⟩ := hinfo
        refine ⟨⟨v, hvpin⟩, ?_, rfl⟩
        simp [PartialColouring.pinnedNeighbours, hadj, hcolour]
      · have hv : v = r.1 := by
          by_contra hvr
          have hi := he
          simp [PartialColouring.pinnedEdge, pinVertex, hu, hvr, hadj] at hi
          obtain ⟨⟨hupin, hvpin, _⟩, hnot⟩ := hi
          exact hnot hupin hvpin
        subst v
        have hinfo : ∃ hupin : u ∈ tau.domain, tau.colour ⟨u, hupin⟩ = a := by
          simpa [PartialColouring.pinnedConflictEdges, PartialColouring.pinnedSameColour,
            PartialColouring.pinnedEdge, pinVertex, hr, hu, hadj] using he
        obtain ⟨hupin, hcolour⟩ := hinfo
        refine ⟨⟨u, hupin⟩, ?_, ?_⟩
        · simp [PartialColouring.pinnedNeighbours, hadj.symm, hcolour]
        · exact Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)

lemma pinnedConflictCount_pinVertex (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) :
    (pinVertex tau r a).pinnedConflictCount G =
      tau.pinnedConflictCount G + tau.boundaryCount G r a := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (pinVertex tau r a).pinnedConflictEdges G) (p := tau.pinnedEdge)
  rw [pinnedConflictEdges_old_part, pinnedConflictEdges_new_card] at h
  exact h.symm

lemma child_exponent_pinVertex (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) (eta : (pinVertex tau r a).FreeVertex → C) :
    (pinVertex tau r a).boundaryConflictCount G eta +
        (pinVertex tau r a).freeConflictCount G eta =
      rootChildExponent tau G r (childToParent tau r a eta) := by
  have hfull := fullConflictCount_pinVertex tau G r a eta
  rw [(pinVertex tau r a).fullConflictCount_add G eta,
    tau.fullConflictCount_add G (childToParent tau r a eta), pinnedConflictCount_pinVertex] at hfull
  have hexp := root_exponent_split tau G r (childToParent tau r a eta)
  rw [childToParent_root] at hexp
  omega

/-- The conditional finite-sum child is exactly the normalized polynomial of
the graph with the root actually added to the pinning domain. -/
lemma rootChildPolynomial_eq_pinVertex (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) :
    rootChildPolynomial tau G r a = normalizedPolynomial (pinVertex tau r a) G := by
  unfold rootChildPolynomial normalizedPolynomial
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype _ (p := fun sigma : tau.FreeVertex → C => sigma r = a) (by simp)]
  symm
  apply Fintype.sum_equiv (childConfigEquiv tau r a)
  intro eta
  congr 1
  exact child_exponent_pinVertex tau G r a eta

lemma rootChildPartition_eq_pinVertex (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) (z : ℂ) :
    rootChildPartition tau G r a z = normalizedPartition (pinVertex tau r a) G z := by
  simp [rootChildPartition, normalizedPartition, rootChildPolynomial_eq_pinVertex]

/-- The paper's one-vertex recursion, with a literal enlarged partial
colouring in each child and no division by the activity. -/
lemma normalizedPartition_pinVertex_recursion (tau : PartialColouring V C)
    (G : SimpleGraph V) (r : tau.FreeVertex) (z : ℂ) :
    normalizedPartition tau G z =
      ∑ a : C, z ^ tau.boundaryCount G r a * normalizedPartition (pinVertex tau r a) G z := by
  rw [normalizedPartition_root_recursion tau G r z]
  simp only [rootChildPartition_eq_pinVertex]

lemma rootChildPartition_zero_ne_zero [Nonempty C] (tau : PartialColouring V C)
    (G : SimpleGraph V) (r : tau.FreeVertex) (a : C) {Δ : ℕ}
    (hdegree : ∀ v, G.degree v ≤ Δ) (hcolours : Δ + 1 ≤ Fintype.card C) :
    rootChildPartition tau G r a 0 ≠ 0 := by
  rw [rootChildPartition_eq_pinVertex]
  exact normalizedPartition_zero_ne_zero (pinVertex tau r a) G hdegree hcolours

end ZeroFreeness.Potts
