import ZeroFreeness.Coupling.Girth.Covariance.Response.Insertion
import ZeroFreeness.Potts.Model.OptionPartition
import ZeroFreeness.Potts.Geometry.GenericGibbsRelabel

/-! The insertion response identity for the actual root-deleted and
root-pinned Potts models. All likelihoods and conditional means are
derived from the finite graph weights. -/
namespace ZeroFreeness.Appendix.Girth
open scoped BigOperators
open PottsCI ZeroFreeness.Potts ZeroFreeness.Potts.Separator
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C] [Nonempty C]

namespace GraphResponseRoot
variable (I : PinningData (Option V) C)

abbrev Neighbour := ↥(optionRootNeighbours I)
def coordinate (u : Neighbour I) (σ : V → C) : C := σ u.val
def rootCoordinate (σ : Option V → C) : C := σ none
def join (a : C) (σ : V → C) : Option V → C := Option.elim' a σ

def coloringEquiv : (Option V → C) ≃ C × (V → C) where
  toFun σ := (σ none, fun v => σ (some v))
  invFun a := join a.1 a.2
  left_inv σ := by funext v; cases v <;> rfl
  right_inv a := rfl

theorem sum_colorings {M : Type*} [AddCommMonoid M] (f : (Option V → C) → M) :
    (∑ σ, f σ) = ∑ a, ∑ σ : V → C, f (join a σ) := by
  rw [Fintype.sum_equiv coloringEquiv _ (fun p => f (join p.1 p.2))
    (fun σ => by congr 1; exact (coloringEquiv.left_inv σ).symm), Fintype.sum_prod_type]

theorem child_weight (x : ℝ) (a : C) (σ : V → C) :
    (optionChildData I a).weight x σ = (optionMiddleData I).weight x σ *
      RootInsertion.likelihood (coordinate I) (1 - x) a σ := by
  unfold PinningData.weight optionChildData addBoundarySet
  simp only [pow_add, Finset.prod_mul_distrib]
  have hp : (∏ v : V, x ^ (if v ∈ optionRootNeighbours I ∧ σ v = a then (1 : ℕ) else 0)) =
      RootInsertion.likelihood (coordinate I) (1 - x) a σ := by
    unfold RootInsertion.likelihood coordinate
    rw [← Finset.prod_subtype (optionRootNeighbours I) (fun _ => Iff.rfl)
      (fun v => 1 - (1 - x) * colourIndicator a (σ v))]
    have hfilter : (optionRootNeighbours I) = Finset.univ.filter (fun v => v ∈ optionRootNeighbours I) := by simp
    rw [hfilter, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro v _
    by_cases hv : v ∈ optionRootNeighbours I <;>
      by_cases hc : σ v = a <;> simp [colourIndicator, hv, hc]
  rw [← hp]
  ring

theorem parent_weight (x : ℝ) (a : C) (σ : V → C) :
    I.weight x (join a σ) = x ^ I.boundaryCount none a * (optionChildData I a).weight x σ := by
  let τ : Separator.Vertex Empty Unit V → C := Separator.join (fun e => e.elim) (fun _ => a) σ
  have he : (relabelColouring optionSeparatorEquiv).symm τ = join a σ := by
    funext v
    cases v <;> rfl
  rw [← he, ← weight_relabel I optionSeparatorEquiv x τ]
  rw [real_weight_eq_product, real_weight_eq_product]
  change Separator.weight (optionSeparatorData I) x τ = _
  rw [show τ = Separator.join (fun e => e.elim) (fun _ => a) σ from rfl,
    weight_join _ (optionSeparatorData_separates I), optionSeparator_insideWeight,
    exteriorWeight_eq_pinningProductWeight _ (optionSeparatorData_separates I),
    optionSeparatorData_exterior]

variable (x : ℝ) (hx : 0 < x)

def parentLaw : FinDist (Option V → C) := I.gibbs x hx.le (I.partition_pos_of_parameter_pos hx)
def deletedLaw : FinDist (V → C) :=
  (optionMiddleData I).gibbs x hx.le ((optionMiddleData I).partition_pos_of_parameter_pos hx)
def childLaw (a : C) : FinDist (V → C) :=
  (optionChildData I a).gibbs x hx.le ((optionChildData I a).partition_pos_of_parameter_pos hx)

theorem child_normalizer (a : C) :
    RootInsertion.normalizer (deletedLaw I x hx) (coordinate I) (1 - x) a =
      (optionChildData I a).partition x / (optionMiddleData I).partition x := by
  unfold RootInsertion.normalizer expectReal deletedLaw PinningData.gibbs
  simp only
  have he (σ : V → C) : (optionMiddleData I).weight x σ / (optionMiddleData I).partition x *
      RootInsertion.likelihood (coordinate I) (1 - x) a σ =
        (optionChildData I a).weight x σ / (optionMiddleData I).partition x := by
    rw [child_weight]
    ring
  simp_rw [he]
  rw [← Finset.sum_div]
  rfl

theorem normalizer_pos (a : C) :
    0 < RootInsertion.normalizer (deletedLaw I x hx) (coordinate I) (1 - x) a := by
  rw [child_normalizer]
  exact div_pos ((optionChildData I a).partition_pos_of_parameter_pos hx)
    ((optionMiddleData I).partition_pos_of_parameter_pos hx)

theorem insertionMean_eq_child (f : (V → C) → ℝ) (a : C) :
    RootInsertion.insertionMean (deletedLaw I x hx) (coordinate I) (1 - x) f a =
      expectReal (childLaw I x hx a) f := by
  unfold RootInsertion.insertionMean
  rw [child_normalizer]
  unfold expectReal deletedLaw childLaw PinningData.gibbs
  simp only
  have he (σ : V → C) : (optionMiddleData I).weight x σ / (optionMiddleData I).partition x *
      (f σ * RootInsertion.likelihood (coordinate I) (1 - x) a σ) =
        (optionChildData I a).weight x σ * f σ / (optionMiddleData I).partition x := by
    rw [child_weight]
    ring
  simp_rw [he]
  rw [← Finset.sum_div]
  have hd : (∑ σ, (optionChildData I a).weight x σ / (optionChildData I a).partition x * f σ) =
      (∑ σ, (optionChildData I a).weight x σ * f σ) / (optionChildData I a).partition x := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  rw [hd]
  field_simp [((optionMiddleData I).partition_pos_of_parameter_pos hx).ne',
    ((optionChildData I a).partition_pos_of_parameter_pos hx).ne']

def rootLaw : FinDist C where
  w a := x ^ I.boundaryCount none a * (optionChildData I a).partition x / I.partition x
  nonneg a := div_nonneg (mul_nonneg (pow_nonneg hx.le _) ((optionChildData I a).partition_nonneg hx.le))
    (I.partition_nonneg hx.le)
  sum_one := by
    rw [← Finset.sum_div]
    have hp := option_parent_partition I x
    simp_rw [← real_partition_eq_product] at hp
    rw [← hp]
    exact div_self (I.partition_pos_of_parameter_pos hx).ne'

theorem rootLaw_pos (a : C) : 0 < (rootLaw I x hx).w a :=
  div_pos (mul_pos (pow_pos hx _) ((optionChildData I a).partition_pos_of_parameter_pos hx))
    (I.partition_pos_of_parameter_pos hx)

theorem parent_expectation (f : (Option V → C) → ℝ) :
    expectReal (parentLaw I x hx) f =
      expectReal (rootLaw I x hx) (fun a => expectReal (childLaw I x hx a) (fun σ => f (join a σ))) := by
  unfold expectReal parentLaw childLaw rootLaw PinningData.gibbs
  simp only
  rw [sum_colorings]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [parent_weight]
  field_simp [((optionChildData I a).partition_pos_of_parameter_pos hx).ne']

theorem rootMarginal_eq : coordinateMarginal (parentLaw I x hx) rootCoordinate = rootLaw I x hx := by
  apply FinDist.ext
  funext a
  rw [← coordinateIndicator_mean, parent_expectation]
  have he : (fun b => expectReal (childLaw I x hx b) (fun σ => colourIndicator a (rootCoordinate (join b σ)))) =
      fun b => colourIndicator a b := by
    funext b
    exact expectReal_const (childLaw I x hx b) (colourIndicator a b)
  rw [he]
  exact expect_colourIndicator _ _

theorem root_mean (f : (Option V → C) → ℝ) (a : C) :
    coordinateMean (parentLaw I x hx) rootCoordinate f a =
      expectReal (childLaw I x hx a) (fun σ => f (join a σ)) := by
  unfold coordinateMean
  rw [rootMarginal_eq, parent_expectation]
  have he : (fun b => expectReal (childLaw I x hx b) (fun σ => f (join b σ) * colourIndicator a (rootCoordinate (join b σ)))) =
      fun b => expectReal (childLaw I x hx b) (fun σ => f (join b σ)) * colourIndicator a b := by
    funext b
    exact expectReal_mul_const (childLaw I x hx b) (fun σ => f (join b σ)) (colourIndicator a b)
  rw [he]
  simp only [expectReal, colourIndicator, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp [(rootLaw_pos I x hx a).ne']

theorem root_source_score (f : (Option V → C) → ℝ) :
    responseScore (1 - x) (parentLaw I x hx) rootCoordinate f =
      scoreSource (1 - x) (rootLaw I x hx)
        (fun a => expectReal (childLaw I x hx a) (fun σ => f (join a σ))) := by
  funext a
  have hp : 0 < (coordinateMarginal (parentLaw I x hx) rootCoordinate).w a := by
    rw [rootMarginal_eq]
    exact rootLaw_pos I x hx a
  rw [responseScore_eq _ _ _ _ _ hp, rootMarginal_eq, root_mean, parent_expectation]
  rfl

def additiveSource (fv : C → ℝ) (f : (V → C) → ℝ) (σ : Option V → C) : ℝ :=
  fv (σ none) + f (fun v => σ (some v))

theorem additive_root_score (fv : C → ℝ) (f : (V → C) → ℝ) :
    responseScore (1 - x) (parentLaw I x hx) rootCoordinate (additiveSource fv f) =
      scoreSource (1 - x) (rootLaw I x hx)
        (fun a => fv a + RootInsertion.insertionMean (deletedLaw I x hx) (coordinate I) (1 - x) f a) := by
  rw [root_source_score]
  congr 1
  funext a
  rw [insertionMean_eq_child]
  change expectReal (childLaw I x hx a) (fun σ => fv a + f σ) = _
  rw [expectReal_add, expectReal_const]

theorem deleted_marginal_pos (u : Neighbour I) (a : C) :
    0 < (coordinateMarginal (deletedLaw I x hx) (coordinate I u)).w a := by
  rw [← coordinateIndicator_mean]
  have hp : 0 < (deletedLaw I x hx).w (fun _ => a) :=
    div_pos ((optionMiddleData I).weight_pos hx _) ((optionMiddleData I).partition_pos_of_parameter_pos hx)
  have hh : (deletedLaw I x hx).w (fun _ => a) ≤
      expectReal (deletedLaw I x hx) (fun σ => colourIndicator a (coordinate I u σ)) := by
    calc
      _ = (deletedLaw I x hx).w (fun _ => a) *
          colourIndicator a (coordinate I u (fun _ => a)) := by simp [coordinate, colourIndicator]
      _ ≤ _ := Finset.single_le_sum (s := Finset.univ)
        (f := fun σ => (deletedLaw I x hx).w σ * colourIndicator a (coordinate I u σ))
        (fun σ _ => mul_nonneg ((deletedLaw I x hx).nonneg σ)
        (by unfold colourIndicator; split_ifs <;> norm_num)) (Finset.mem_univ _)
  exact hp.trans_le hh

theorem deleted_denominator_pos (u : Neighbour I) (a : C) :
    0 < 1 - (1 - x) * (coordinateMarginal (deletedLaw I x hx) (coordinate I u)).w a := by
  have hp := deleted_marginal_pos I x hx u a
  have hp1 := probability_atom_le_one (coordinateMarginal (deletedLaw I x hx) (coordinate I u)) a
  have hxp := mul_pos hx hp
  nlinarith

/-- The appendix response identity on the original finite graph law.
The deleted responses contain the entire remaining observable. -/
theorem actual_response_recursion (fv : C → ℝ) (f : (V → C) → ℝ) :
    responseScore (1 - x) (parentLaw I x hx) rootCoordinate (additiveSource fv f) =
      fun c => responseBlockAction (1 - x) (rootLaw I x hx)
        (fun u => coordinateMarginal (deletedLaw I x hx) (coordinate I u))
        (fun u => responseScore (1 - x) (deletedLaw I x hx) (coordinate I u) f) c +
        scoreSource (1 - x) (rootLaw I x hx)
          (fun c => fv c + RootInsertion.defect (deletedLaw I x hx) (coordinate I) (1 - x) f c) c := by
  rw [additive_root_score]
  exact response_recursion (deletedLaw I x hx) (coordinate I) (1 - x) (rootLaw I x hx) fv f
    (fun c => (normalizer_pos I x hx c).ne') (deleted_marginal_pos I x hx)
    (fun u c => (deleted_denominator_pos I x hx u c).ne')

end GraphResponseRoot
end
end ZeroFreeness.Appendix.Girth
