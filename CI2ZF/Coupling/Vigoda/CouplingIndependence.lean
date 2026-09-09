import CI2ZF.Coupling.Vigoda.Endgame
import CI2ZF.Coupling.Vigoda.ComponentCoupling
import CI2ZF.Potts.Model.Real.Endpoint
import CI2ZF.Potts.Model.PottsModel
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The stationary-comparison endgame for Potts coupling independence

The analytic and probabilistic implication from adjacent-state contraction
and boundary perturbation estimates to coupling independence is proved here.
The one-step contraction and boundary estimates are explicit hypotheses;
they must be supplied by the concrete Vigoda coupling construction.
-/

namespace CI2ZF

open scoped BigOperators
open PottsCI PottsCI.FinDist

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The positive soft-contraction numerator. -/
def ciDenominator (q Δ x : ℝ) : ℝ := q - (11 / 6 : ℝ) * (1 - x) * Δ

/-- The two-child coupling-independence estimate in the paper. -/
def ciBound (q Δ x : ℝ) : ℝ := 2 * (1 - x) * Δ / ciDenominator q Δ x

/-- Distance above the strict Vigoda line, normalized by the degree bound. -/
def ciGap (q Δ : ℝ) : ℝ := q / Δ - 11 / 6

theorem ciDenominator_pos_of_strict {q Δ x : ℝ} (hΔ : 0 ≤ Δ)
    (hx : 0 ≤ x) (hq : (11 / 6 : ℝ) * Δ < q) : 0 < ciDenominator q Δ x := by
  unfold ciDenominator
  nlinarith

theorem ciGap_pos {q Δ : ℝ} (hΔ : 0 < Δ) (hq : (11 / 6 : ℝ) * Δ < q) :
    0 < ciGap q Δ := by
  unfold ciGap
  have h := (lt_div_iff₀ hΔ).2 hq
  linarith

theorem ciBound_nonneg {q Δ x : ℝ} (hΔ : 0 ≤ Δ) (hx : x ≤ 1)
    (hden : 0 < ciDenominator q Δ x) : 0 ≤ ciBound q Δ x := by
  unfold ciBound
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hx)) hΔ) hden.le

/-- The strict-line constant is uniform over the whole physical interval. -/
theorem ciBound_le_strict_uniform {q Δ x : ℝ} (hΔ : 0 < Δ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hq : (11 / 6 : ℝ) * Δ < q) :
    ciBound q Δ x ≤ 2 / ciGap q Δ := by
  have hb : 0 < q - (11 / 6 : ℝ) * Δ := by linarith
  have hd := ciDenominator_pos_of_strict hΔ.le hx.1 hq
  have hbase : q - (11 / 6 : ℝ) * Δ ≤ ciDenominator q Δ x := by
    unfold ciDenominator
    nlinarith [mul_nonneg hx.1 hΔ.le]
  have hnum : 2 * (1 - x) * Δ ≤ 2 * Δ := by nlinarith [mul_nonneg hx.1 hΔ.le]
  calc
    ciBound q Δ x ≤ 2 * Δ / ciDenominator q Δ x := by
      exact div_le_div_of_nonneg_right hnum hd.le
    _ ≤ 2 * Δ / (q - (11 / 6 : ℝ) * Δ) :=
      div_le_div_of_nonneg_left (by positivity) hb hbase
    _ = 2 / ciGap q Δ := by
      unfold ciGap
      field_simp

/-- On the critical line, every positive base has a positive contraction gap. -/
theorem ciDenominator_pos_of_critical {q Δ x : ℝ} (hΔ : 0 < Δ)
    (hx : 0 < x) (hq : q = (11 / 6 : ℝ) * Δ) : 0 < ciDenominator q Δ x := by
  unfold ciDenominator
  rw [hq]
  nlinarith [mul_pos hx hΔ]

theorem ciBound_critical_eq {q Δ x : ℝ} (hΔ : 0 < Δ)
    (hx : 0 < x) (hq : q = (11 / 6 : ℝ) * Δ) :
    ciBound q Δ x = 12 * (1 - x) / (11 * x) := by
  unfold ciBound ciDenominator
  rw [hq]
  field_simp [ne_of_gt hx, ne_of_gt hΔ]
  ring

/-- Critical-line CI is uniform away from the hard endpoint. -/
theorem ciBound_le_critical_uniform {q Δ x δ : ℝ} (hΔ : 0 < Δ)
    (hδ : 0 < δ) (hx : x ∈ Set.Icc δ 1) (hq : q = (11 / 6 : ℝ) * Δ) :
    ciBound q Δ x ≤ 12 / (11 * δ) := by
  have hxpos : 0 < x := hδ.trans_le hx.1
  rw [ciBound_critical_eq hΔ hxpos hq]
  apply (div_le_div_iff₀ (by positivity : 0 < 11 * x)
    (by positivity : 0 < 11 * δ)).2
  have hlow := hx.1
  nlinarith [mul_nonneg hδ.le hxpos.le]

@[simp] theorem ciBound_one (q Δ : ℝ) : ciBound q Δ 1 = 0 := by
  simp [ciBound]

theorem ciBound_zero_eq_strict_uniform {q Δ : ℝ} (hΔ : 0 < Δ)
    (hq : (11 / 6 : ℝ) * Δ < q) : ciBound q Δ 0 = 2 / ciGap q Δ := by
  have hg := ciGap_pos hΔ hq
  have hd : q - (11 / 6 : ℝ) * Δ ≠ 0 := ne_of_gt (by linarith)
  unfold ciBound ciDenominator ciGap
  simp only [sub_zero, mul_one]
  field_simp

/-- At or above the Vigoda line, integrality gives the two-colour slack
required by the inherited concrete hard-endpoint continuity module. -/
theorem colours_slack_of_vigoda_line {q Δ : ℕ} (hΔ : 2 ≤ Δ)
    (hq : (11 / 6 : ℝ) * Δ ≤ q) : Δ + 2 ≤ q := by
  by_contra hh
  have hnat : q ≤ Δ + 1 := by omega
  have hreal : (q : ℝ) ≤ (Δ : ℝ) + 1 := by exact_mod_cast hnat
  have hΔreal : (2 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  nlinarith

variable {V C : Type*} [Fintype V] [Fintype C]

/-- Empty remaining vertex sets require no transition-kernel construction. -/
theorem W_ham_eq_zero_of_isEmpty [IsEmpty V] (μ ν : FinDist (V → C)) :
    W ham μ ν = 0 := by
  apply le_antisymm
  · exact W_le_bound ham_nonneg (fun σ τ => by simp [ham, hamCard])
  · exact W_nonneg ham_nonneg

/-- At activity one all pinned Potts instances on the same free set have the
same Gibbs law. -/
theorem gibbs_one_eq [Nonempty C] (I J : PinningData V C)
    (hI : 0 < I.partition 1) (hJ : 0 < J.partition 1) :
    I.gibbs 1 (by norm_num) hI = J.gibbs 1 (by norm_num) hJ := by
  have hweight (K : PinningData V C) (σ : V → C) : K.weight 1 σ = 1 := by
    unfold PinningData.weight
    simp only [one_pow, Finset.prod_const_one, one_mul]
    apply Finset.prod_eq_one
    intro e he
    induction e using Sym2.ind with
    | _ u v => simp [PinningData.edgeFactor_mk]
  have hpartition (K : PinningData V C) :
      K.partition 1 = Fintype.card (V → C) := by
    simp [PinningData.partition, hweight]
  apply FinDist.ext
  funext σ
  simp [PinningData.gibbs, hweight, hpartition]

theorem W_ham_gibbs_one [Nonempty C] (I J : PinningData V C)
    (hI : 0 < I.partition 1) (hJ : 0 < J.partition 1) :
    W ham (I.gibbs 1 (by norm_num) hI) (J.gibbs 1 (by norm_num) hJ) = 0 := by
  rw [gibbs_one_eq I J hI hJ]
  exact W_self ham_nonneg ham_self _

/-- The remaining one-step input for the *concrete* soft Vigoda kernels.
All four fields must be proved by the coupling construction; stationarity
is already a theorem and is not a field of this structure. -/
structure SoftVigodaCouplingInputs [Nonempty V] [Nonempty C]
    (I J M : PinningData V C) (Δ : ℕ) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) : Prop where
  contraction_left : ∀ σ τ : V → C, hamCard σ τ = 1 →
    W ham (Vigoda.softVigodaKernel I x hx0 hx1 σ)
      (Vigoda.softVigodaKernel I x hx0 hx1 τ) ≤
      1 - ciDenominator (Fintype.card C) Δ x /
        ((Fintype.card V : ℝ) * Fintype.card C)
  contraction_right : ∀ σ τ : V → C, hamCard σ τ = 1 →
    W ham (Vigoda.softVigodaKernel J x hx0 hx1 σ)
      (Vigoda.softVigodaKernel J x hx0 hx1 τ) ≤
      1 - ciDenominator (Fintype.card C) Δ x /
        ((Fintype.card V : ℝ) * Fintype.card C)
  boundary_left : ∀ σ : V → C,
    W ham (Vigoda.softVigodaKernel I x hx0 hx1 σ)
      (Vigoda.softVigodaKernel M x hx0 hx1 σ) ≤
      (1 - x) * Δ / ((Fintype.card V : ℝ) * Fintype.card C)
  boundary_right : ∀ σ : V → C,
    W ham (Vigoda.softVigodaKernel J x hx0 hx1 σ)
      (Vigoda.softVigodaKernel M x hx0 hx1 σ) ≤
      (1 - x) * Δ / ((Fintype.card V : ℝ) * Fintype.card C)

/-- Concrete Gibbs coupling independence follows from the four one-step
soft-kernel inputs. The free-volume factor is instantiated by `card V` and
cancels completely in the resulting estimate. -/
theorem gibbs_ci_of_softVigoda_inputs [Nonempty V] [Nonempty C]
    (I J M : PinningData V C) (Δ : ℕ) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (hgap : 0 < ciDenominator (Fintype.card C) Δ x)
    (hinput : SoftVigodaCouplingInputs I J M Δ x hx0 hx1) :
    W ham (I.gibbs x hx0.le (I.partition_pos_of_parameter_pos hx0))
      (J.gibbs x hx0.le (J.partition_pos_of_parameter_pos hx0)) ≤
      ciBound (Fintype.card C) Δ x := by
  have hq : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hn : (1 : ℝ) ≤ Fintype.card V := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos (α := V)))
  exact Vigoda.nearVigoda_two_children_endgame
    (Vigoda.softVigodaKernel I x hx0 hx1)
    (Vigoda.softVigodaKernel J x hx0 hx1)
    (Vigoda.softVigodaKernel M x hx0 hx1)
    (I.gibbs x hx0.le (I.partition_pos_of_parameter_pos hx0))
    (J.gibbs x hx0.le (J.partition_pos_of_parameter_pos hx0))
    (M.gibbs x hx0.le (M.partition_pos_of_parameter_pos hx0))
    (Vigoda.softVigodaKernel_stationary I x hx0 hx1)
    (Vigoda.softVigodaKernel_stationary J x hx0 hx1)
    (Vigoda.softVigodaKernel_stationary M x hx0 hx1)
    (1 - x) Δ (Fintype.card C) (Fintype.card V)
    (sub_nonneg.mpr hx1.le) (Nat.cast_nonneg _) hq hn hgap
    hinput.contraction_left hinput.contraction_right hinput.boundary_left hinput.boundary_right

/-- The direct activity-one identity closes the positive interval without
defining the active-constraint transition rule at its degenerate endpoint. -/
theorem gibbs_ci_of_softVigoda_inputs_le_one [Nonempty V] [Nonempty C]
    (I J M : PinningData V C) (Δ : ℕ) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hgap : 0 < ciDenominator (Fintype.card C) Δ x)
    (hinput : ∀ hx : x < 1, SoftVigodaCouplingInputs I J M Δ x hx0 hx) :
    W ham (I.gibbs x hx0.le (I.partition_pos_of_parameter_pos hx0))
      (J.gibbs x hx0.le (J.partition_pos_of_parameter_pos hx0)) ≤
      ciBound (Fintype.card C) Δ x := by
  rcases lt_or_eq_of_le hx1 with hlt | rfl
  · exact gibbs_ci_of_softVigoda_inputs I J M Δ x hx0 hlt hgap (hinput hlt)
  · rw [W_ham_gibbs_one, ciBound_one]

open Filter Topology

/-- A concrete sequence of positive physical activities tending to zero. -/
def hardApproach (n : ℕ) : PinningData.NonnegativeParameter :=
  ⟨1 / ((n : ℝ) + 1), by change 0 ≤ 1 / ((n : ℝ) + 1); positivity⟩

theorem hardApproach_pos (n : ℕ) : 0 < (hardApproach n : ℝ) := by
  change 0 < 1 / ((n : ℝ) + 1)
  positivity

theorem hardApproach_le_one (n : ℕ) : (hardApproach n : ℝ) ≤ 1 := by
  change 1 / ((n : ℝ) + 1) ≤ 1
  apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).2
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem tendsto_hardApproach :
    Tendsto hardApproach atTop (nhds PinningData.hardParameter) := by
  apply tendsto_subtype_rng.2
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The strict-line positive-activity CI estimate passes to the actual hard
Gibbs laws, with the same rational formula at zero. The premise is an
estimate on the concrete Gibbs families, not an assumed continuity axiom. -/
theorem hard_ciBound_of_positive_bound [Nonempty C] (I J : PinningData V C)
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hdegreeI : I.DegreeBound Δ) (hdegreeJ : J.DegreeBound Δ)
    (hq : (11 / 6 : ℝ) * Δ < Fintype.card C)
    (hsoft : ∀ y : PinningData.NonnegativeParameter,
      0 < (y : ℝ) → (y : ℝ) ≤ 1 →
      W ham
        (I.nonnegativeGibbs hdegreeI (colours_slack_of_vigoda_line hΔ hq.le) y)
        (J.nonnegativeGibbs hdegreeJ (colours_slack_of_vigoda_line hΔ hq.le) y) ≤
        ciBound (Fintype.card C) Δ y) :
    W ham
      (I.hardGibbs hdegreeI (colours_slack_of_vigoda_line hΔ hq.le))
      (J.hardGibbs hdegreeJ (colours_slack_of_vigoda_line hΔ hq.le)) ≤
      ciBound (Fintype.card C) Δ 0 := by
  have hΔpos : (0 : ℝ) < Δ := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hΔ)
  rw [ciBound_zero_eq_strict_uniform hΔpos hq]
  apply I.hard_W_le_of_positive_parameter_bound J hdegreeI hdegreeJ
    (colours_slack_of_vigoda_line hΔ hq.le) hardApproach tendsto_hardApproach
    (Filter.Eventually.of_forall hardApproach_pos)
    (Filter.Eventually.of_forall hardApproach_le_one)
    ham_nonneg ham_self ham_triangle ham_le_card
  intro y hy hy1
  exact (hsoft y hy hy1).trans (ciBound_le_strict_uniform hΔpos ⟨hy.le, hy1⟩ hq)

/-- The complete strict-line interval implication from concrete one-step
inputs. The hard endpoint is proved by finite Gibbs-law continuity. -/
theorem strict_ci_of_softVigoda_family [Nonempty V] [Nonempty C]
    (I J M : PinningData V C) {Δ : ℕ} (hΔ : 2 ≤ Δ)
    (hdegreeI : I.DegreeBound Δ) (hdegreeJ : J.DegreeBound Δ)
    (hq : (11 / 6 : ℝ) * Δ < Fintype.card C)
    (hinputs : ∀ (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1),
      SoftVigodaCouplingInputs I J M Δ x hx0 hx1)
    (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1) :
    W ham
      (I.nonnegativeGibbs hdegreeI (colours_slack_of_vigoda_line hΔ hq.le) x)
      (J.nonnegativeGibbs hdegreeJ (colours_slack_of_vigoda_line hΔ hq.le) x) ≤
      ciBound (Fintype.card C) Δ x := by
  have hsoft : ∀ y : PinningData.NonnegativeParameter,
      0 < (y : ℝ) → (y : ℝ) ≤ 1 →
      W ham
        (I.nonnegativeGibbs hdegreeI (colours_slack_of_vigoda_line hΔ hq.le) y)
        (J.nonnegativeGibbs hdegreeJ (colours_slack_of_vigoda_line hΔ hq.le) y) ≤
        ciBound (Fintype.card C) Δ y := by
    intro y hy hy1
    exact gibbs_ci_of_softVigoda_inputs_le_one I J M Δ y hy hy1
      (ciDenominator_pos_of_strict (Nat.cast_nonneg _) hy.le hq)
      (fun hlt => hinputs y hy hlt)
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ x from x.property) with hxzero | hxpos
  · have hx : x = PinningData.hardParameter := Subtype.ext hxzero.symm
    subst x
    exact hard_ciBound_of_positive_bound I J hΔ hdegreeI hdegreeJ hq hsoft
  · exact hsoft x hxpos hx1

/-- In the strict regime the resulting bound is independent of activity. -/
theorem strict_uniform_ci_of_softVigoda_family [Nonempty V] [Nonempty C]
    (I J M : PinningData V C) {Δ : ℕ} (hΔ : 2 ≤ Δ)
    (hdegreeI : I.DegreeBound Δ) (hdegreeJ : J.DegreeBound Δ)
    (hq : (11 / 6 : ℝ) * Δ < Fintype.card C)
    (hinputs : ∀ (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1),
      SoftVigodaCouplingInputs I J M Δ x hx0 hx1)
    (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1) :
    W ham
      (I.nonnegativeGibbs hdegreeI (colours_slack_of_vigoda_line hΔ hq.le) x)
      (J.nonnegativeGibbs hdegreeJ (colours_slack_of_vigoda_line hΔ hq.le) x) ≤
      2 / ciGap (Fintype.card C) Δ := by
  have hΔpos : (0 : ℝ) < Δ := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hΔ)
  exact (strict_ci_of_softVigoda_family I J M hΔ hdegreeI hdegreeJ hq hinputs x hx1).trans
    (ciBound_le_strict_uniform hΔpos ⟨x.property, hx1⟩ hq)

/-- The critical-line input away from zero. No hard-endpoint CI theorem is
claimed here: at equality that input requires the separate hard-colouring
result, exactly as in the paper. -/
theorem critical_uniform_ci_of_softVigoda_family [Nonempty V] [Nonempty C]
    (I J M : PinningData V C) {Δ : ℕ} (hΔ : 2 ≤ Δ)
    (hdegreeI : I.DegreeBound Δ) (hdegreeJ : J.DegreeBound Δ)
    (hq : (Fintype.card C : ℝ) = (11 / 6 : ℝ) * Δ)
    (hinputs : ∀ (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1),
      SoftVigodaCouplingInputs I J M Δ x hx0 hx1)
    {δ : ℝ} (hδ : 0 < δ) (x : PinningData.NonnegativeParameter)
    (hx : (x : ℝ) ∈ Set.Icc δ 1) :
    W ham
      (I.nonnegativeGibbs hdegreeI (colours_slack_of_vigoda_line hΔ hq.ge) x)
      (J.nonnegativeGibbs hdegreeJ (colours_slack_of_vigoda_line hΔ hq.ge) x) ≤
      12 / (11 * δ) := by
  have hΔpos : (0 : ℝ) < Δ := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hΔ)
  have hxpos : (0 : ℝ) < x := hδ.trans_le hx.1
  have hbound := gibbs_ci_of_softVigoda_inputs_le_one I J M Δ x hxpos hx.2
    (ciDenominator_pos_of_critical hΔpos hxpos hq) (fun hlt => hinputs x hxpos hlt)
  exact hbound.trans (ciBound_le_critical_uniform hΔpos hδ hx hq)

/-- The strict-line theorem including the empty remaining-vertex case.
Only nonempty instances need concrete transition-kernel inputs. -/
theorem strict_ci_including_empty [Nonempty C]
    (I J M : PinningData V C) {Δ : ℕ} (hΔ : 2 ≤ Δ)
    (hdegreeI : I.DegreeBound Δ) (hdegreeJ : J.DegreeBound Δ)
    (hq : (11 / 6 : ℝ) * Δ < Fintype.card C)
    (hinputs : ∀ [Nonempty V], ∀ (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1),
      SoftVigodaCouplingInputs I J M Δ x hx0 hx1)
    (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1) :
    W ham
      (I.nonnegativeGibbs hdegreeI (colours_slack_of_vigoda_line hΔ hq.le) x)
      (J.nonnegativeGibbs hdegreeJ (colours_slack_of_vigoda_line hΔ hq.le) x) ≤
      ciBound (Fintype.card C) Δ x := by
  by_cases hV : Nonempty V
  · let : Nonempty V := hV
    exact strict_ci_of_softVigoda_family I J M hΔ hdegreeI hdegreeJ hq hinputs x hx1
  · let : IsEmpty V := ⟨fun v => hV ⟨v⟩⟩
    rw [W_ham_eq_zero_of_isEmpty]
    exact ciBound_nonneg (Nat.cast_nonneg _) hx1
      (ciDenominator_pos_of_strict (Nat.cast_nonneg _) x.property hq)

/-- Critical-line CI on compact positive intervals, also covering an empty
remaining vertex set without constructing a flip chain. -/
theorem critical_uniform_ci_including_empty [Nonempty C]
    (I J M : PinningData V C) {Δ : ℕ} (hΔ : 2 ≤ Δ)
    (hdegreeI : I.DegreeBound Δ) (hdegreeJ : J.DegreeBound Δ)
    (hq : (Fintype.card C : ℝ) = (11 / 6 : ℝ) * Δ)
    (hinputs : ∀ [Nonempty V], ∀ (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1),
      SoftVigodaCouplingInputs I J M Δ x hx0 hx1)
    {δ : ℝ} (hδ : 0 < δ) (x : PinningData.NonnegativeParameter)
    (hx : (x : ℝ) ∈ Set.Icc δ 1) :
    W ham
      (I.nonnegativeGibbs hdegreeI (colours_slack_of_vigoda_line hΔ hq.ge) x)
      (J.nonnegativeGibbs hdegreeJ (colours_slack_of_vigoda_line hΔ hq.ge) x) ≤
      12 / (11 * δ) := by
  by_cases hV : Nonempty V
  · let : Nonempty V := hV
    exact critical_uniform_ci_of_softVigoda_family I J M hΔ hdegreeI hdegreeJ hq hinputs hδ x hx
  · let : IsEmpty V := ⟨fun v => hV ⟨v⟩⟩
    rw [W_ham_eq_zero_of_isEmpty]
    positivity

end

end CI2ZF
