import ZeroFreeness.LeeYang.TransportBFS
import ZeroFreeness.LeeYang.InductionState

/-! Canonical exterior logs are Hamming Lipschitz because changing one
shell colour is exactly a root response of its actual temporary unpinning. -/
namespace ZeroFreeness.LeeYang
open PottsCI ZeroFreeness.Potts ZeroFreeness.Potts.Separator ZeroFreeness.Potts.OptionBFS
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {U S O C : Type*} [Fintype U] [Fintype S] [Fintype O] [Fintype C]

theorem exterior_logs_lipschitz_of_actual_repinning_responses
    (I : PinningData (Separator.Vertex U S O) C)
    (d : Separator.Vertex U S O → C → ℂ)
    {r α : ℝ} (hr : 0 < r) (h : (S → C) → ℂ → ℂ)
    (hzero : ∀ ξ, h ξ 0 = 0)
    (hdiff : ∀ ξ, DifferentiableOn ℂ (h ξ) (Metric.ball 0 r))
    (hexp : ∀ ξ, ∀ z ∈ Metric.ball 0 r,
      Complex.exp (h ξ z) = fieldCurve (exteriorData I ξ) (exteriorField d) z /
        fieldCurve (exteriorData I ξ) (exteriorField d) 0)
    (hroot : ∀ (ξ : S → C) (s : S), CurveRootResponses
      (unpinnedExteriorData I ξ s) (fieldPull (unpinShellEmbedding s) d) r α) :
    ∀ z ∈ Metric.ball 0 r, ∀ ξ ξ' : S → C,
      ‖h ξ z - h ξ' z‖ ≤ α * ham ξ ξ' := by
  have hstep (ξ : S → C) (s : S) (a : C) :
      ∀ z ∈ Metric.ball 0 r, ‖h (Function.update ξ s a) z - h ξ z‖ ≤ α := by
    obtain ⟨L, hLzero, hLdiff, hLexp, hLbound⟩ := hroot ξ s a (ξ s)
    have hEq : Set.EqOn (fun z => h (Function.update ξ s a) z - h ξ z) L (Metric.ball 0 r) := by
      apply logs_eq_on_ball_of_exp_eq hr _ L ((hdiff _).sub (hdiff ξ)) hLdiff
      · intro z hz
        change Complex.exp (h (Function.update ξ s a) z - h ξ z) = Complex.exp (L z)
        rw [Complex.exp_sub, hexp _ z hz, hexp _ z hz, hLexp z hz]
        simp only [fieldCurve_unpinnedExterior, Function.update_eq_self]
      · change h (Function.update ξ s a) 0 - h ξ 0 = L 0
        rw [hzero, hzero, sub_self, hLzero]
    intro z hz
    rw [show h (Function.update ξ s a) z - h ξ z = L z from hEq hz]
    exact hLbound z hz
  intro z hz ξ ξ'
  exact norm_sub_le_ham_of_coordinates (fun η => h η z) (fun η s a => hstep η s a z hz) ξ ξ'

end
end ZeroFreeness.LeeYang

namespace ZeroFreeness.LeeYang
open PottsCI ZeroFreeness.Potts ZeroFreeness.Potts.Separator ZeroFreeness.Potts.OptionBFS
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] optionBFSMarginalInsideEq optionBFSMarginalShellEq
  optionBFSMarginalOutsideEq optionBFSMarginalInsideFintype optionBFSMarginalOutsideFintype
universe u v
variable {O : Type u} {C : Type v} [Fintype O] [Fintype C]
local instance (priority := 2000) : DecidableEq (Option O) := Classical.decEq _

theorem childSplit_exterior_response_logs (F : PinningFamily.{u, v} C)
    (I : PinningData (Option O) C) (hI : F.contains I) (a : C)
    (d : Option O → C → ℂ) (hdir : DirectionBound d)
    {Δ : ℕ} (hd : I.DegreeBound Δ) (k : ℕ)
    (hs : Nonempty (BFS.Shell I.graph none k))
    {r α : ℝ} (hr : 0 < r)
    (hNZ : SmallerCurvesNonzero F Δ (Fintype.card (Option O)) r)
    (hRoot : SmallerCurveResponses F Δ (Fintype.card (Option O)) r α) :
    ∃ h : (BFS.Shell I.graph none k → C) → ℂ → ℂ,
      (∀ ξ, h ξ 0 = 0) ∧
      (∀ ξ, DifferentiableOn ℂ (h ξ) (Metric.ball 0 r)) ∧
      (∀ ξ, ∀ z ∈ Metric.ball 0 r, Complex.exp (h ξ z) =
        fieldCurve (exteriorData (childSplit I a k) ξ) (fieldPull Subtype.val d) z /
          fieldCurve (exteriorData (childSplit I a k) ξ) (fieldPull Subtype.val d) 0) ∧
      ∀ z ∈ Metric.ball 0 r, ∀ ξ ξ', ‖h ξ z - h ξ' z‖ ≤ α * ham ξ ξ' := by
  have hm := F.childSplit_mem hI a k
  have hsep := childSplit_separates I a k
  have hdegree := childSplit_degreeBound I a k hd
  have hnz (ξ : BFS.Shell I.graph none k → C) :
      CurveNonzeroOn (exteriorData (childSplit I a k) ξ) (fieldPull Subtype.val d) r :=
    hNZ _ (F.exterior_mem hm ξ) (exteriorData_degreeBound _ hsep hdegree ξ)
      (outside_card_lt_parent I.graph k) _ (hdir.pull Subtype.val)
  choose h hzero hdiff hexp using fun ξ => exists_curve_response_log _ _ hr (hnz ξ)
  refine ⟨h, hzero, hdiff, hexp, ?_⟩
  apply exterior_logs_lipschitz_of_actual_repinning_responses (childSplit I a k)
    (fieldPull (parentValue I.graph k) d) hr h hzero hdiff hexp
  intro ξ s
  exact hRoot (unpinnedExteriorData (childSplit I a k) ξ s) (F.unpinnedExterior_mem hm ξ s)
    (unpinnedExterior_degreeBound _ hdegree ξ s) (unpinOutside_card_lt_parent I.graph k hs)
    _ ((hdir.pull _).pull _)

end
end ZeroFreeness.LeeYang
