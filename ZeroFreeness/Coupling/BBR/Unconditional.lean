import ZeroFreeness.Coupling.BBR.Certificate
import ZeroFreeness.Coupling.BBR.TotalInfluence
import ZeroFreeness.Coupling.BBR.Spatial
import ZeroFreeness.Coupling.BBR.Relative
import ZeroFreeness.Coupling.BBR.Proposition26

/-! Companion Lemmas 7.1, 7.2, 7.4 and 7.5 with the proved BBR results
supplied: the same statements as `contraction_certificate`,
`point_certificate`, `total_influence_decay`, `root_spatial_energy` and
`root_relative_ssm`, without their `Literature` argument. -/
namespace ZeroFreeness.Appendix.BBR
open scoped BigOperators
open Finset Set PottsCI
open ZeroFreeness.Appendix.Girth
noncomputable section
set_option linter.unusedSectionVars false

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

/-- Companion Lemma 7.1, the BBR contraction certificate. -/
theorem contraction_certificate_unconditional {Δ : ℕ}
    (hq : 3 ≤ Fintype.card C)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / Fintype.card C)
    {x : ℝ} (hx : x ∈ Icc (start (Fintype.card C) Δ) 1)
    (t u : Girth.CavityTree C) (ht : t.DegreeBudget Δ) (hu : u.DegreeBudget Δ)
    (hdom : CLMM.SameDomain t u) (hb : t.boundary = u.boundary) :
    (t.degree : ℝ) * ((1 - x) / Real.exp 1) * segmentWeightSquare x (t.message x) (u.message x) ≤
      contractionSquare Δ :=
  contraction_certificate (literature C) hq hr hx t u ht hu hdom hb

/-- Companion Lemma 7.2, the pointwise differential contraction. -/
theorem point_certificate_unconditional {Δ : ℕ}
    (hq : 3 ≤ Fintype.card C)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / Fintype.card C)
    {x : ℝ} (hx : x ∈ Icc (start (Fintype.card C) Δ) 1)
    (t : Girth.CavityTree C) (ht : t.DegreeBudget Δ) :
    (t.degree : ℝ) * pointCoefficient x t ≤ contractionSquare Δ :=
  point_certificate (literature C) hq hr hx t ht

/-- Companion Proposition 7.4, tree total-influence decay. -/
theorem total_influence_decay_unconditional
    {Δ : ℕ} (hq : 3 ≤ Fintype.card C)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / Fintype.card C)
    {x : ℝ} (hx : x ∈ Icc (start (Fintype.card C) Δ) 1)
    (d : ℕ) (b : C → ℕ) (child : Fin d → Girth.CavityTree C)
    (hroot : d + (∑ c, b c) ≤ Δ) (ht : ∀ i, (child i).DegreeBudget Δ)
    (k : ℕ) (a z : C) :
    (Girth.CavityTree.node d b child).levelTotalVariation x ((start_mem hq hr).1.trans_le hx.1) (k + 1) a z ≤
      totalInfluenceConstant (Fintype.card C) Δ (start (Fintype.card C) Δ) * contractionRate Δ ^ k :=
  total_influence_decay (literature C) hq hr hx d b child hroot ht k a z

/-- Companion Lemma 7.5, message form of the uniform relative SSM. -/
theorem root_spatial_energy_unconditional {Δ : ℕ}
    (hq : 3 ≤ Fintype.card C)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / Fintype.card C)
    {x : ℝ} (hx : x ∈ Icc (start (Fintype.card C) Δ) 1)
    (k d : ℕ) (b : C → ℕ) (t u : Fin d → Girth.CavityTree C)
    (hroot : d + (∑ c, b c) ≤ Δ) (ht : ∀ i, (t i).DegreeBudget Δ) (hu : ∀ i, (u i).DegreeBudget Δ)
    (hdom : ∀ i, CLMM.SameDomain (t i) (u i)) (hag : ∀ i, Girth.CavityTree.Agreement k (t i) (u i)) :
    messageDistance x (.node d b t) (.node d b u) ≤
      (Δ : ℝ) * (Fintype.card C : ℝ) * contractionSquare Δ ^ k :=
  root_spatial_energy (literature C) hq hr hx k d b t u hroot ht hu hdom hag

/-- Companion Lemma 7.5, uniform relative SSM in ratio form. -/
theorem root_relative_ssm_unconditional {Δ : ℕ}
    (hq : 3 ≤ Fintype.card C)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / Fintype.card C)
    {x : ℝ} (hx : x ∈ Icc (start (Fintype.card C) Δ) 1)
    (k d : ℕ) (b : C → ℕ) (t u : Fin d → Girth.CavityTree C)
    (hroot : d + (∑ c, b c) ≤ Δ) (ht : ∀ i, (t i).DegreeBudget Δ) (hu : ∀ i, (u i).DegreeBudget Δ)
    (hdom : ∀ i, CLMM.SameDomain (t i) (u i)) (hag : ∀ i, Girth.CavityTree.Agreement k (t i) (u i)) (c : C) :
    |(Girth.CavityTree.node d b t).probability x c / (Girth.CavityTree.node d b u).probability x c - 1| ≤
      relativeConstant (Fintype.card C) Δ (start (Fintype.card C) Δ) * contractionRate Δ ^ (k + 2) :=
  root_relative_ssm (literature C) hq hr hx k d b t u hroot ht hu hdom hag c

end
end ZeroFreeness.Appendix.BBR
