import ZeroFreeness.Coupling.Girth.Covariance.Insertion.Beta

/-! The scalar estimates instantiated in the actual two-layer insertion model. -/
namespace ZeroFreeness.Appendix.Girth
open scoped BigOperators
open PottsCI Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {Ω U O C : Type*} [Fintype Ω] [Fintype U] [Fintype O] [Fintype C]
variable [DecidableEq U] [DecidableEq C]

namespace InsertionModel
variable (M : InsertionModel Ω U O C)

def Q (s : ℝ) (c : C) : ℝ := ∏ u, (1 - s * M.p u c)
def centredCavitySum (c : C) (ω : Ω) : ℝ := ∑ u, (M.pi u c ω - M.p u c)

def scalarInsertion (c : C) (s B Δ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hB0 : 0 ≤ B) (hB1 : B < 1) (hdegree : (Fintype.card U : ℝ) ≤ Δ)
    (hcap : ∀ u ω, M.pi u c ω ≤ B) : ScalarInsertion Ω U where
  μ := M.shell
  π := fun u => M.pi u c
  s := s
  B := B
  Δ := Δ
  s_nonneg := hs0
  s_le_one := hs1
  B_nonneg := hB0
  B_lt_one := hB1
  degree := hdegree
  π_nonneg u ω := (M.cavity ω u).nonneg c
  π_le := hcap

theorem insertion_T_lower (c : C) {s B Δ : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hB0 : 0 ≤ B) (hB1 : B < 1) (hdegree : (Fintype.card U : ℝ) ≤ Δ)
    (hcap : ∀ u ω, M.pi u c ω ≤ B) :
    Real.exp (-(Δ * B) - Δ * B ^ 2 / (2 * (1 - B))) ≤ M.T s c := by
  exact (M.scalarInsertion c s B Δ hs0 hs1 hB0 hB1 hdegree hcap).T_lower

theorem insertion_T_pos (c : C) {s B Δ : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hB0 : 0 ≤ B) (hB1 : B < 1) (hdegree : (Fintype.card U : ℝ) ≤ Δ)
    (hcap : ∀ u ω, M.pi u c ω ≤ B) : 0 < M.T s c :=
  (M.scalarInsertion c s B Δ hs0 hs1 hB0 hB1 hdegree hcap).T_pos

theorem insertion_log_quotient (c : C) {s B Δ VM : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hB0 : 0 ≤ B) (hB1 : B < 1) (hdegree : (Fintype.card U : ℝ) ≤ Δ)
    (hcap : ∀ u ω, M.pi u c ω ≤ B) (hVM : variance M.shell (M.centredCavitySum c) ≤ VM) :
    |Real.log (M.T s c / M.Q s c)| ≤ Δ * B ^ 2 / (2 * (1 - B)) + Real.exp (Δ * B) * VM / 2 :=
  (M.scalarInsertion c s B Δ hs0 hs1 hB0 hB1 hdegree hcap).log_quotient_bound hVM

theorem insertion_beta_mean_square (c : C) {s B Δ Vπ VM : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hB0 : 0 ≤ B) (hB1 : B < 1) (hdegree : (Fintype.card U : ℝ) ≤ Δ)
    (hcap : ∀ u ω, M.pi u c ω ≤ B) (hVπ : ∀ u, variance M.shell (M.pi u c) ≤ Vπ)
    (hVM : variance M.shell (M.centredCavitySum c) ≤ VM) (u : U) :
    expectReal M.shell (fun ω => M.beta s u c ω ^ 2) ≤
      ((1 / (1 - B)) ^ 2 * Real.sqrt Vπ +
        (1 / (1 - B)) * Real.exp (Δ * B + 2 * (Δ * B ^ 2 / (2 * (1 - B)))) *
          (Real.sqrt VM + Δ * B ^ 2 / (2 * (1 - B)))) ^ 2 :=
  (M.scalarInsertion c s B Δ hs0 hs1 hB0 hB1 hdegree hcap).beta_mean_square_bound hVπ hVM u

end InsertionModel
end
end ZeroFreeness.Appendix.Girth
