import ZeroFreeness.Potts.Geometry.BFSShellMarginals
import ZeroFreeness.Coupling.Vigoda.OptionCI

/-! Root-child laws live on the root-deleted vertex set. Padding both laws
with the same fixed root colour preserves Hamming costs and makes the
actual parent graph's BFS spheres available to the shell argument. -/
namespace ZeroFreeness.Potts
open PottsCI PottsCI.FinDist Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
variable {O C : Type*} [Fintype O] [Fintype C]

def padRoot (a : C) (σ : O → C) : Option O → C := Option.elim' a σ

omit [Fintype C] in
theorem ham_padRoot (a : C) (σ τ : O → C) :
    ham (padRoot a σ) (padRoot a τ) = ham σ τ := by
  unfold ham hamCard
  rw [natCast_card_filter, natCast_card_filter, Fintype.sum_option]
  simp only [padRoot, Option.elim'_none, Option.elim'_some, ne_eq,
    not_true_eq_false, if_false, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

def paddedRootLaw (μ : FinDist (O → C)) (a : C) : FinDist (Option O → C) :=
  mapLaw μ (padRoot a)

theorem W_paddedRootLaw_le (μ ν : FinDist (O → C)) (a : C) :
    W ham (paddedRootLaw μ a) (paddedRootLaw ν a) ≤ W ham μ ν := by
  have ht := W_mapLaw_le (μ := μ) (ν := ν) (padRoot a) (padRoot a) ham ham_nonneg
  simpa only [ham_padRoot, paddedRootLaw] using ht

/-- The selected sphere is measured in the parent graph, even though the
two distributions are on the common root-deleted state space. -/
theorem exists_low_root_sphere (I : PinningData (Option O) C)
    (μ ν : FinDist (O → C)) (a : C) {R : ℕ} (hR : 0 < R)
    {B : ℝ} (hCI : W ham μ ν ≤ B) :
    ∃ r : ℕ, 2 ≤ r ∧ r ≤ R + 1 ∧
      W ham (BFS.sphereMarginal (paddedRootLaw μ a) I.graph none r)
        (BFS.sphereMarginal (paddedRootLaw ν a) I.graph none r) ≤ B / R :=
  BFS.exists_low_W_sphereMarginal _ _ I.graph none hR ((W_paddedRootLaw_le μ ν a).trans hCI)

/-- The low-cost BFS sphere follows from the proved concrete Potts CI,
with no transportation-bound assumption left for the caller. -/
theorem strict_root_exists_low_sphere [Nonempty C]
    (I : PinningData (Option O) C) {Δ : ℕ} (hΔ : 2 ≤ Δ) (hdegree : I.DegreeBound Δ)
    (hq : (11 / 6 : ℝ) * Δ < Fintype.card C) (a b : C)
    (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1)
    {R : ℕ} (hR : 0 < R) :
    let μ := (optionChildData I a).nonnegativeGibbs (optionChildData_degreeBound I hdegree a)
      (colours_slack_of_vigoda_line hΔ hq.le) x
    let ν := (optionChildData I b).nonnegativeGibbs (optionChildData_degreeBound I hdegree b)
      (colours_slack_of_vigoda_line hΔ hq.le) x
    ∃ r : ℕ, 2 ≤ r ∧ r ≤ R + 1 ∧
      W ham (BFS.sphereMarginal (paddedRootLaw μ a) I.graph none r)
        (BFS.sphereMarginal (paddedRootLaw ν a) I.graph none r) ≤
          (2 / ciGap (Fintype.card C) Δ) / R :=
  exists_low_root_sphere I _ _ a hR (option_root_strict_uniform_ci I hΔ hdegree hq a b x hx1)

end
end ZeroFreeness.Potts
