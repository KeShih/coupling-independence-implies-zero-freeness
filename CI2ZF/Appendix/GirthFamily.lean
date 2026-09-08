import CI2ZF.Appendix.GirthGeometry
import CI2ZF.FamilyUniformTransfer
import CI2ZF.UniformZeroFreePackaging

/-!
# The large-girth family and endpoint-to-zero-free bridge

The admissible class is the actual free residual graph's extended girth.
It is closed under arbitrary further pinning and induced restriction.
A uniform positive-activity CI estimate on that class is extended to both
physical endpoints and fed into the proved family CI-to-zero-free theorem.
-/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open PottsCI PottsCI.FinDist CI2ZF.Potts CI2ZF.Potts.Separator Set Metric

noncomputable section

attribute [local instance] Classical.propDecidable

universe u v

def largeGirthFamily (C : Type v) [Fintype C] (g : ℕ) : PinningFamily.{u, v} C where
  contains I := (g : ℕ∞) ≤ I.graph.egirth
  restrict_mem I e p _ hI := by
    exact hI.trans (SimpleGraph.Embedding.comap e I.graph).isContained.egirth_le

variable {C : Type v} [Fintype C] [Nonempty C]

/-- The positive-temperature conclusion expected from the general CLMM
transfer: actual root-conditioned Gibbs laws on every admissible graph. -/
def SoftLargeGirthCoupling (C : Type v) [Fintype C] [Nonempty C]
    (Δ g : ℕ) (K : ℝ) : Prop :=
  ∀ {O : Type u} [Fintype O] (I : PinningData (Option O) C), I.DegreeBound Δ →
    (g : ℕ∞) ≤ I.graph.egirth → ∀ a b : C, ∀ x : ℝ, ∀ hx : 0 < x, x < 1 →
    W ham ((optionChildData I a).gibbs x hx.le ((optionChildData I a).partition_pos_of_parameter_pos hx))
      ((optionChildData I b).gibbs x hx.le ((optionChildData I b).partition_pos_of_parameter_pos hx)) ≤ K

/-- Finite-state continuity supplies the hard endpoint; activity one is
the common product law. No hard-colouring literature input is needed. -/
theorem closed_root_coupling_of_soft {Δ g : ℕ} {K : ℝ}
    (hq : Δ + 2 ≤ Fintype.card C) (hK : 0 ≤ K)
    (hsoft : SoftLargeGirthCoupling.{u, v} C Δ g K)
    (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1) :
    (largeGirthFamily.{u, v} C g).RootCouplingBound Δ (by omega) x K := by
  intro O _ I hI hd a b
  have hda := optionChildData_degreeBound I hd a
  have hdb := optionChildData_degreeBound I hd b
  have hpos : ∀ y : PinningData.NonnegativeParameter, 0 < (y : ℝ) → (y : ℝ) ≤ 1 →
      W ham ((optionChildData I a).nonnegativeGibbs hda hq y)
        ((optionChildData I b).nonnegativeGibbs hdb hq y) ≤ K := by
    intro y hy hy1
    rcases lt_or_eq_of_le hy1 with hylt | hyeq
    · exact hsoft I hd hI a b y hy hylt
    · have hyeq' : y = ⟨1, by norm_num⟩ := Subtype.ext hyeq
      subst y
      rw [PinningData.nonnegativeGibbs, PinningData.nonnegativeGibbs, W_ham_gibbs_one]
      exact hK
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ x from x.property) with hxzero | hxpos
  · have hxeq : x = PinningData.hardParameter := Subtype.ext hxzero.symm
    subst x
    exact (optionChildData I a).hard_W_le_of_positive_parameter_bound (optionChildData I b)
      hda hdb hq hardApproach tendsto_hardApproach
      (Filter.Eventually.of_forall hardApproach_pos)
      (Filter.Eventually.of_forall hardApproach_le_one)
      ham_nonneg ham_self ham_triangle ham_le_card hpos
  · exact hpos x hxpos hx1

theorem transfer_inputs_of_soft {Δ g : ℕ} {K : ℝ}
    (hq : Δ + 2 ≤ Fintype.card C) (hK : 0 ≤ K)
    (hsoft : SoftLargeGirthCoupling.{u, v} C Δ g K) :
    (largeGirthFamily.{u, v} C g).TransferCouplingInputs Δ (by omega) := by
  constructor
  · exact ⟨K, closed_root_coupling_of_soft hq hK hsoft PinningData.hardParameter (by norm_num)⟩
  · intro δ _ _
    exact ⟨K, fun x hx => closed_root_coupling_of_soft hq hK hsoft x hx.2⟩

/-- The completed family transfer from actual positive-activity CI to a
single graph-, size-, pinning-, and activity-independent complex radius. -/
theorem large_girth_zero_free_of_soft_ci {Δ g : ℕ} {K : ℝ}
    (hq : Δ + 2 ≤ Fintype.card C) (hK : 0 ≤ K)
    (hsoft : SoftLargeGirthCoupling.{u, v} C Δ g K) :
    ∃ eps > 0, ∀ {V : Type u} [Fintype V] (I : PinningData V C),
      (g : ℕ∞) ≤ I.graph.egirth → I.DegreeBound Δ →
      ∀ z ∈ thickening eps pottsInterval, pinningProductPartition I z ≠ 0 :=
  (largeGirthFamily.{u, v} C g).uniform_transfer_zero_free Δ (by omega)
    (transfer_inputs_of_soft hq hK hsoft)

end

end CI2ZF.Appendix.Girth
