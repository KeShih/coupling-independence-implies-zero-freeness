import ZeroFreeness.Potts.Geometry.SeparatorRelabel
import ZeroFreeness.Coupling.Foundations.CommonCoins

/-! Vertex reindexing transports the actual Gibbs law and each of its
deterministic marginals. The proof uses the finite Potts weights and
partitions, and remains valid at the hard endpoint. -/
namespace ZeroFreeness.Potts.Separator
open PottsCI PottsCI.FinDist
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
section Generic
variable {V W C : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype C] [DecidableEq C]

lemma real_weight_eq_product (I : PinningData V C) (x : ℝ) (σ : V → C) :
    I.weight x σ = pinningProductWeight I x σ := by
  unfold PinningData.weight pinningProductWeight
  apply congrArg₂ (· * ·)
  · rfl
  · apply Finset.prod_congr (by ext e; simp only [SimpleGraph.mem_edgeFinset])
    intro e _
    induction e using Sym2.ind with
    | _ u v =>
      rw [PinningData.edgeFactor_mk, edgeWeight_mk]
      split_ifs <;> rfl

lemma real_partition_eq_product (I : PinningData V C) (x : ℝ) :
    I.partition x = pinningProductPartition I x := by
  unfold PinningData.partition pinningProductPartition
  apply Finset.sum_congr (by ext σ; simp)
  intro σ _
  exact real_weight_eq_product I x σ

theorem weight_relabel (I : PinningData V C) (e : V ≃ W) (x : ℝ) (τ : W → C) :
    (relabelData I e).weight x τ = I.weight x ((relabelColouring e).symm τ) := by
  rw [real_weight_eq_product, real_weight_eq_product]
  exact pinningProductWeight_relabel I e x τ

theorem partition_relabel (I : PinningData V C) (e : V ≃ W) (x : ℝ) :
    (relabelData I e).partition x = I.partition x := by
  rw [real_partition_eq_product, real_partition_eq_product]
  exact pinningProductPartition_relabel I e x

theorem partition_relabel_pos (I : PinningData V C) (e : V ≃ W) (x : ℝ)
    (hZ : 0 < I.partition x) : 0 < (relabelData I e).partition x := by
  rw [partition_relabel]
  exact hZ

/-- Equality of the genuine finite laws, not just equality of partition
functions or of their supports. The two positivity proofs are irrelevant. -/
theorem gibbs_relabel (I : PinningData V C) (e : V ≃ W) (x : ℝ) (hx : 0 ≤ x)
    (hZ : 0 < I.partition x) (hZ' : 0 < (relabelData I e).partition x) :
    (relabelData I e).gibbs x hx hZ' =
      mapLaw (I.gibbs x hx hZ) (relabelColouring (C := C) e) := by
  apply FinDist.ext
  funext τ
  rw [mapLaw_equiv_w]
  change (relabelData I e).weight x τ / (relabelData I e).partition x =
    I.weight x ((relabelColouring e).symm τ) / I.partition x
  rw [weight_relabel, partition_relabel]

/-- A deterministic observable commutes with the relabelled Gibbs law. -/
theorem map_gibbs_relabel {T : Type*} [Fintype T]
    (I : PinningData V C) (e : V ≃ W) (x : ℝ) (hx : 0 ≤ x)
    (hZ : 0 < I.partition x) (hZ' : 0 < (relabelData I e).partition x)
    (p : (W → C) → T) :
    mapLaw ((relabelData I e).gibbs x hx hZ') p =
      mapLaw (I.gibbs x hx hZ) (fun σ => p (relabelColouring e σ)) := by
  rw [gibbs_relabel I e x hx hZ hZ', mapLaw_comp]

/-- The coordinate marginal on any selected relabelled vertices is the
original marginal on their actual inverse images. -/
theorem coordinate_marginal_gibbs_relabel {A : Type*} [Fintype A]
    (I : PinningData V C) (e : V ≃ W) (x : ℝ) (hx : 0 ≤ x)
    (hZ : 0 < I.partition x) (hZ' : 0 < (relabelData I e).partition x)
    (j : A → W) :
    mapLaw ((relabelData I e).gibbs x hx hZ') (fun τ a => τ (j a)) =
      mapLaw (I.gibbs x hx hZ) (fun σ a => σ (e.symm (j a))) := by
  exact map_gibbs_relabel I e x hx hZ hZ' (fun τ a => τ (j a))

end Generic
variable {V C : Type*} [Fintype V] [Fintype C]

/-- In particular, the shell law in a three-part separator is the actual
coordinate marginal of the original Gibbs law. -/
theorem shellMarginal_relabel {U S O : Type*} [Fintype U] [Fintype S] [Fintype O]
    (I : PinningData V C) (e : V ≃ Vertex U S O) (x : ℝ) (hx : 0 ≤ x)
    (hZ : 0 < I.partition x) (hZ' : 0 < (relabelData I e).partition x) :
    shellMarginal (relabelData I e) x hx hZ' =
      mapLaw (I.gibbs x hx hZ) (fun σ s => σ (e.symm (Sum.inr (Sum.inl s)))) := by
  exact coordinate_marginal_gibbs_relabel I e x hx hZ hZ' (fun s => Sum.inr (Sum.inl s))

end
end ZeroFreeness.Potts.Separator
