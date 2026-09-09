import CI2ZF.Appendix.GirthMessages
import CI2ZF.Appendix.GirthSupportedOperator

/-! Single-site Potts weights and their exact factorization, including activity zero. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

namespace GraphHeatBath

def siteCount (I : PinningData V C) (σ : V → C) (v : V) (c : C) : ℕ :=
  I.boundaryCount v c + ((I.graph.neighborFinset v).filter (fun w => σ w = c)).card

def siteWeight (I : PinningData V C) (x : ℝ) (σ : V → C) (v : V) (c : C) : ℝ :=
  x ^ siteCount I σ v c

def sitePartition (I : PinningData V C) (x : ℝ) (σ : V → C) (v : V) : ℝ :=
  ∑ c, siteWeight I x σ v c

def backgroundWeight (I : PinningData V C) (x : ℝ) (σ : V → C) (v : V) : ℝ :=
  (∏ u ∈ Finset.univ.erase v, x ^ I.boundaryCount u (σ u)) *
    ∏ e ∈ I.graph.edgeFinset.filter (fun e => v ∉ e), PinningData.edgeFactor x σ e

theorem siteCount_sum (I : PinningData V C) (σ : V → C) (v : V) :
    ∑ c, siteCount I σ v c = I.constraintDegree v := by
  unfold siteCount PinningData.constraintDegree
  rw [Finset.sum_add_distrib]
  have h := Finset.sum_card_fiberwise_eq_card_filter (I.graph.neighborFinset v)
    (Finset.univ : Finset C) σ
  simp only [Finset.mem_univ, Finset.filter_true] at h
  rw [h, SimpleGraph.card_neighborFinset_eq_degree, Nat.add_comm]

theorem sitePartition_lower (I : PinningData V C) {x : ℝ} (hx : 0 ≤ x)
    (σ : V → C) (v : V) :
    (Fintype.card C : ℝ) - (1 - x) * I.constraintDegree v ≤ sitePartition I x σ v := by
  have h := palette_mass_lower hx (siteCount I σ v)
  simpa only [sitePartition, siteWeight, paletteWeight, ← Nat.cast_sum, siteCount_sum] using h

theorem sitePartition_pos (I : PinningData V C) {x : ℝ} (hx : 0 ≤ x) (_hx1 : x ≤ 1)
    {Δ : ℕ} (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C)
    (σ : V → C) (v : V) : 0 < sitePartition I x σ v := by
  have hb := sitePartition_lower I hx σ v
  have hv : (I.constraintDegree v : ℝ) ≤ Δ := by exact_mod_cast hd v
  have hq' : (Δ : ℝ) + 1 ≤ Fintype.card C := by exact_mod_cast hq
  have hn : (0 : ℝ) ≤ I.constraintDegree v := Nat.cast_nonneg _
  nlinarith

theorem siteCount_update_of_not_adj (I : PinningData V C) (σ : V → C) (v u : V)
    (hu : ¬ I.graph.Adj v u) (a c : C) :
    siteCount I (Function.update σ u a) v c = siteCount I σ v c := by
  unfold siteCount
  congr 2
  apply Finset.filter_congr
  intro w hw
  have hwu : w ≠ u := by
    intro h; subst w; exact hu (by simpa using hw)
  rw [Function.update_of_ne hwu]

theorem siteWeight_update_of_not_adj (I : PinningData V C) (x : ℝ) (σ : V → C) (v u : V)
    (hu : ¬ I.graph.Adj v u) (a c : C) :
    siteWeight I x (Function.update σ u a) v c = siteWeight I x σ v c := by
  rw [siteWeight, siteCount_update_of_not_adj I σ v u hu]
  rfl

theorem incident_product (I : PinningData V C) (x : ℝ) (σ : V → C) (v : V) :
    (∏ e ∈ I.graph.edgeFinset.filter (fun e => v ∈ e), PinningData.edgeFactor x σ e) =
      x ^ ((I.graph.neighborFinset v).filter (fun w => σ w = σ v)).card := by
  have heq : (∏ w ∈ I.graph.neighborFinset v, PinningData.edgeFactor x σ s(v,w)) =
      ∏ e ∈ I.graph.edgeFinset.filter (fun e => v ∈ e), PinningData.edgeFactor x σ e := by
    apply Finset.prod_bij (fun w _ => s(v,w))
    · intro w hw
      simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        Sym2.mem_iff, true_or, and_true]
      simpa using hw
    · intro a ha b hb hab
      exact Sym2.congr_right.mp hab
    · intro e he
      induction e using Sym2.ind with
      | _ a b =>
        rcases Finset.mem_filter.mp he with ⟨he,hv⟩
        have hab : I.graph.Adj a b := by simpa using he
        rcases Sym2.mem_iff.mp hv with rfl | rfl
        · exact ⟨b, (by simpa using hab), rfl⟩
        · exact ⟨a, (by simpa using hab.symm), Sym2.eq_swap⟩
    · intro w hw; rfl
  rw [← heq]
  simp only [PinningData.edgeFactor_mk]
  rw [show (fun w => if σ v = σ w then x else 1) =
    (fun w => if σ w = σ v then x else 1) by funext w; simp [eq_comm]]
  rw [← Finset.prod_filter]
  simp

theorem weight_factorization (I : PinningData V C) (x : ℝ) (σ : V → C) (v : V) :
    I.weight x σ = backgroundWeight I x σ v * siteWeight I x σ v (σ v) := by
  unfold PinningData.weight backgroundWeight siteWeight siteCount
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ v),
    ← Finset.prod_filter_mul_prod_filter_not I.graph.edgeFinset (fun e => v ∈ e),
    incident_product, pow_add]
  ring

theorem backgroundWeight_update (I : PinningData V C) (x : ℝ) (σ : V → C)
    (v : V) (c : C) :
    backgroundWeight I x (Function.update σ v c) v = backgroundWeight I x σ v := by
  unfold backgroundWeight
  congr 1
  · apply Finset.prod_congr rfl
    intro u hu
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hu)]
  · apply Finset.prod_congr rfl
    intro e he
    have hv := (Finset.mem_filter.mp he).2
    induction e using Sym2.ind with
    | _ a b =>
      have ha : a ≠ v := by intro h; subst a; exact hv (by simp)
      have hb : b ≠ v := by intro h; subst b; exact hv (by simp)
      simp only [PinningData.edgeFactor_mk, Function.update_of_ne ha, Function.update_of_ne hb]

theorem weight_swap (I : PinningData V C) (x : ℝ) (σ : V → C) (v : V) (c : C) :
    I.weight x (Function.update σ v c) * siteWeight I x σ v (σ v) =
      I.weight x σ * siteWeight I x σ v c := by
  rw [weight_factorization I x (Function.update σ v c) v,
    backgroundWeight_update, Function.update_self,
    siteWeight_update_of_not_adj I x σ v v I.graph.irrefl,
    weight_factorization I x σ v]
  ring

end GraphHeatBath
end
end CI2ZF.Appendix.Girth
