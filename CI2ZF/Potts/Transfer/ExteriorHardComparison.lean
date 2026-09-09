import CI2ZF.Potts.Transfer.ExteriorRepinning
import CI2ZF.Potts.Transfer.HardCountComparison
import CI2ZF.Coupling.Foundations.HammingResponses

/-! Actual hard exterior weights under shell recolouring. Only the
neighbours of the changed shell vertex are recoloured in the counting
injection, and there are at most Delta such vertices. -/
namespace CI2ZF.Potts
open PottsCI
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {O C : Type*} [Fintype O] [Fintype C]

theorem optionChildData_zero_comparison (I : PinningData (Option O) C)
    {Δ : ℕ} (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C) (d e : C) :
    (optionChildData I d).partition 0 ≤
      (Fintype.card C : ℝ) ^ Δ * (optionChildData I e).partition 0 := by
  let : Nonempty C := ⟨e⟩
  have hb : ∀ o, o ∉ optionRootNeighbours I → ∀ c,
      (optionChildData I d).boundaryCount o c = (optionChildData I e).boundaryCount o c := by
    intro o ho c
    have hn : ¬ I.graph.Adj none (some o) := by simpa [optionRootNeighbours] using ho
    simp only [optionChildData_count, hn, false_and, if_false, add_zero]
  have hc := partition_zero_comparison (optionChildData I d) (optionChildData I e)
    (optionRootNeighbours I) rfl hb (optionChildData_degreeBound I hd e) hq
  apply hc.trans
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by exact_mod_cast Fintype.card_pos (α := C))
      (optionRootNeighbours_card_le I hd)) ((optionChildData I e).partition_nonneg le_rfl)

namespace Separator
variable {U S : Type*} [Fintype U] [Fintype S]

/-- Every shell colouring has a positive actual exterior hard weight,
including shell colourings defective on the inside. -/
theorem exteriorPartition_zero_pos (I : PinningData (Vertex U S O) C)
    (hsep : Separates I) {Δ : ℕ} (hd : I.DegreeBound Δ)
    (hq : Δ + 1 ≤ Fintype.card C) (ξ : S → C) :
    0 < exteriorPartition I (0 : ℝ) ξ := by
  let : Nonempty C := Fintype.card_pos_iff.mp (lt_of_lt_of_le (Nat.succ_pos Δ) hq)
  rw [exteriorPartition_eq_real_partition I hsep]
  exact partition_zero_pos_of_succ_le (exteriorData I ξ) (exteriorData_degreeBound I hsep hd ξ) hq

/-- Changing one actual shell coordinate satisfies the uniform hard
comparison, via the two genuine children of its temporarily unpinned data. -/
theorem exteriorPartition_zero_update_le (I : PinningData (Vertex U S O) C)
    (hsep : Separates I) {Δ : ℕ} (hd : I.DegreeBound Δ)
    (hq : Δ + 1 ≤ Fintype.card C) (ξ : S → C) (s : S) (a : C) :
    exteriorPartition I (0 : ℝ) (Function.update ξ s a) ≤
      (Fintype.card C : ℝ) ^ Δ * exteriorPartition I (0 : ℝ) ξ := by
  have hc := optionChildData_zero_comparison (unpinnedExteriorData I ξ s)
    (unpinnedExterior_degreeBound I hd ξ s) hq a (ξ s)
  simp only [optionChildData_unpinnedExterior, Function.update_eq_self] at hc
  simpa only [exteriorPartition_eq_real_partition I hsep] using hc

/-- All hard shell weights are uniformly comparable by an actual
coordinate-by-coordinate recolouring path. -/
theorem exteriorPartition_zero_le_anchor (I : PinningData (Vertex U S O) C)
    (hsep : Separates I) {Δ : ℕ} (hd : I.DegreeBound Δ)
    (hq : Δ + 1 ≤ Fintype.card C) (ξ anchor : S → C) :
    exteriorPartition I (0 : ℝ) ξ ≤
      ((Fintype.card C : ℝ) ^ Δ) ^ Fintype.card S * exteriorPartition I (0 : ℝ) anchor := by
  have hqpos : (1 : ℝ) ≤ Fintype.card C := by exact_mod_cast lt_of_lt_of_le (Nat.succ_pos Δ) hq
  have hH : (1 : ℝ) ≤ (Fintype.card C : ℝ) ^ Δ := one_le_pow₀ hqpos
  exact le_pow_card_mul_of_coordinates (exteriorPartition I (0 : ℝ)) hH
    (fun ξ => (exteriorPartition_zero_pos I hsep hd hq ξ).le)
    (exteriorPartition_zero_update_le I hsep hd hq) ξ anchor

end Separator
end
end CI2ZF.Potts
