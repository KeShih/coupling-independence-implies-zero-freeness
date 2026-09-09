import CI2ZF.Potts.Transfer.InductionState
import CI2ZF.Potts.Transfer.OptionParentNonzero
import CI2ZF.Potts.Transfer.TransferLocalControls

/-! The actual positive and hard parent steps in the common induction
language. The positive step reads its boundary control from the uniform
local controls; the hard step uses the actual root anchor and weight
comparison proved in `OptionParentNonzero`. -/
namespace CI2ZF.Potts
open PottsCI Separator
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v

theorem option_root_boundaryCount_le {O : Type u} {C : Type v}
    [Fintype O] [Fintype C] (I : PinningData (Option O) C)
    {Delta : ℕ} (hd : I.DegreeBound Delta) (c : C) : I.boundaryCount none c ≤ Delta := by
  have hc := Finset.single_le_sum (s := Finset.univ)
    (f := fun b : C => I.boundaryCount none b)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  have hroot := hd none
  unfold PinningData.constraintDegree at hroot
  omega

theorem positive_parent_step_of_local_controls {O : Type u} {C : Type v}
    [Fintype O] [Fintype C] [Nonempty C] {Delta B : ℕ} {K : Set ℂ}
    {r alpha : ℝ} (hlocal : PositiveLocalControls.{u, v} C Delta B K r alpha)
    (ha : alpha ≤ (1 / 8 : ℝ)) {x : ℝ} (hx : 0 < x) (hxK : (x : ℂ) ∈ K)
    (I : PinningData (Option O) C) (hd : I.DegreeBound Delta)
    (hchildren : ∀ a : C, PartitionNonzeroOn (optionChildData I a) (x : ℂ) r)
    (hresponse : OptionRootResponses I (x : ℂ) r alpha) :
    PartitionNonzeroOn I (x : ℂ) r := by
  have hb (c : C) := hlocal.boundary (I.boundaryCount none c)
    (option_root_boundaryCount_le I hd c) (x : ℂ) hxK
  intro z hz
  apply option_positive_parent_nonzero_of_pairwise_child_logs I hx z ha
    (fun a => hchildren a z hz)
    (fun c => principalResponseLog (fun w : ℂ => w ^ I.boundaryCount none c) (x : ℂ) z)
  · exact fun c => (hb c).2.2.1 z hz
  · exact fun c => (hb c).2.2.2 z hz
  · intro a b
    obtain ⟨L, _, _, he, hnorm⟩ := hresponse a b
    exact ⟨L z, he z hz, hnorm z hz⟩

/-- A weak inequality at the radius gives the strict hard error budget
at every point of the open disk. No root anchor or weight estimate is
left as an input. -/
theorem hard_parent_step {O : Type u} {C : Type v}
    [Fintype O] [Fintype C] {Delta : ℕ} {r alpha : ℝ}
    (hq : Delta + 1 ≤ Fintype.card C) (ha : alpha ≤ (1 / 8 : ℝ))
    (hr : r ≤ 1)
    (hbudget : (4 / 3 : ℝ) * Fintype.card C * (Fintype.card C : ℝ) ^ Delta * r ≤ 1)
    (I : PinningData (Option O) C) (hd : I.DegreeBound Delta)
    (hchildren : ∀ a : C, PartitionNonzeroOn (optionChildData I a) 0 r)
    (hresponse : OptionRootResponses I 0 r alpha) : PartitionNonzeroOn I 0 r := by
  have hqpos : 0 < (Fintype.card C : ℝ) := by
    exact_mod_cast (Nat.succ_pos Delta).trans_le hq
  have hfactor : 0 < (4 / 3 : ℝ) * Fintype.card C * (Fintype.card C : ℝ) ^ Delta := by
    positivity
  intro z hz
  have hzr : ‖z‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  apply option_hard_parent_nonzero_of_pairwise_child_logs I hd hq z ha
    (fun a => hchildren a z hz) _ (hzr.le.trans hr)
    ((mul_lt_mul_of_pos_left hzr hfactor).trans_le hbudget)
  intro a b
  obtain ⟨L, _, _, he, hnorm⟩ := hresponse a b
  exact ⟨L z, he z hz, hnorm z hz⟩

end
end CI2ZF.Potts
