import CI2ZF.LeeYang.Analytic
import CI2ZF.LeeYang.ModelRoot
import CI2ZF.Potts.Transfer.OptionParentNonzero

/-! The hard field parent cannot vanish: every allowed root colour
contributes a term with positive real part after one common normalization. -/

namespace CI2ZF.LeeYang
open PottsCI CI2ZF.Potts
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

theorem field_mul_exp_re_pos (ℓ L : ℂ)
    (hfield : ‖ℓ - 1‖ < (1 / 2 : ℝ)) (hlog : ‖L‖ ≤ (1 / 4 : ℝ)) :
    0 < (ℓ * Complex.exp L).re := by
  have he := CI2ZF.norm_exp_sub_one_le_third L hlog
  have hn : ‖Complex.exp L‖ ≤ (4 / 3 : ℝ) := by
    calc
      ‖Complex.exp L‖ = ‖(Complex.exp L - 1) + 1‖ := by congr 1; ring
      _ ≤ ‖Complex.exp L - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 4 / 3 := by norm_num at *; linarith
  have hdist : ‖ℓ * Complex.exp L - 1‖ < 1 := by
    calc
      ‖ℓ * Complex.exp L - 1‖ =
          ‖(ℓ - 1) * Complex.exp L + (Complex.exp L - 1)‖ := by congr 1; ring
      _ ≤ ‖ℓ - 1‖ * ‖Complex.exp L‖ + ‖Complex.exp L - 1‖ := by
        simpa only [norm_mul] using norm_add_le ((ℓ - 1) * Complex.exp L) (Complex.exp L - 1)
      _ ≤ ‖ℓ - 1‖ * (4 / 3) + 1 / 3 :=
        add_le_add (mul_le_mul_of_nonneg_left hn (norm_nonneg _)) he
      _ < 1 := by nlinarith
  have hre := Complex.re_le_norm (1 - ℓ * Complex.exp L)
  rw [norm_sub_rev] at hre
  simp only [Complex.sub_re, Complex.one_re] at hre
  linarith

variable {O C : Type*} [Fintype O] [Fintype C] [Nonempty C]

theorem option_field_nonzero_of_child_logs (I : PinningData (Option O) C)
    {Δ : ℕ} (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C)
    (ℓ : Option O → C → ℂ)
    (hfield : ∀ c, ‖ℓ none c - 1‖ < (1 / 2 : ℝ))
    (hchild : ∀ c, fieldPartition (optionChildData I c) (fun o => ℓ (some o)) ≠ 0)
    (hlogs : ∀ a b : C, ∃ L : ℂ,
      Complex.exp L =
        (fieldPartition (optionChildData I a) (fun o => ℓ (some o)) /
          fieldPartition (optionChildData I a) oneField) /
        (fieldPartition (optionChildData I b) (fun o => ℓ (some o)) /
          fieldPartition (optionChildData I b) oneField) ∧ ‖L‖ ≤ (1 / 4 : ℝ)) :
    fieldPartition I ℓ ≠ 0 := by
  obtain ⟨anchor, hanchor⟩ := option_exists_zero_root_boundary I hd hq
  choose L hexp hnorm using fun c => hlogs c anchor
  let Z (c : C) : ℝ := (optionChildData I c).partition 0
  have hZ (c : C) : 0 < Z c :=
    partition_zero_pos_of_succ_le _ (optionChildData_degreeBound I hd c) hq
  have hZne (c : C) : (Z c : ℂ) ≠ 0 := by exact_mod_cast (hZ c).ne'
  dsimp [Z] at hZne
  let A := fieldPartition (optionChildData I anchor) (fun o => ℓ (some o)) / (Z anchor : ℂ)
  have hA : A ≠ 0 := div_ne_zero (hchild anchor) (hZne anchor)
  have hr (c : C) : fieldPartition (optionChildData I c) (fun o => ℓ (some o)) =
      A * ((Z c : ℂ) * Complex.exp (L c)) := by
    rw [hexp c]
    simp only [fieldPartition_one]
    dsimp [A, Z]
    field_simp [(hZne c), (hZne anchor), hchild anchor]
  let S := Finset.univ.filter (fun c => I.boundaryCount none c = 0)
  let Q : ℂ := ∑ c ∈ S, (Z c : ℂ) * (ℓ none c * Complex.exp (L c))
  have hQre : 0 < Q.re := by
    dsimp [Q]
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    apply Finset.sum_pos
    · intro c _
      exact mul_pos (hZ c) (field_mul_exp_re_pos _ _ (hfield c) (hnorm c))
    · exact ⟨anchor, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hanchor⟩⟩
  have hQ : Q ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hQre
    exact (lt_irrefl 0) hQre
  have he : fieldPartition I ℓ = A * Q := by
    rw [option_parent_fieldPartition_allowed]
    dsimp [Q, S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [hr c]
    ring
  rw [he]
  exact mul_ne_zero hA hQ

theorem curveNonzeroOn_of_child_responses (I : PinningData (Option O) C)
    {Δ : ℕ} (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C)
    (d : Option O → C → ℂ) (hdir : DirectionBound d)
    {r α : ℝ} (hr : r ≤ 1 / 2) (hα : α ≤ 1 / 16)
    (hchild : ∀ c, CurveNonzeroOn (optionChildData I c) (fieldPull some d) r)
    (hresponse : CurveRootResponses I d r α) : CurveNonzeroOn I d r := by
  intro z hz
  have hz' : ‖z‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hz
  apply option_field_nonzero_of_child_logs I hd hq (fieldLine d z)
  · intro c
    exact (fieldLine_dist_one_le hdir z none c).trans_lt (hz'.trans_le hr)
  · intro c
    exact hchild c z hz
  · intro a b
    obtain ⟨L, _, _, he, hL⟩ := hresponse a b
    refine ⟨L z, ?_, (hL z hz).trans (by linarith)⟩
    convert he z hz using 1
    simp only [fieldCurve, fieldLine_zero]
    congr 3

end
end CI2ZF.LeeYang
