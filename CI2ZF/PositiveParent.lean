import CI2ZF.PottsModel
import CI2ZF.ComplexAverage

/-! The positive-base parent recursion cannot cancel when the boundary
and child-response logarithms fit the local budget. -/
namespace CI2ZF
open PottsCI
open scoped BigOperators
noncomputable section

theorem positive_weighted_exponentials_ne_zero {S : Type*} [Fintype S] [Nonempty S]
    (w : S → ℝ) (hw : ∀ s, 0 < w s) (L : S → ℂ)
    (hL : ∀ s, ‖L s‖ ≤ (1 / 4 : ℝ)) :
    (∑ s : S, (w s : ℂ) * Complex.exp (L s)) ≠ 0 := by
  have hre (s : S) : 0 < (Complex.exp (L s)).re := by
    have hn := norm_exp_sub_one_le_third (L s) (hL s)
    have hb := Complex.re_le_norm (1 - Complex.exp (L s))
    rw [norm_sub_rev] at hb
    simp only [Complex.sub_re, Complex.one_re] at hb
    linarith
  have hsum : 0 < (∑ s : S, (w s : ℂ) * Complex.exp (L s)).re := by
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact Finset.sum_pos (fun s _ => mul_pos (hw s) (hre s)) Finset.univ_nonempty
  intro hz
  rw [hz, Complex.zero_re] at hsum
  exact (lt_irrefl _ hsum)

theorem weighted_response_sum_ne_zero {S : Type*} [Fintype S] [Nonempty S]
    (w : S → ℝ) (hw : ∀ s, 0 < w s) (R : S → ℂ) (A : ℂ) (hA : A ≠ 0)
    (L : S → ℂ) (hexp : ∀ s, Complex.exp (L s) = R s / A)
    (hL : ∀ s, ‖L s‖ ≤ (1 / 4 : ℝ)) :
    (∑ s : S, (w s : ℂ) * R s) ≠ 0 := by
  have heq : (∑ s : S, (w s : ℂ) * R s) =
      A * ∑ s : S, (w s : ℂ) * Complex.exp (L s) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [hexp s]
    field_simp
  rw [heq]
  exact mul_ne_zero hA (positive_weighted_exponentials_ne_zero w hw L hL)

namespace Potts
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [Fintype C] [Nonempty C]

/-- The nonvanishing step in the actual Potts positive-base induction.
Its inputs are child and boundary logarithms, rather than the desired
nonvanishing of the parent. No degree restriction is needed for this step. -/
theorem positive_parent_nonzero_of_child_logs
    (tau : PartialColouring V C) (G : SimpleGraph V) (v : tau.FreeVertex)
    (a₀ : C) {x : ℝ} (hx : 0 < x) (z : ℂ)
    (ha₀ : normalizedPartition (pinVertex tau v a₀) G z ≠ 0)
    (g L : C → ℂ)
    (hg : ∀ c, Complex.exp (g c) = z ^ tau.boundaryCount G v c /
      (x : ℂ) ^ tau.boundaryCount G v c)
    (hL : ∀ c, Complex.exp (L c) =
      (normalizedPartition (pinVertex tau v c) G z /
        normalizedPartition (pinVertex tau v c) G (x : ℂ)) /
      (normalizedPartition (pinVertex tau v a₀) G z /
        normalizedPartition (pinVertex tau v a₀) G (x : ℂ)))
    (hbound : ∀ c, ‖g c + L c‖ ≤ (1 / 4 : ℝ)) :
    normalizedPartition tau G z ≠ 0 := by
  let Z (c : C) : ℝ := ((pinVertex tau v c).toPinningData G).partition x
  have hZ (c : C) : 0 < Z c := PinningData.partition_pos_of_parameter_pos _ hx
  have hbase (c : C) : normalizedPartition (pinVertex tau v c) G (x : ℂ) = (Z c : ℂ) :=
    normalizedPartition_ofReal _ _ _
  have hZne (c : C) : (Z c : ℂ) ≠ 0 := by exact_mod_cast (hZ c).ne'
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  let A := normalizedPartition (pinVertex tau v a₀) G z / (Z a₀ : ℂ)
  let R (c : C) := (z ^ tau.boundaryCount G v c / (x : ℂ) ^ tau.boundaryCount G v c) *
    (normalizedPartition (pinVertex tau v c) G z / (Z c : ℂ))
  let w (c : C) : ℝ := x ^ tau.boundaryCount G v c * Z c
  have hexp (c : C) : Complex.exp (g c + L c) = R c / A := by
    rw [Complex.exp_add, hg c, hL c, hbase c, hbase a₀]
    dsimp [R, A]
    ring
  have hn := weighted_response_sum_ne_zero w (fun c => mul_pos (pow_pos hx _) (hZ c)) R A
    (div_ne_zero ha₀ (hZne a₀)) (fun c => g c + L c) hexp hbound
  rw [normalizedPartition_pinVertex_recursion tau G v z]
  convert hn using 1
  apply Finset.sum_congr rfl
  intro c _
  dsimp [w, R]
  push_cast
  field_simp [hZne c]

end Potts
end
end CI2ZF
