import ZeroFreeness.Potts.Transfer.ExteriorHardComparison
import ZeroFreeness.Potts.Transfer.SeparatorInsidePolynomial
import ZeroFreeness.Potts.Transfer.HardEndpointRelativeError

/-! A hard-feasible full colouring supplies the anchor needed by the
separator error estimate. Both the inside multiplicity and exterior weight
refer to the actual factorization, including all defective shell terms. -/
namespace ZeroFreeness.Potts.Separator
open PottsCI
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {U S O C : Type*} [Fintype U] [Fintype S] [Fintype O] [Fintype C]

theorem insidePartition_zero_nonneg (I : PinningData (Vertex U S O) C) (ξ : S → C) :
    0 ≤ insidePartition I (0 : ℝ) ξ := by
  rw [insidePartition_eq_sum_pow]
  exact Finset.sum_nonneg (fun _ _ => pow_nonneg le_rfl _)

/-- The shell restriction of a genuine hard colouring has at least one
inside extension, and its exterior weight is dominated by the parent. -/
theorem exists_hard_shell_anchor (I : PinningData (Vertex U S O) C)
    (hsep : Separates I) {Δ : ℕ} (hd : I.DegreeBound Δ)
    (hq : Δ + 1 ≤ Fintype.card C) :
    ∃ anchor : S → C, 1 ≤ insidePartition I (0 : ℝ) anchor ∧
      exteriorPartition I (0 : ℝ) anchor ≤ I.partition 0 := by
  let : Nonempty C := Fintype.card_pos_iff.mp (lt_of_lt_of_le (Nat.succ_pos Δ) hq)
  obtain ⟨σ, hσ⟩ := exists_hardAdmissible_of_succ_le I hd hq
  let α : U → C := fun u => σ (Sum.inl u)
  let ξ : S → C := shell σ
  let ζ : O → C := fun o => σ (Sum.inr (Sum.inr o))
  have hj : join α ξ ζ = σ := by
    funext v
    rcases v with u | s | o <;> rfl
  have hweight : weight I (0 : ℝ) (join α ξ ζ) = 1 := by
    rw [hj, weight_real, PinningData.weight_zero_eq, if_pos hσ]
  rw [weight_join I hsep] at hweight
  have hn : insideWeight I (0 : ℝ) α ξ ≠ 0 := by
    intro he
    rw [he, zero_mul] at hweight
    exact zero_ne_one hweight
  have hone : insideWeight I (0 : ℝ) α ξ = 1 := by
    rw [insideWeight_eq_pow] at hn ⊢
    cases he : insideExponent I α ξ with
    | zero => simp
    | succ k => simp [he] at hn
  have hD : 1 ≤ insidePartition I (0 : ℝ) ξ := by
    rw [← hone, insidePartition]
    have hi := Finset.single_le_sum (s := Finset.univ)
      (f := fun β : U → C => insideWeight I (0 : ℝ) β ξ)
      (fun β _ => by rw [insideWeight_eq_pow]; exact pow_nonneg le_rfl _)
      (Finset.mem_univ α)
    convert hi using 1
  refine ⟨ξ, hD, ?_⟩
  have hE := (exteriorPartition_zero_pos I hsep hd hq ξ).le
  have hterm : exteriorPartition I (0 : ℝ) ξ ≤
      insidePartition I (0 : ℝ) ξ * exteriorPartition I (0 : ℝ) ξ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hD hE
  apply hterm.trans
  rw [real_partition_factorization I hsep]
  exact Finset.single_le_sum
    (fun η _ => mul_nonneg (insidePartition_zero_nonneg I η)
      (exteriorPartition_zero_pos I hsep hd hq η).le) (Finset.mem_univ ξ)

/-- The separator's actual defect sum has a uniform relative bound.
All shell weight comparisons and the hard-feasible anchor are proved from
the graph; the only response input is the one-coordinate inductive bound. -/
theorem exists_actual_hard_separator_error_bound
    (I : PinningData (Vertex U S O) C) (hsep : Separates I)
    {Δ : ℕ} (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C)
    {N s : ℕ} (hinside : Fintype.card U ≤ N) (hshell : Fintype.card S ≤ s)
    (z : ℂ) (hz : ‖z‖ ≤ 1) (h : (S → C) → ℂ) {alpha : ℝ} (ha : 0 ≤ alpha)
    (hresponse : ∀ ξ u c, ‖h (Function.update ξ u c) - h ξ‖ ≤ alpha) :
    ∃ anchor : S → C, 1 ≤ insidePartition I (0 : ℝ) anchor ∧
      exteriorPartition I (0 : ℝ) anchor ≤ I.partition 0 ∧
      ‖hardEndpointError (insidePartition I z) (insidePartition I (0 : ℂ))
          (exteriorPartition I (0 : ℝ)) h (I.partition 0)‖ ≤
        (Fintype.card C : ℝ) ^ (N + s) * ((Fintype.card C : ℝ) ^ Δ) ^ s *
          Real.exp (alpha * s) * ‖z‖ * ‖Complex.exp (h anchor)‖ := by
  let : Nonempty C := Fintype.card_pos_iff.mp (lt_of_lt_of_le (Nat.succ_pos Δ) hq)
  obtain ⟨anchor, hD, hparent⟩ := exists_hard_shell_anchor I hsep hd hq
  refine ⟨anchor, hD, hparent, ?_⟩
  have hZ := partition_zero_pos_of_succ_le I hd hq
  have hqpos : (1 : ℝ) ≤ Fintype.card C := by exact_mod_cast Fintype.card_pos (α := C)
  have hH : (1 : ℝ) ≤ (Fintype.card C : ℝ) ^ Δ := one_le_pow₀ hqpos
  have hi : Fintype.card (U → C) ≤ (Fintype.card C) ^ N := by
    rw [Fintype.card_fun]
    exact Nat.pow_le_pow_right (Fintype.card_pos (α := C)) hinside
  have he := bounded_monomial_hardEndpointError_norm_le
    (fun (ξ : S → C) (α : U → C) => insideExponent I α ξ) z hz
    (exteriorPartition I (0 : ℝ)) h anchor hZ hH ha hi hshell
    (fun ξ => (exteriorPartition_zero_pos I hsep hd hq ξ).le) hparent
    (exteriorPartition_zero_update_le I hsep hd hq) hresponse
  simpa only [← insidePartition_eq_sum_pow] using he

end
end ZeroFreeness.Potts.Separator
