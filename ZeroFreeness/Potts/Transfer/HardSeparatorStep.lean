import ZeroFreeness.Potts.Transfer.SeparatorHardAnchor
import ZeroFreeness.Potts.Transfer.SeparatorHardResponse

/-! The hard separator nonvanishing step, with the feasible anchor,
hard-weight comparisons and local defects all derived from the actual graph. -/
namespace ZeroFreeness.Potts.Separator
open PottsCI
attribute [local instance] Classical.propDecidable
noncomputable section
variable {U S O C : Type*} [Fintype U] [Fintype S] [Fintype O] [Fintype C]

/-- Only the exterior response identities and their one-coordinate bound
remain as inductive inputs. The quantitative defect and witness hypotheses
of the analytic perturbation lemma have been discharged. -/
theorem hard_separator_nonzero_of_exterior_responses
    (I : PinningData (Vertex U S O) C) (hsep : Separates I)
    {Δ : ℕ} (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C)
    {N s : ℕ} (hinside : Fintype.card U ≤ N) (hshell : Fintype.card S ≤ s)
    (z : ℂ) (hz : ‖z‖ ≤ 1) (h : (S → C) → ℂ) {alpha : ℝ} (ha : 0 ≤ alpha)
    (hexp : ∀ ξ, Complex.exp (h ξ) =
      exteriorPartition I z ξ / exteriorPartition I (0 : ℂ) ξ)
    (hresponse : ∀ ξ u c, ‖h (Function.update ξ u c) - h ξ‖ ≤ alpha)
    (hphase : alpha * s ≤ (1 / 4 : ℝ))
    (hsmall : (3 / 2 : ℝ) *
      ((Fintype.card C : ℝ) ^ (N + s) * ((Fintype.card C : ℝ) ^ Δ) ^ s *
        Real.exp (alpha * s)) * ‖z‖ ≤ 1 / 2) :
    partition I z ≠ 0 := by
  let : Nonempty C := Fintype.card_pos_iff.mp (lt_of_lt_of_le (Nat.succ_pos Δ) hq)
  obtain ⟨anchor, _, _, herr⟩ := exists_actual_hard_separator_error_bound
    I hsep hd hq hinside hshell z hz h ha hresponse
  have ho (ξ : S → C) : ‖h ξ - h anchor‖ ≤ (1 / 4 : ℝ) := by
    apply (norm_sub_le_card_of_coordinates h ha hresponse ξ anchor).trans
    apply le_trans _ hphase
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hshell) ha
  have hK : 0 ≤ (Fintype.card C : ℝ) ^ (N + s) *
      ((Fintype.card C : ℝ) ^ Δ) ^ s * Real.exp (alpha * s) := by positivity
  exact partition_ne_zero_of_hard_main_error I hsep
    (partition_zero_pos_of_succ_le I hd hq)
    (exteriorPartition_zero_pos I hsep hd hq) z h anchor hexp ho hK (norm_nonneg z) herr hsmall

end
end ZeroFreeness.Potts.Separator
