import CI2ZF.Coupling.Girth.Covariance.Doob.Conditioning

/-! Sequential revelation of genuine conditional laws, with exact variance
increments and a transformed-response bound on the full revealed source. -/
namespace CI2ZF.Appendix.Girth.Doob
open scoped BigOperators
open PottsCI Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {Ω C : Type*} [Fintype Ω] [Fintype C] [DecidableEq C]

def revealMean : List (Ω → C) → FinDist Ω → (Ω → ℝ) → Ω → ℝ
  | [], μ, f, _ => expectReal μ f
  | k :: ks, μ, f, ω => revealMean ks (given μ k (k ω)) f ω

theorem revealMean_expectation (ks : List (Ω → C)) (μ : FinDist Ω) (f : Ω → ℝ) :
    expectReal μ (revealMean ks μ f) = expectReal μ f := by
  induction ks generalizing μ with
  | nil => exact expectReal_const _ _
  | cons k ks ih =>
    change expectReal μ (fun ω => revealMean ks (given μ k (k ω)) f ω) = _
    rw [family_expectation μ k (fun c => revealMean ks (given μ k c) f)]
    simp_rw [ih]
    exact (expectation_disintegration μ k f).symm

theorem revealMean_variance_step (k : Ω → C) (ks : List (Ω → C)) (μ : FinDist Ω) (f : Ω → ℝ) :
    variance μ (revealMean (k :: ks) μ f) =
      expectReal (observed μ k) (fun c => variance (given μ k c) (revealMean ks (given μ k c) f)) +
      variance (observed μ k) (observedMean μ k f) := by
  change variance μ (fun ω => revealMean ks (given μ k (k ω)) f ω) = _
  rw [family_variance μ k (fun c => revealMean ks (given μ k c) f)]
  simp only [revealMean_expectation]
  rfl

/-- At each node of the actual revelation tree, the score bound is only
needed on positive-probability branches. -/
def BoundedScores (s K : ℝ) (f : Ω → ℝ) : List ((Ω → C) × ℝ) → FinDist Ω → Prop
  | [], _ => True
  | (k,a) :: ks, μ =>
      (∀ c, 1 - s * (coordinateMarginal μ k).w c ≠ 0) ∧
      (∑ c, responseScore s μ k f c ^ 2) ≤ K * a ^ 2 ∧
      ∀ c, 0 < (observed μ k).w c → BoundedScores s K f ks (given μ k c)

def squareBudget (ks : List ((Ω → C) × ℝ)) : ℝ := (ks.map (fun z => z.2 ^ 2)).sum

/-- Finite Doob bound for the full conditional source, obtained from
actual score bounds in successively conditioned laws. -/
theorem variance_reveal_le (ks : List ((Ω → C) × ℝ)) (μ : FinDist Ω) (f : Ω → ℝ)
    {s K : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hscore : BoundedScores s K f ks μ) :
    variance μ (revealMean (ks.map Prod.fst) μ f) ≤ K * squareBudget ks := by
  induction ks generalizing μ with
  | nil => simp [revealMean, squareBudget, variance, expectReal_const]
  | cons z ks ih =>
    obtain ⟨k,a⟩ := z
    rcases hscore with ⟨hden,hbound,hrest⟩
    simp only [List.map_cons] at *
    rw [revealMean_variance_step]
    have hfirst := (observed_variance_le_score s μ k f hs hs1 hden).trans hbound
    have ht : expectReal (observed μ k) (fun c =>
        variance (given μ k c) (revealMean (ks.map Prod.fst) (given μ k c) f)) ≤
        K * squareBudget ks := by
      calc
        _ ≤ expectReal (observed μ k) (fun _ => K * squareBudget ks) := by
          apply Finset.sum_le_sum
          intro c _
          by_cases hc : 0 < (observed μ k).w c
          · exact mul_le_mul_of_nonneg_left (ih (given μ k c) (hrest c hc)) ((observed μ k).nonneg c)
          · have hz : (observed μ k).w c = 0 :=
              le_antisymm (le_of_not_gt hc) ((observed μ k).nonneg c)
            simp only [hz, zero_mul, le_refl]
        _ = _ := expectReal_const _ _
    have hb : squareBudget ((k,a) :: ks) = a ^ 2 + squareBudget ks := by
      simp [squareBudget]
    rw [hb]
    nlinarith

end
end CI2ZF.Appendix.Girth.Doob
