import CI2ZF.Coupling.Girth.Covariance.Doob.Reveal

/-! Identification of sequential revelation with the conditional expectation
given the entire revealed configuration, including null fibres. -/
namespace CI2ZF.Appendix.Girth.Doob
open scoped BigOperators
open PottsCI Finset Edge.FiniteLaw
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {Ω C : Type*} [Fintype Ω] [Fintype C] [DecidableEq C]

theorem eventMass_pos_of_atom (μ : FinDist Ω) (P : Ω → Prop) (σ : Ω)
    (hσ : 0 < μ.w σ) (hP : P σ) : 0 < eventMass μ P := by
  have h := eventWeight_le_mass μ P σ
  rw [if_pos hP] at h
  exact hσ.trans_le h

theorem conditional_true (μ : FinDist Ω) : conditional μ (fun _ => True) = μ := by
  have hm : eventMass μ (fun _ => True) = 1 := by simp [eventMass, μ.sum_one]
  apply FinDist.ext
  funext σ
  rw [conditional_w _ _ (by rw [hm]; norm_num), hm]
  simp

theorem eventMass_conditional_intersection (μ : FinDist Ω) (P Q : Ω → Prop)
    (hp : 0 < eventMass μ P) :
    eventMass (conditional μ P) Q = eventMass μ (fun σ => P σ ∧ Q σ) / eventMass μ P := by
  unfold eventMass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  rw [conditional_w μ P hp]
  by_cases hP : P σ <;> by_cases hQ : Q σ <;> simp [hP, hQ]
  rfl

theorem conditional_intersection (μ : FinDist Ω) (P Q : Ω → Prop)
    (hp : 0 < eventMass μ P) (hpq : 0 < eventMass μ (fun σ => P σ ∧ Q σ)) :
    conditional (conditional μ P) Q = conditional μ (fun σ => P σ ∧ Q σ) := by
  have hm := eventMass_conditional_intersection μ P Q hp
  have hq : 0 < eventMass (conditional μ P) Q := by rw [hm]; positivity
  apply FinDist.ext
  funext σ
  rw [conditional_w _ Q hq, conditional_w μ _ hpq, hm]
  by_cases hQ : Q σ
  · rw [if_pos hQ, conditional_w μ P hp]
    simp only [hQ, and_true]
    exact div_div_div_cancel_right₀ hp.ne' _ _
  · simp only [hQ, if_false, and_false, zero_div]

def jointEvent (ks : List (Ω → C)) (σ ω : Ω) : Prop := ∀ k ∈ ks, k ω = k σ

def jointMean (ks : List (Ω → C)) (μ : FinDist Ω) (f : Ω → ℝ) (σ : Ω) : ℝ :=
  expectReal (conditional μ (jointEvent ks σ)) f

theorem jointEvent_self (ks : List (Ω → C)) (σ : Ω) : jointEvent ks σ σ := by
  intro k _
  rfl

theorem jointEvent_cons (k : Ω → C) (ks : List (Ω → C)) (σ : Ω) :
    jointEvent (k :: ks) σ = fun ω => k ω = k σ ∧ jointEvent ks σ ω := by
  funext ω
  simp only [jointEvent, List.mem_cons, forall_eq_or_imp]

/-- The iterated conditional law is exactly the law conditioned on all
revealed coordinates, at every positive atom of the original law. -/
theorem revealMean_eq_jointMean (ks : List (Ω → C)) (μ : FinDist Ω) (f : Ω → ℝ)
    (σ : Ω) (hσ : 0 < μ.w σ) : revealMean ks μ f σ = jointMean ks μ f σ := by
  induction ks generalizing μ with
  | nil =>
    have he : jointEvent ([] : List (Ω → C)) σ = fun _ => True := by
      funext ω
      simp [jointEvent]
    simp only [revealMean, jointMean, he, conditional_true]
  | cons k ks ih =>
    have hp := eventMass_pos_of_atom μ (fun ω => k ω = k σ) σ hσ rfl
    have hσ' : 0 < (given μ k (k σ)).w σ := by
      rw [given, conditional_w μ _ hp, if_pos rfl]
      positivity
    change revealMean ks (given μ k (k σ)) f σ = _
    rw [ih _ hσ']
    unfold jointMean
    rw [jointEvent_cons, given]
    congr 1
    apply conditional_intersection μ _ _ hp
    exact eventMass_pos_of_atom μ _ σ hσ ⟨rfl, jointEvent_self ks σ⟩

theorem expectReal_congr_support (μ : FinDist Ω) (f g : Ω → ℝ)
    (h : ∀ σ, 0 < μ.w σ → f σ = g σ) : expectReal μ f = expectReal μ g := by
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hσ : 0 < μ.w σ
  · rw [h σ hσ]
  · have hz : μ.w σ = 0 := le_antisymm (le_of_not_gt hσ) (μ.nonneg σ)
    simp only [hz, zero_mul]

theorem variance_congr_support (μ : FinDist Ω) (f g : Ω → ℝ)
    (h : ∀ σ, 0 < μ.w σ → f σ = g σ) : variance μ f = variance μ g := by
  rw [variance_moment, variance_moment, expectReal_congr_support μ f g h]
  congr 1
  exact expectReal_congr_support μ _ _ (fun σ hσ => by rw [h σ hσ])

theorem jointMean_expectation (ks : List (Ω → C)) (μ : FinDist Ω) (f : Ω → ℝ) :
    expectReal μ (jointMean ks μ f) = expectReal μ f := by
  rw [← revealMean_expectation ks μ f]
  exact expectReal_congr_support μ _ _ (fun σ hσ => (revealMean_eq_jointMean ks μ f σ hσ).symm)

/-- Doob's bound for the actual full-source conditional expectation. -/
theorem variance_jointMean_le (ks : List ((Ω → C) × ℝ)) (μ : FinDist Ω) (f : Ω → ℝ)
    {s K : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hscore : BoundedScores s K f ks μ) :
    variance μ (jointMean (ks.map Prod.fst) μ f) ≤ K * squareBudget ks := by
  rw [← variance_congr_support μ _ _ (revealMean_eq_jointMean (ks.map Prod.fst) μ f)]
  exact variance_reveal_le ks μ f hs hs1 hscore

end
end CI2ZF.Appendix.Girth.Doob
