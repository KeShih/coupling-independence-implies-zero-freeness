import CI2ZF.Appendix.EdgeFiniteSlack
import CI2ZF.Appendix.EdgeFiniteTransport

/-! Finite conditioning and exact exposure disintegration, including events
of probability zero. Conditional transport estimates will be used only on
the positive support of the exposure weights. -/
namespace CI2ZF.Appendix.Edge.FiniteLaw
open PottsCI PottsCI.FinDist Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {S T J : Type*} [Fintype S] [Fintype T] [Fintype J]

def eventMass (μ : FinDist S) (P : S → Prop) : ℝ := ∑ x, if P x then μ.w x else 0

lemma eventMass_nonneg (μ : FinDist S) (P : S → Prop) : 0 ≤ eventMass μ P := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs <;> first | exact μ.nonneg x | rfl

lemma eventWeight_le_mass (μ : FinDist S) (P : S → Prop) (x : S) :
    (if P x then μ.w x else 0) ≤ eventMass μ P := by
  apply Finset.single_le_sum _ (Finset.mem_univ x)
  intro y _
  split_ifs <;> first | exact μ.nonneg y | rfl

lemma eventMass_pos_exists (μ : FinDist S) (P : S → Prop) (hp : 0 < eventMass μ P) :
    ∃ x, P x ∧ 0 < μ.w x := by
  obtain ⟨x, _, hx⟩ := (Finset.sum_pos_iff_of_nonneg (fun x _ => show
    0 ≤ if P x then μ.w x else 0 by split_ifs <;> first | exact μ.nonneg x | rfl)).mp hp
  by_cases hP : P x
  · exact ⟨x, hP, by simpa only [if_pos hP] using hx⟩
  · simp only [if_neg hP] at hx
    exact (lt_irrefl _ hx).elim

def conditional (μ : FinDist S) (P : S → Prop) : FinDist S :=
  if h : 0 < eventMass μ P then
    { w x := (if P x then μ.w x else 0) / eventMass μ P
      nonneg x := div_nonneg (by split_ifs <;> first | exact μ.nonneg x | rfl) h.le
      sum_one := by rw [← Finset.sum_div]; exact div_self h.ne' }
  else μ

lemma conditional_w (μ : FinDist S) (P : S → Prop) (h : 0 < eventMass μ P) (x : S) :
    (conditional μ P).w x = (if P x then μ.w x else 0) / eventMass μ P := by
  simp only [conditional, dif_pos h]

/-- Multiplication by event mass removes the arbitrary null-event fallback. -/
lemma mass_mul_conditional (μ : FinDist S) (P : S → Prop) (x : S) :
    eventMass μ P * (conditional μ P).w x = if P x then μ.w x else 0 := by
  by_cases hp : 0 < eventMass μ P
  · rw [conditional_w μ P hp, mul_div_cancel₀ _ hp.ne']
  · have hz : eventMass μ P = 0 := le_antisymm (le_of_not_gt hp) (eventMass_nonneg μ P)
    rw [hz, zero_mul]
    have hs := eventWeight_le_mass μ P x
    rw [hz] at hs
    apply le_antisymm
    · split_ifs <;> first | exact μ.nonneg x | rfl
    · exact hs

lemma conditional_pos_support (μ : FinDist S) (P : S → Prop)
    (hp : 0 < eventMass μ P) {x : S} (hx : 0 < (conditional μ P).w x) : P x ∧ 0 < μ.w x := by
  rw [conditional_w μ P hp] at hx
  have ht := (div_pos_iff_of_pos_right hp).mp hx
  by_cases hP : P x
  · exact ⟨hP, by simpa only [if_pos hP] using ht⟩
  · simp only [if_neg hP] at ht
    exact (lt_irrefl _ ht).elim

/-- An event partition gives the exact coefficient identities required by
the four-row exposure coupling. -/
theorem exposure_identity (μ : FinDist S) (P₀ : S → Prop) (Pj : J → S → Prop)
    (hzero : 0 < eventMass μ P₀)
    (hpart : ∀ x, (if P₀ x then μ.w x else 0) +
      (∑ j, if Pj j x then μ.w x else 0) = μ.w x) (x : S) :
    (conditional μ P₀).w x + ∑ j, (eventMass μ (Pj j) / eventMass μ P₀) * (conditional μ (Pj j)).w x =
      (1 + ∑ j, eventMass μ (Pj j) / eventMass μ P₀) * μ.w x := by
  have htotal : eventMass μ P₀ + ∑ j, eventMass μ (Pj j) = 1 := by
    unfold eventMass
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    simp_rw [hpart]
    exact μ.sum_one
  have hpoint : eventMass μ P₀ * (conditional μ P₀).w x +
      ∑ j, eventMass μ (Pj j) * (conditional μ (Pj j)).w x = μ.w x := by
    simp_rw [mass_mul_conditional]
    exact hpart x
  apply (mul_right_cancel₀ hzero.ne')
  rw [add_mul, Finset.sum_mul]
  have hc (j : J) : eventMass μ (Pj j) / eventMass μ P₀ * (conditional μ (Pj j)).w x * eventMass μ P₀ =
      eventMass μ (Pj j) * (conditional μ (Pj j)).w x := by field_simp
  simp_rw [hc]
  rw [mul_comm ((conditional μ P₀).w x), hpoint]
  have hm : (1 + ∑ j, eventMass μ (Pj j) / eventMass μ P₀) * eventMass μ P₀ = 1 := by
    rw [add_mul, one_mul, Finset.sum_mul]
    simp only [div_mul_cancel₀ _ hzero.ne']
    exact htotal
  rw [mul_right_comm, hm, one_mul]

/-- The exact finite marginal of an observation. -/
def marginal (μ : FinDist S) (f : S → T) : FinDist T where
  w t := eventMass μ (fun x => f x = t)
  nonneg t := eventMass_nonneg μ _
  sum_one := by
    unfold eventMass
    rw [Finset.sum_comm]
    simp
    exact μ.sum_one

/-- Disintegration by a finite observation, with null fibres handled by
zero mixture weight. -/
theorem marginal_bind_conditional (μ : FinDist S) (f : S → T) :
    (marginal μ f).bind (fun t => conditional μ (fun x => f x = t)) = μ := by
  ext x
  change (∑ t, eventMass μ (fun y => f y = t) *
    (conditional μ (fun y => f y = t)).w x) = μ.w x
  simp_rw [mass_mul_conditional]
  simp

/-- Uniform conditional transport on positive fibres survives independent
mixing of the two exposed observations. -/
theorem W_le_of_conditionals (μ ν : FinDist S) (f g : S → T)
    (d : S → S → ℝ) (hd : ∀ x y, 0 ≤ d x y) {K : ℝ}
    (hK : ∀ a b, 0 < (marginal μ f).w a → 0 < (marginal ν g).w b →
      W d (conditional μ (fun x => f x = a)) (conditional ν (fun x => g x = b)) ≤ K) :
    W d μ ν ≤ K := by
  let α := marginal μ f
  let β := marginal ν g
  let M := fun t => conditional μ (fun x => f x = t)
  let N := fun t => conditional ν (fun x => g x = t)
  let γ := Coupling.prod α β
  have hμ : α.bind M = μ := marginal_bind_conditional μ f
  have hν : β.bind N = ν := marginal_bind_conditional ν g
  calc
    W d μ ν = W d (α.bind M) (β.bind N) := by rw [hμ, hν]
    _ ≤ ∑ a, ∑ b, γ.w a b * W d (M a) (N b) := W_bind_le hd γ M N
    _ ≤ ∑ a, ∑ b, γ.w a b * K := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      rcases eq_or_lt_of_le (α.nonneg a) with ha | ha
      · simp [γ, Coupling.prod, ← ha]
      · rcases eq_or_lt_of_le (β.nonneg b) with hb | hb
        · simp [γ, Coupling.prod, ← hb]
        · exact mul_le_mul_of_nonneg_left (hK a b ha hb) (γ.nonneg a b)
    _ = K := by simp_rw [← Finset.sum_mul]; rw [γ.total_mass, one_mul]

lemma eventMass_conditional_of_imp (μ : FinDist S) (P Q : S → Prop)
    (hp : 0 < eventMass μ P) (hQP : ∀ x, Q x → P x) :
    eventMass (conditional μ P) Q = eventMass μ Q / eventMass μ P := by
  unfold eventMass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [conditional_w μ P hp]
  by_cases hq : Q x
  · simp only [hq, hQP x hq, if_true]
    rfl
  · simp only [hq, if_false, zero_div]

/-- Conditioning a second time on a subevent equals conditioning directly
on that subevent. All normalization factors are actual event masses. -/
theorem conditional_conditional_of_imp (μ : FinDist S) (P Q : S → Prop)
    (hp : 0 < eventMass μ P) (hq : 0 < eventMass (conditional μ P) Q)
    (hQP : ∀ x, Q x → P x) :
    conditional (conditional μ P) Q = conditional μ Q := by
  have hm := eventMass_conditional_of_imp μ P Q hp hQP
  have hq' : 0 < eventMass μ Q := by
    rw [hm] at hq
    exact (div_pos_iff_of_pos_right hp).mp hq
  ext x
  rw [conditional_w _ Q hq, conditional_w μ Q hq', hm]
  by_cases hx : Q x
  · rw [if_pos hx, if_pos hx, conditional_w μ P hp, if_pos (hQP x hx)]
    exact div_div_div_cancel_right₀ hp.ne' _ _
  · simp only [if_neg hx, zero_div]

end
end CI2ZF.Appendix.Edge.FiniteLaw
