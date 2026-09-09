import CI2ZF.Appendix.Edge.Finite.Conditioning

/-! The actual conditioned Gibbs law is exactly the pinned residual law,
with the exposed state restored by an injective map. -/
namespace CI2ZF.Appendix.Edge.FiniteSystem
open PottsCI PottsCI.FinDist Finset FiniteLaw
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V E A L : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype L]
local instance (priority := 2000) : DecidableEq V := Classical.decEq V
local instance (priority := 2000) : DecidableEq E := Classical.decEq E
local instance (priority := 2000) : DecidableEq A := Classical.decEq A
local instance (priority := 2000) : DecidableEq L := Classical.decEq L

def restrictConfig (e : E) (σ : E → A) : {f : E // f ≠ e} → A := fun f => σ f.val

@[simp] lemma joinConfig_restrict (e : E) (σ : E → A) :
    joinConfig e (σ e) (restrictConfig e σ) = σ :=
  (Equiv.funSplitAt e A).symm_apply_apply σ

lemma joinConfig_eq_iff (e : E) (a : A) (τ : {f : E // f ≠ e} → A) (σ : E → A) :
    σ = joinConfig e a τ ↔ σ e = a ∧ τ = restrictConfig e σ := by
  constructor
  · intro h
    subst σ
    refine ⟨joinConfig_self e a τ, ?_⟩
    ext f
    exact (joinConfig_other e a τ f).symm
  · rintro ⟨he, rfl⟩
    rw [← he, joinConfig_restrict]

lemma sum_coordinate_fibre (e : E) (a : A) (w : (E → A) → ℝ) :
    (∑ σ, if σ e = a then w σ else 0) = ∑ τ, w (joinConfig e a τ) := by
  rw [← Fintype.sum_equiv (Equiv.funSplitAt e A).symm
    (fun p => if p.1 = a then w (joinConfig e p.1 p.2) else 0)
    (fun σ => if σ e = a then w σ else 0) (fun p => by simp [joinConfig])]
  rw [Fintype.sum_prod_type]
  simp

lemma mapLaw_join_w (e : E) (a : A) (μ : FinDist ({f : E // f ≠ e} → A)) (σ : E → A) :
    (CI2ZF.mapLaw μ (joinConfig e a)).w σ = if σ e = a then μ.w (restrictConfig e σ) else 0 := by
  unfold CI2ZF.mapLaw FinDist.bind
  simp only [FinDist.pure, joinConfig_eq_iff]
  by_cases he : σ e = a
  · simp [he]
  · simp [he]

lemma configurationWeight_fibre (I : FiniteSystem V E A L) (B : Boundary V L) (e : E) (a : A) :
    (∑ σ, if σ e = a then I.configurationWeight B σ else 0) =
      (if I.Compatible B e a then I.activity e a else 0) *
        (I.remove e).partition (I.pinBoundary B e a) := by
  rw [sum_coordinate_fibre]
  simp_rw [I.configurationWeight_join]
  exact (Finset.mul_sum _ _ _).symm

lemma gibbs_coordinate_mass (I : FiniteSystem V E A L) (B : Boundary V L)
    (hZ : 0 < I.partition B) (e : E) (a : A) :
    eventMass (I.gibbs B hZ) (fun σ => σ e = a) =
      (if I.Compatible B e a then I.activity e a else 0) *
        (I.remove e).partition (I.pinBoundary B e a) / I.partition B := by
  rw [← I.configurationWeight_fibre B e a, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases he : σ e = a <;> simp [gibbs, he]

/-- On every positive coordinate fibre, conditioning the normalized Gibbs
law agrees exactly with deletion and endpoint-label pinning. -/
theorem conditional_gibbs_coordinate (I : FiniteSystem V E A L) (B : Boundary V L)
    (hZ : 0 < I.partition B) (e : E) (a : A)
    (hZp : 0 < (I.remove e).partition (I.pinBoundary B e a))
    (ha : 0 < eventMass (I.gibbs B hZ) (fun σ => σ e = a)) :
    conditional (I.gibbs B hZ) (fun σ => σ e = a) =
      CI2ZF.mapLaw ((I.remove e).gibbs (I.pinBoundary B e a) hZp) (joinConfig e a) := by
  let k : ℝ := if I.Compatible B e a then I.activity e a else 0
  have hk : k ≠ 0 := by
    intro hh
    rw [I.gibbs_coordinate_mass] at ha
    change 0 < k * _ / _ at ha
    rw [hh, zero_mul, zero_div] at ha
    exact lt_irrefl _ ha
  ext σ
  rw [conditional_w _ _ ha, mapLaw_join_w, I.gibbs_coordinate_mass]
  by_cases he : σ e = a
  · rw [if_pos he, if_pos he]
    have hw : I.configurationWeight B σ = k *
        (I.remove e).configurationWeight (I.pinBoundary B e a) (restrictConfig e σ) := by
      have h := I.configurationWeight_join B e a (restrictConfig e σ)
      rw [← he, joinConfig_restrict] at h
      simpa only [he] using h
    change I.configurationWeight B σ / I.partition B /
      (k * (I.remove e).partition (I.pinBoundary B e a) / I.partition B) = _
    rw [hw]
    change _ = (I.remove e).configurationWeight (I.pinBoundary B e a) (restrictConfig e σ) /
      (I.remove e).partition (I.pinBoundary B e a)
    rw [div_div_div_cancel_right₀ hZ.ne', mul_div_mul_left _ _ hk]
  · simp only [if_neg he, zero_div]

end
end CI2ZF.Appendix.Edge.FiniteSystem
