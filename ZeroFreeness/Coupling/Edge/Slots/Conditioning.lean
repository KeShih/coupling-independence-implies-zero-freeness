import ZeroFreeness.Coupling.Edge.Slots.SimpleGraphBounds
import ZeroFreeness.Coupling.Edge.Finite.ConditionalCosts
import ZeroFreeness.Coupling.Foundations.EndpointContinuity

/-! Conditioning, deterministic colour projection, and limits commute for
the actual finite distributions used by the endpoint-slot lift. -/

namespace ZeroFreeness.Appendix.Edge
open PottsCI PottsCI.FinDist Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

namespace FiniteLaw
variable {S T : Type*} [Fintype S] [Fintype T]

lemma eventMass_mapLaw (μ : FinDist S) (f : S → T) (P : T → Prop) :
    eventMass (ZeroFreeness.mapLaw μ f) P = eventMass μ (fun x => P (f x)) := by
  have h := ZeroFreeness.expectReal_mapLaw μ f (fun y => if P y then (1 : ℝ) else 0)
  simpa only [ZeroFreeness.expectReal, mul_ite, mul_one, mul_zero, eventMass] using h

theorem conditional_mapLaw (μ : FinDist S) (f : S → T) (P : T → Prop) :
    ZeroFreeness.mapLaw (conditional μ (fun x => P (f x))) f = conditional (ZeroFreeness.mapLaw μ f) P := by
  by_cases hp : 0 < eventMass μ (fun x => P (f x))
  · have hpm : 0 < eventMass (ZeroFreeness.mapLaw μ f) P := by rwa [eventMass_mapLaw]
    apply FinDist.ext
    funext y
    rw [conditional_w _ _ hpm, eventMass_mapLaw]
    change (∑ x, (conditional μ (fun x => P (f x))).w x *
      (if y = f x then 1 else 0)) = _
    simp only [conditional_w _ _ hp]
    by_cases hy : P y
    · rw [if_pos hy]
      change _ = (∑ x, μ.w x * (if y = f x then 1 else 0)) / _
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hxy : y = f x
      · simp only [hxy ▸ hy, if_true, hxy, mul_one]
      · simp only [if_neg hxy, mul_zero, zero_div]
    · rw [if_neg hy, zero_div]
      apply Finset.sum_eq_zero
      intro x _
      by_cases hxy : y = f x
      · simp only [show ¬P (f x) from hxy ▸ hy, if_false, zero_div, zero_mul]
      · simp only [if_neg hxy, mul_zero]
  · have hpm : ¬0 < eventMass (ZeroFreeness.mapLaw μ f) P := by rwa [eventMass_mapLaw]
    simp only [conditional, dif_neg hp, dif_neg hpm]

lemma mapLaw_tendsto {μ : ℕ → FinDist S} {μ₀ : FinDist S}
    (hμ : ∀ x, Tendsto (fun n => (μ n).w x) atTop (𝓝 (μ₀.w x))) (f : S → T) (y : T) :
    Tendsto (fun n => (ZeroFreeness.mapLaw (μ n) f).w y) atTop (𝓝 ((ZeroFreeness.mapLaw μ₀ f).w y)) := by
  apply tendsto_finsetSum
  intro x _
  exact (hμ x).mul_const _

lemma eventMass_tendsto {μ : ℕ → FinDist S} {μ₀ : FinDist S}
    (hμ : ∀ x, Tendsto (fun n => (μ n).w x) atTop (𝓝 (μ₀.w x))) (P : S → Prop) :
    Tendsto (fun n => eventMass (μ n) P) atTop (𝓝 (eventMass μ₀ P)) := by
  apply tendsto_finsetSum
  intro x _
  by_cases hx : P x
  · simp only [if_pos hx]
    exact hμ x
  · simp only [if_neg hx]
    exact tendsto_const_nhds

theorem conditional_tendsto {μ : ℕ → FinDist S} {μ₀ : FinDist S}
    (hμ : ∀ x, Tendsto (fun n => (μ n).w x) atTop (𝓝 (μ₀.w x))) (P : S → Prop)
    (hp : ∀ n, 0 < eventMass (μ n) P) (hp₀ : 0 < eventMass μ₀ P) (x : S) :
    Tendsto (fun n => (conditional (μ n) P).w x) atTop (𝓝 ((conditional μ₀ P).w x)) := by
  simp only [conditional_w _ _ (hp _), conditional_w _ _ hp₀]
  apply Tendsto.div _ (eventMass_tendsto hμ P) hp₀.ne'
  by_cases hx : P x
  · simpa only [if_pos hx] using hμ x
  · simp only [if_neg hx]
    exact tendsto_const_nhds

lemma eventMass_coordinate_pos {E C : Type*} [Fintype E] [Fintype C]
    (μ : FinDist (E → C)) (hμ : ∀ φ, 0 < μ.w φ) (e : E) (c : C) :
    0 < eventMass μ (fun φ => φ e = c) := by
  have hl := eventWeight_le_mass μ (fun φ => φ e = c) (fun _ => c)
  simp only [if_true] at hl
  exact (hμ _).trans_le hl

end FiniteLaw

namespace EndpointGeometry
open FiniteLaw FiniteSystem
variable {V E C R : Type*} [Fintype V] [Fintype E] [Fintype C] [Fintype R]
local instance (priority := 2000) : DecidableEq V := Classical.decEq V
local instance (priority := 2000) : DecidableEq E := Classical.decEq E
local instance (priority := 2000) : DecidableEq C := Classical.decEq C
local instance (priority := 2000) : DecidableEq R := Classical.decEq R

def rootExcludedColourLaw (μ : FinDist (E → C)) (e : E) (c : C) :
    FinDist ({f : E // f ≠ e} → C) :=
  ZeroFreeness.mapLaw (conditional μ (fun φ => φ e = c)) (restrictConfig e)

lemma ham_colourProjection_le (σ τ : E → SlotState C R) :
    ham (colourProjection σ) (colourProjection τ) ≤ ham σ τ := by
  unfold ham hamCard
  exact_mod_cast Finset.card_le_card (show
    Finset.univ.filter (fun e => colourProjection σ e ≠ colourProjection τ e) ⊆
      Finset.univ.filter (fun e => σ e ≠ τ e) from by
        intro e he
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ e,
          fun h => (Finset.mem_filter.mp he).2 (congrArg Prod.fst h)⟩)

def remainingColourProjection (e : E) (σ : E → SlotState C R) : {f : E // f ≠ e} → C :=
  restrictConfig e (colourProjection σ)

lemma remainingColourProjection_join (e : E) (a : SlotState C R)
    (σ : {f : E // f ≠ e} → SlotState C R) :
    remainingColourProjection e (joinConfig e a σ) = colourProjection σ := by
  funext f
  exact congrArg Prod.fst (joinConfig_other e a σ f)

lemma rootExcludedColourLaw_eq (μ : FinDist (E → SlotState C R)) (e : E) (c : C) :
    rootExcludedColourLaw (ZeroFreeness.mapLaw μ colourProjection) e c =
      ZeroFreeness.mapLaw (conditional μ (fun σ => (σ e).1 = c)) (remainingColourProjection e) := by
  rw [rootExcludedColourLaw, ← conditional_mapLaw, ZeroFreeness.mapLaw_comp]
  rfl

lemma W_remaining_restore_le (e : E) (a b : SlotState C R)
    (μ ν : FinDist ({f : E // f ≠ e} → SlotState C R)) :
    W (fun σ τ => ham (remainingColourProjection e σ) (remainingColourProjection e τ))
      (ZeroFreeness.mapLaw μ (joinConfig e a)) (ZeroFreeness.mapLaw ν (joinConfig e b)) ≤ W ham μ ν := by
  obtain ⟨π, hπ⟩ := exists_optimal_coupling μ ν ham ham_nonneg
  apply (W_le_cost (fun _ _ => ham_nonneg _ _)
    (ZeroFreeness.mapCoupling π (joinConfig e a) (joinConfig e b))).trans
  rw [ZeroFreeness.cost_mapCoupling, ← hπ]
  apply ZeroFreeness.cost_le_cost π
  intro σ τ
  simp only [remainingColourProjection_join]
  exact ham_colourProjection_le σ τ

lemma colour_coordinate_data (I : FiniteSystem V E (SlotState C R) (C × R))
    (B : Boundary V (C × R)) {Δ : ℕ} (hB : I.Bounds B Δ) (e : E) (c : C)
    (hc : 0 < eventMass (I.validLaw B hB) (fun σ => (σ e).1 = c)) (a : SlotState C R)
    (ha : 0 < eventMass (conditional (I.validLaw B hB) (fun σ => (σ e).1 = c))
      (fun σ => σ e = a)) :
    I.Compatible B e a ∧
      conditional (conditional (I.validLaw B hB) (fun σ => (σ e).1 = c)) (fun σ => σ e = a) =
        ZeroFreeness.mapLaw (I.pinnedLaw B hB e a) (joinConfig e a) := by
  obtain ⟨σ, he, hs⟩ := eventMass_pos_exists _ _ ha
  have hp := (conditional_pos_support _ _ hc hs).1
  have hac : a.1 = c := by simpa only [he] using hp
  have himp (τ : E → SlotState C R) (hτ : τ e = a) : (τ e).1 = c := by rw [hτ, hac]
  have hm := eventMass_conditional_of_imp (I.validLaw B hB) (fun σ => (σ e).1 = c)
    (fun σ => σ e = a) hc himp
  have hd : 0 < eventMass (I.validLaw B hB) (fun σ => σ e = a) := by
    rw [hm] at ha
    exact (div_pos_iff_of_pos_right hc).mp ha
  refine ⟨I.gibbs_coordinate_pos_compatible B _ e a hd, ?_⟩
  rw [conditional_conditional_of_imp _ _ _ hc ha himp]
  exact I.conditional_validLaw_coordinate B hB e a hd

/-- Uniform transport bounds between the actual pinned root-state laws
survive root-colour disintegration and projection, without paying for the
removed root. The finite-state bound is supplied by the internal induction. -/
theorem rootExcludedColourLaw_W_le (I : FiniteSystem V E (SlotState C R) (C × R))
    (B : Boundary V (C × R)) {Δ : ℕ} (hB : I.Bounds B Δ) (e : E) (c d : C)
    (hc : 0 < eventMass (I.validLaw B hB) (fun σ => (σ e).1 = c))
    (hd : 0 < eventMass (I.validLaw B hB) (fun σ => (σ e).1 = d)) {K : ℝ}
    (hci : ∀ a b, I.Compatible B e a → I.Compatible B e b →
      W ham (I.pinnedLaw B hB e a) (I.pinnedLaw B hB e b) ≤ K) :
    W ham (rootExcludedColourLaw (ZeroFreeness.mapLaw (I.validLaw B hB) colourProjection) e c)
      (rootExcludedColourLaw (ZeroFreeness.mapLaw (I.validLaw B hB) colourProjection) e d) ≤ K := by
  rw [rootExcludedColourLaw_eq, rootExcludedColourLaw_eq]
  apply (ZeroFreeness.W_mapLaw_le _ _ ham ham_nonneg).trans
  apply W_le_of_conditionals _ _ (fun σ => σ e) (fun σ => σ e)
    (fun σ τ => ham (remainingColourProjection e σ) (remainingColourProjection e τ))
    (fun _ _ => ham_nonneg _ _)
  intro a b ha hb
  obtain ⟨hac, hae⟩ := colour_coordinate_data I B hB e c hc a ha
  obtain ⟨hbc, hbe⟩ := colour_coordinate_data I B hB e d hd b hb
  rw [hae, hbe]
  exact (W_remaining_restore_le e a b _ _).trans (hci a b hac hbc)

end EndpointGeometry
end
end ZeroFreeness.Appendix.Edge
