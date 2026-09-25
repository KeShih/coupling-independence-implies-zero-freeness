import ZeroFreeness.Coupling.CV.DiscountKernel
import ZeroFreeness.Coupling.CV.GlobalCoupling

/-! The actual CV coupling cannot create an off-root disagreement in a
non-target colour. Outside root recolouring, target events use only two
marginal transition rates. -/
namespace ZeroFreeness.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C] [Nonempty V] [Nonempty C]

lemma coupling_entry_le_left {S T : Type*} [Fintype S] [Fintype T]
    {μ : FinDist S} {ν : FinDist T} (γ : Coupling μ ν) (s : S) (t : T) :
    γ.w s t ≤ μ.w s := by
  rw [← γ.sum_row]
  exact Finset.single_le_sum (fun t _ => γ.nonneg s t) (Finset.mem_univ t)

lemma coupling_entry_le_right {S T : Type*} [Fintype S] [Fintype T]
    {μ : FinDist S} {ν : FinDist T} (γ : Coupling μ ν) (s : S) (t : T) :
    γ.w s t ≤ ν.w t := by
  rw [← γ.sum_col]
  exact Finset.single_le_sum (fun s _ => γ.nonneg s t) (Finset.mem_univ s)

def transposeCoupling {S T : Type*} [Fintype S] [Fintype T]
    {μ : FinDist S} {ν : FinDist T} (γ : Coupling μ ν) : Coupling ν μ where
  w t s := γ.w s t
  nonneg t s := γ.nonneg s t
  sum_row := γ.sum_col
  sum_col := γ.sum_row

/-- A root-preserving change whose new colour is not the opposite root
colour must use the fully synchronous common allocation. -/
theorem common_at_support
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b)
    (γ : Coupling (hardStep FX X) (hardStep FY Y))
    (hdom : ∀ U Z, (hardCommonOffRootPartial FX FY X Y v).w U Z ≤ γ.w U Z)
    (U Z : V → C) (hp : 0 < γ.w U Z) (hv : U v = X v)
    (u : V) (hu : u ≠ v) (hub : X u ≠ b)
    (hchange : U u ≠ X u) (htarget : U u ≠ b) : U u = Z u := by
  have hpU := hp.trans_le (coupling_entry_le_left γ U Z)
  obtain ⟨hout, ha⟩ := hardStep_positive_at FX X U u (U u) hchange rfl hpU
  have hvX : v ∉ flipSet FX.graph X u (U u) := by
    intro hm
    have hh := (flipConfiguration_ne_iff hchange v).mpr hm
    rw [← hout, hv] at hh
    exact hh rfl
  have hvY : v ∉ flipSet FY.graph Y u (U u) := by
    intro hm
    rcases colour_eq_of_mem_flipSet hm with hh | hh
    · exact hub ((h.agree_off_root u hu).trans (hh.symm.trans h.Y_root))
    · exact htarget (hh.symm.trans h.Y_root)
  have hsets := common_component_sets h u (U u) hvX hvY
  let Z₀ := flipConfiguration Y (flipSet FY.graph Y u (U u)) (Y u) (U u)
  have hm := hardCommonOffRoot_component_match h u (U u) hchange hsets hvX ha
  have hmass := hardStep_component_mass FX X u (U u) hchange ha
  rw [← hmass, ← hout] at hm
  have hfull : (hardStep FX X).w U ≤ γ.w U Z₀ := by rw [← hm]; exact hdom _ _
  have hz := coupling_saturated_row γ U Z₀ Z hfull hp
  rw [hz]
  exact flipConfiguration_at_start.symm

/-- All root-preserving losses of a regular endpoint are contained in
`X -> b` or `Y -> a`, even when the completion is a product coupling. -/
theorem root_fixed_badAt_implies_cross
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b)
    (γ : Coupling (hardStep FX X) (hardStep FY Y))
    (hdom : ∀ U Z, (hardCommonOffRootPartial FX FY X Y v).w U Z ≤ γ.w U Z)
    (U Z : V → C) (hp : 0 < γ.w U Z) (hvU : U v = X v) (hvZ : Z v = Y v)
    (u : V) (hu : u ≠ v) (hua : X u ≠ a) (hub : X u ≠ b)
    (hbad : ¬ (U u = Z u ∧ U u ≠ a ∧ U u ≠ b)) : U u = b ∨ Z u = a := by
  by_contra hn
  push Not at hn
  have hagree : U u = Z u := by
    by_cases hchange : U u = X u
    · by_cases hz : Z u = Y u
      · exact hchange.trans ((h.agree_off_root u hu).trans hz.symm)
      · have hdom' (Z U : V → C) :
            (hardCommonOffRootPartial FY FX Y X v).w Z U ≤ (transposeCoupling γ).w Z U := by
          rw [hardCommonOffRoot_transpose_w h]
          exact hdom U Z
        exact (common_at_support h.symm (transposeCoupling γ) hdom' Z U hp hvZ u hu
          (by simpa only [← h.agree_off_root u hu] using hua) hz hn.2).symm
    · exact common_at_support h γ hdom U Z hp hvU u hu hub hchange hn.1
  exact hbad ⟨hagree, fun ha => hn.2 (hagree.symm.trans ha), hn.1⟩

/-- The complete probability of losing regularity outside root recolouring
is bounded by two concrete vertex-target probabilities. -/
theorem root_fixed_badAt_mass_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b)
    (γ : Coupling (hardStep FX X) (hardStep FY Y))
    (hdom : ∀ U Z, (hardCommonOffRootPartial FX FY X Y v).w U Z ≤ γ.w U Z)
    (u : V) (hu : u ≠ v) (hua : X u ≠ a) (hub : X u ≠ b) :
    (∑ U, ∑ Z, if U v = X v ∧ Z v = Y v ∧
        ¬ (U u = Z u ∧ U u ≠ a ∧ U u ≠ b) then γ.w U Z else 0) ≤
      targetProbability FX X u b + targetProbability FY Y u a := by
  calc
    _ ≤ ∑ U, ∑ Z, ((if U u = b then γ.w U Z else 0) +
        (if Z u = a then γ.w U Z else 0)) := by
      apply Finset.sum_le_sum
      intro U _
      apply Finset.sum_le_sum
      intro Z _
      by_cases hp : 0 < γ.w U Z
      · by_cases hevent : U v = X v ∧ Z v = Y v ∧
            ¬ (U u = Z u ∧ U u ≠ a ∧ U u ≠ b)
        · rw [if_pos hevent]
          have hc := root_fixed_badAt_implies_cross h γ hdom U Z hp hevent.1
            hevent.2.1 u hu hua hub hevent.2.2
          rcases hc with hb | ha
          · rw [if_pos hb]; split_ifs <;> linarith
          · rw [if_pos ha]; split_ifs <;> linarith
        · rw [if_neg hevent]; split_ifs <;> linarith
      · have hz : γ.w U Z = 0 := le_antisymm (le_of_not_gt hp) (γ.nonneg U Z)
        simp [hz]
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro U _
        by_cases hu : U u = b <;> simp [hu, γ.sum_row]
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro Z _
        by_cases hu : Z u = a <;> simp [hu, γ.sum_col]

/-- In particular, the actual completed CV coupling has at most `2/(nq)`
probability of a root-preserving target loss at a regular vertex. -/
theorem fullHardCoupling_root_fixed_badAt_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h)
    (u : V) (hu : u ≠ v) (hua : X u ≠ a) (hub : X u ≠ b) :
    (∑ U, ∑ Z, if U v = X v ∧ Z v = Y v ∧
        ¬ (U u = Z u ∧ U u ≠ a ∧ U u ≠ b) then (fullHardCoupling h choice).w U Z else 0) ≤
      2 / ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hle := root_fixed_badAt_mass_le h (fullHardCoupling h choice)
    (fullHardCoupling_dominate_common h choice) u hu hua hub
  have hx := targetProbability_le FX X u b hub.symm
  have hy := targetProbability_le FY Y u a (by simpa only [← h.agree_off_root u hu] using hua.symm)
  simpa only [← add_div, one_add_one_eq_two] using hle.trans (add_le_add hx hy)

/-- A certified cross pair can be subtracted from the union of the two
marginal target events. This includes the singleton case at an active root edge. -/
theorem root_fixed_badAt_mass_le_with_cross
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b)
    (γ : Coupling (hardStep FX X) (hardStep FY Y))
    (hdom : ∀ U Z, (hardCommonOffRootPartial FX FY X Y v).w U Z ≤ γ.w U Z)
    (u : V) (hu : u ≠ v) (hua : X u ≠ a) (hub : X u ≠ b)
    (U₀ Z₀ : V → C) (hUb : U₀ u = b) (hZa : Z₀ u = a) :
    (∑ U, ∑ Z, if U v = X v ∧ Z v = Y v ∧
        ¬ (U u = Z u ∧ U u ≠ a ∧ U u ≠ b) then γ.w U Z else 0) ≤
      targetProbability FX X u b + targetProbability FY Y u a - γ.w U₀ Z₀ := by
  have hpoint (U Z : V → C) :
      (if U v = X v ∧ Z v = Y v ∧ ¬ (U u = Z u ∧ U u ≠ a ∧ U u ≠ b)
        then γ.w U Z else 0) + (if U = U₀ ∧ Z = Z₀ then γ.w U Z else 0) ≤
      (if U u = b then γ.w U Z else 0) + (if Z u = a then γ.w U Z else 0) := by
    have hn := γ.nonneg U Z
    by_cases hp : 0 < γ.w U Z
    · by_cases hmatch : U = U₀ ∧ Z = Z₀
      · obtain ⟨hU, hZ⟩ := hmatch
        subst U
        subst Z
        rw [if_pos hUb, if_pos hZa, if_pos (show U₀ = U₀ ∧ Z₀ = Z₀ from ⟨rfl, rfl⟩)]
        split_ifs <;> linarith
      · rw [if_neg hmatch, add_zero]
        by_cases hevent : U v = X v ∧ Z v = Y v ∧
            ¬ (U u = Z u ∧ U u ≠ a ∧ U u ≠ b)
        · rw [if_pos hevent]
          have hc := root_fixed_badAt_implies_cross h γ hdom U Z hp hevent.1
            hevent.2.1 u hu hua hub hevent.2.2
          rcases hc with hb | ha
          · rw [if_pos hb]; split_ifs <;> linarith
          · rw [if_pos ha]; split_ifs <;> linarith
        · rw [if_neg hevent]; split_ifs <;> linarith
    · have hz : γ.w U Z = 0 := le_antisymm (le_of_not_gt hp) hn
      simp [hz]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun U _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun Z _ => hpoint U Z))
  simp only [Finset.sum_add_distrib] at hsum
  have hm : (∑ U, ∑ Z, if U = U₀ ∧ Z = Z₀ then γ.w U Z else 0) = γ.w U₀ Z₀ := by
    classical
    rw [Finset.sum_eq_single U₀]
    · simp
    · intro U _ hU; simp [hU]
    · simp
  have hleft : (∑ U, ∑ Z, if U u = b then γ.w U Z else 0) = targetProbability FX X u b := by
    apply Finset.sum_congr rfl
    intro U _
    by_cases hu : U u = b <;> simp [hu, γ.sum_row]
  have hright : (∑ U, ∑ Z, if Z u = a then γ.w U Z else 0) = targetProbability FY Y u a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro Z _
    by_cases hu : Z u = a <;> simp [hu, γ.sum_col]
  rw [hm, hleft, hright] at hsum
  linarith

end
end ZeroFreeness.Appendix.CV
