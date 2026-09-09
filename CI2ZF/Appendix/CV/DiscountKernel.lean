import CI2ZF.Appendix.CV.Coupling
import CI2ZF.HardMoveClassification

/-! True vertex recolouring probabilities and saturated common-move support
for the CV geometric-discount analysis. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

theorem hardStep_positive_move [Nonempty V] [Nonempty C]
    (F : HardListInstance V C) (X U : V → C) (hU : U ≠ X)
    (hp : 0 < (hardStep F X).w U) :
    ∃ u c, c ≠ X u ∧ flipAllowed F (flipSet F.graph X u c)
      (flipConfiguration X (flipSet F.graph X u c) (X u) c) ∧
      U = flipConfiguration X (flipSet F.graph X u c) (X u) c := by
  rw [hardStep_w] at hp
  have hex : ∃ p ∈ (Finset.univ : Finset (V × C)),
      0 < (Fintype.card (V × C) : ℝ)⁻¹ * (proposalDistribution F X p.1 p.2).w U := by
    by_contra hn
    push Not at hn
    have hle := Finset.sum_nonpos hn
    linarith
  obtain ⟨⟨u, c⟩, _, hterm⟩ := hex
  have hp' : 0 < (proposalDistribution F X u c).w U :=
    (mul_pos_iff_of_pos_left (by positivity)).mp hterm
  by_cases hc : c = X u
  · simp [proposalDistribution, hc, FinDist.pure, hU] at hp'
  · rw [proposalDistribution, if_neg hc, twoPoint_w] at hp'
    simp only [if_neg hU, add_zero] at hp'
    split_ifs at hp' with hout
    · refine ⟨u, c, hc, ?_, hout⟩
      by_contra ha
      simp [acceptanceProbability, ha] at hp'
    · exact (lt_irrefl _ hp').elim

/-- A positive transition changing a fixed vertex to a prescribed colour
has only one possible output: the component move rooted at that vertex. -/
theorem hardStep_positive_at [Nonempty V] [Nonempty C]
    (F : HardListInstance V C) (X U : V → C) (u : V) (c : C) (hc : c ≠ X u)
    (hu : U u = c) (hp : 0 < (hardStep F X).w U) :
    U = flipConfiguration X (flipSet F.graph X u c) (X u) c ∧
      flipAllowed F (flipSet F.graph X u c)
        (flipConfiguration X (flipSet F.graph X u c) (X u) c) := by
  have hne : U ≠ X := fun hh => hc (hu.symm.trans (congrFun hh u))
  obtain ⟨s, d, hd, ha, hU⟩ := hardStep_positive_move F X U hne hp
  have hs : u ∈ flipSet F.graph X s d := by
    apply (flipConfiguration_ne_iff hd u).mp
    rw [← hU, hu]
    exact hc
  obtain ⟨hset, hconf⟩ := component_move_from_member F.graph X s d hd u hs
  rw [← hU, hu] at hset hconf
  exact ⟨hconf.symm, by rw [hconf, hset]; exact hU ▸ ha⟩

def targetProbability [Nonempty V] [Nonempty C] (F : HardListInstance V C)
    (X : V → C) (u : V) (c : C) : ℝ := ∑ U, if U u = c then (hardStep F X).w U else 0

/-- The complete probability of recolouring a vertex into a distinct colour
is the full aggregate component mass, including the list-feasibility test. -/
theorem targetProbability_eq [Nonempty V] [Nonempty C]
    (F : HardListInstance V C) (X : V → C) (u : V) (c : C) (hc : c ≠ X u) :
    targetProbability F X u c =
      if flipAllowed F (flipSet F.graph X u c)
          (flipConfiguration X (flipSet F.graph X u c) (X u) c) then
        mass (flipSet F.graph X u c).card / ((Fintype.card V : ℝ) * Fintype.card C) else 0 := by
  let U₀ := flipConfiguration X (flipSet F.graph X u c) (X u) c
  unfold targetProbability
  rw [Finset.sum_eq_single U₀]
  · have hu : U₀ u = c := flipConfiguration_at_start
    rw [if_pos hu]
    by_cases ha : flipAllowed F (flipSet F.graph X u c) U₀
    · rw [if_pos ha]
      exact hardStep_component_mass F X u c hc ha
    · rw [if_neg ha]
      apply le_antisymm _ ((hardStep F X).nonneg U₀)
      apply le_of_not_gt
      intro hp
      exact ha (hardStep_positive_at F X U₀ u c hc hu hp).2
  · intro U _ hU
    by_cases hu : U u = c
    · rw [if_pos hu]
      apply le_antisymm _ ((hardStep F X).nonneg U)
      apply le_of_not_gt
      intro hp
      exact hU (hardStep_positive_at F X U u c hc hu hp).1
    · exact if_neg hu
  · simp

lemma targetProbability_le [Nonempty V] [Nonempty C]
    (F : HardListInstance V C) (X : V → C) (u : V) (c : C) (hc : c ≠ X u) :
    targetProbability F X u c ≤ 1 / ((Fintype.card V : ℝ) * Fintype.card C) := by
  rw [targetProbability_eq F X u c hc]
  split_ifs
  · exact div_le_div_of_nonneg_right (mass_le_one _) (by positivity)
  · positivity

lemma targetProbability_le_mass_two [Nonempty V] [Nonempty C]
    (F : HardListInstance V C) (X : V → C) (u : V) (c : C) (hc : c ≠ X u)
    (hsize : 2 ≤ (flipSet F.graph X u c).card) :
    targetProbability F X u c ≤ (81 / 250) / ((Fintype.card V : ℝ) * Fintype.card C) := by
  rw [targetProbability_eq F X u c hc]
  split_ifs
  · apply div_le_div_of_nonneg_right _ (by positivity)
    exact (mass_antitone (by norm_num : 1 ≤ 2) hsize).trans_eq (by norm_num [mass])
  · positivity

/-- A coupling entry that exhausts its marginal row forces every other
positive entry in that row to use the same partner. -/
lemma coupling_saturated_row {S T : Type*} [Fintype S] [Fintype T]
    {μ : FinDist S} {ν : FinDist T} (γ : Coupling μ ν) (x : S) (y₀ y : T)
    (hfull : μ.w x ≤ γ.w x y₀) (hp : 0 < γ.w x y) : y = y₀ := by
  classical
  by_contra hne
  have hs := γ.sum_row x
  have htwo : γ.w x y₀ + γ.w x y ≤ μ.w x := by
    calc
      _ = ∑ z ∈ ({y₀, y} : Finset T), γ.w x z := by simp [Ne.symm hne]
      _ ≤ ∑ z, γ.w x z := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun z _ _ => γ.nonneg x z)
      _ = _ := hs
  linarith

end
end CI2ZF.Appendix.CV
