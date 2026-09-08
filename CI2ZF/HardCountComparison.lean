import CI2ZF.RootChildren

/-!
# Uniform one-vertex comparison at the hard endpoint

A legal colouring outside a set can be extended by recolouring only that
set when every effective list has more colours than the full vertex degree.
Recording the old colours on that set turns this extension into an injection.
For actual root children, the set is the free neighbours of the newly pinned
root, so its size is at most the original degree bound. Pinned-only conflicts
are never tested, exactly as in the normalized partition function.
-/
namespace CI2ZF.Potts
open PottsCI
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
section Generic
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
local instance hardCountConfigDecEq : DecidableEq (V → C) := Classical.decEq _

/-- Greedy extension with the colours outside the designated set fixed. -/
theorem exists_list_recolour [Nonempty C]
    (G : SimpleGraph V) (L : V → Finset C)
    (hL : ∀ u, G.degree u + 1 ≤ (L u).card) (S : Finset V)
    (sigma : V → C)
    (hproper : ∀ u, u ∉ S → ∀ v, v ∉ S → G.Adj u v → sigma u ≠ sigma v)
    (hlist : ∀ u, u ∉ S → sigma u ∈ L u) :
    ∃ eta : V → C, (∀ u v, G.Adj u v → eta u ≠ eta v) ∧
      (∀ u, eta u ∈ L u) ∧ ∀ u, u ∉ S → eta u = sigma u := by
  induction S using Finset.induction_on generalizing sigma with
  | empty =>
    exact ⟨sigma, fun u v ha => hproper u (by simp) v (by simp) ha,
      fun u => hlist u (by simp), fun _ _ => rfl⟩
  | @insert u S hu ih =>
    have hused : ((G.neighborFinset u).image sigma).card < (L u).card := by
      have hi := Finset.card_image_le (s := G.neighborFinset u) (f := sigma)
      have hl := hL u
      rw [SimpleGraph.card_neighborFinset_eq_degree] at hi
      omega
    have hfresh : (L u \ (G.neighborFinset u).image sigma).Nonempty := by
      rw [← Finset.card_pos]
      have hd := Finset.le_card_sdiff ((G.neighborFinset u).image sigma) (L u)
      omega
    obtain ⟨c, hc⟩ := hfresh
    have hcl : c ∈ L u := (Finset.mem_sdiff.mp hc).1
    have hcf : c ∉ (G.neighborFinset u).image sigma := (Finset.mem_sdiff.mp hc).2
    let sigma' := Function.update sigma u c
    have hproper' : ∀ w, w ∉ S → ∀ z, z ∉ S → G.Adj w z → sigma' w ≠ sigma' z := by
      intro w hw z hz ha
      by_cases hwu : w = u
      · subst w
        have hzu : z ≠ u := fun he => G.irrefl (he ▸ ha)
        simp only [sigma', Function.update_apply, if_neg hzu]
        intro he
        exact hcf (Finset.mem_image.mpr ⟨z, (G.mem_neighborFinset u z).mpr ha, he.symm⟩)
      · by_cases hzu : z = u
        · subst z
          simp only [sigma', Function.update_apply, if_neg hwu]
          intro he
          exact hcf (Finset.mem_image.mpr ⟨w, (G.mem_neighborFinset u w).mpr ha.symm, he⟩)
        · simp only [sigma', Function.update_apply, if_neg hwu, if_neg hzu]
          exact hproper w (by simp [hwu, hw]) z (by simp [hzu, hz]) ha
    have hlist' : ∀ w, w ∉ S → sigma' w ∈ L w := by
      intro w hw
      by_cases hwu : w = u
      · subst w
        simpa [sigma'] using hcl
      · simpa [sigma', hwu] using hlist w (by simp [hwu, hw])
    obtain ⟨eta, heproper, helist, heagree⟩ := ih sigma' hproper' hlist'
    refine ⟨eta, heproper, helist, ?_⟩
    intro w hw
    have hws : w ∉ S := fun hs => hw (Finset.mem_insert_of_mem hs)
    have hwu : w ≠ u := fun he => hw (he ▸ Finset.mem_insert_self u S)
    rw [heagree w hws]
    simp [sigma', hwu]

/-- Hard configurations as a genuine finite subset of all colourings. -/
abbrev HardConfigurations (I : PinningData V C) := {sigma : V → C // I.HardAdmissible sigma}

theorem partition_zero_eq_card (I : PinningData V C) :
    I.partition 0 = (Fintype.card (HardConfigurations I) : ℝ) := by
  simp only [PinningData.partition, PinningData.weight_zero_eq]
  simp [HardConfigurations, Fintype.card_subtype]

/-- Two instances agreeing outside a small boundary-affected set have
a counting comparison obtained from an actual recolouring injection. -/
theorem hardConfigurations_card_le [Nonempty C]
    (I J : PinningData V C) (S : Finset V)
    (hgraph : I.graph = J.graph)
    (hboundary : ∀ u, u ∉ S → ∀ c, I.boundaryCount u c = J.boundaryCount u c)
    {Δ : ℕ} (hdegree : J.DegreeBound Δ) (hcolours : Δ + 1 ≤ Fintype.card C) :
    Fintype.card (HardConfigurations I) ≤
      Fintype.card (HardConfigurations J) * (Fintype.card C) ^ S.card := by
  have hext (sigma : HardConfigurations I) :
      ∃ eta : HardConfigurations J, ∀ u, u ∉ S → eta.val u = sigma.val u := by
    obtain ⟨eta, hp, hl, he⟩ := exists_list_recolour J.graph J.hardList
      (card_hardList_of_succ_le J hdegree hcolours) S sigma.val
      (fun u _ v _ ha => sigma.property.1 u v (hgraph ▸ ha))
      (fun u hu => by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, (hboundary u hu _).symm.trans (sigma.property.2 u)⟩)
    exact ⟨⟨eta, hp, fun u => (Finset.mem_filter.mp (hl u)).2⟩, he⟩
  let f : HardConfigurations I → HardConfigurations J × (S → C) :=
    fun sigma => ⟨(hext sigma).choose, fun u => sigma.val u.val⟩
  have hf : Function.Injective f := by
    intro sigma eta he
    apply Subtype.ext
    funext u
    by_cases hu : u ∈ S
    · exact congrFun (congrArg Prod.snd he) ⟨u, hu⟩
    · have hleft := congrArg Prod.fst he
      have heq := congrArg (fun z : HardConfigurations J => z.val u) hleft
      exact ((hext sigma).choose_spec u hu).symm.trans
        (heq.trans ((hext eta).choose_spec u hu))
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_coe] using hc

theorem partition_zero_comparison [Nonempty C]
    (I J : PinningData V C) (S : Finset V)
    (hgraph : I.graph = J.graph)
    (hboundary : ∀ u, u ∉ S → ∀ c, I.boundaryCount u c = J.boundaryCount u c)
    {Δ : ℕ} (hdegree : J.DegreeBound Δ) (hcolours : Δ + 1 ≤ Fintype.card C) :
    I.partition 0 ≤ (Fintype.card C : ℝ) ^ S.card * J.partition 0 := by
  have hc := hardConfigurations_card_le I J S hgraph hboundary hdegree hcolours
  rw [partition_zero_eq_card, partition_zero_eq_card, mul_comm]
  exact_mod_cast hc

end Generic

variable {V C : Type*} [Fintype V] [Fintype C]

/-- Actual normalized root children at zero differ by at most q^Delta,
for arbitrary initial pinning and arbitrary new root colours. -/
theorem rootChildData_partition_zero_comparison
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex) (d e : C)
    {Δ : ℕ} (hdegree : ∀ u, G.degree u ≤ Δ) (hcolours : Δ + 1 ≤ Fintype.card C) :
    (rootChildData tau G r d).partition 0 ≤
      (Fintype.card C : ℝ) ^ Δ * (rootChildData tau G r e).partition 0 := by
  let : Nonempty C := ⟨e⟩
  have hb : ∀ u, u ∉ rootBoundaryVertices tau G r → ∀ c,
      (rootChildData tau G r d).boundaryCount u c =
        (rootChildData tau G r e).boundaryCount u c := by
    intro u hu c
    have hn : ¬ G.Adj u.val r.val := by simpa [rootBoundaryVertices] using hu
    simp only [rootChildData_boundaryCount, hn, false_and, if_false, add_zero]
  have hc := partition_zero_comparison (rootChildData tau G r d) (rootChildData tau G r e)
    (rootBoundaryVertices tau G r) rfl hb (rootChildData_degreeBound tau G r e hdegree) hcolours
  apply hc.trans
  apply mul_le_mul_of_nonneg_right _ ((rootChildData tau G r e).partition_nonneg le_rfl)
  exact pow_le_pow_right₀ (by exact_mod_cast (Fintype.card_pos (α := C)))
    (rootBoundaryVertices_card_le tau G r hdegree)

/-- Real part of the normalized complex polynomial gives the same actual
hard count, including when the new pinning has pinned-only conflicts. -/
theorem normalizedPartition_pinVertex_zero_comparison
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex) (d e : C)
    {Δ : ℕ} (hdegree : ∀ u, G.degree u ≤ Δ) (hcolours : Δ + 1 ≤ Fintype.card C) :
    (normalizedPartition (pinVertex tau r d) G 0).re ≤
      (Fintype.card C : ℝ) ^ Δ * (normalizedPartition (pinVertex tau r e) G 0).re := by
  simp only [show (0 : ℂ) = ((0 : ℝ) : ℂ) from rfl,
    normalizedPartition_ofReal, Complex.ofReal_re]
  convert rootChildData_partition_zero_comparison tau G r d e hdegree hcolours using 1
  all_goals congr 1

theorem rootChildPartition_zero_comparison
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex) (d e : C)
    {Δ : ℕ} (hdegree : ∀ u, G.degree u ≤ Δ) (hcolours : Δ + 1 ≤ Fintype.card C) :
    (rootChildPartition tau G r d 0).re ≤
      (Fintype.card C : ℝ) ^ Δ * (rootChildPartition tau G r e 0).re := by
  simp only [rootChildPartition_eq_pinVertex]
  exact normalizedPartition_pinVertex_zero_comparison tau G r d e hdegree hcolours

theorem rootChildData_partition_zero_ratio_le
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex) (d e : C)
    {Δ : ℕ} (hdegree : ∀ u, G.degree u ≤ Δ) (hcolours : Δ + 1 ≤ Fintype.card C) :
    (rootChildData tau G r d).partition 0 / (rootChildData tau G r e).partition 0 ≤
      (Fintype.card C : ℝ) ^ Δ := by
  let : Nonempty C := ⟨e⟩
  have he := partition_zero_pos_of_succ_le (rootChildData tau G r e)
    (rootChildData_degreeBound tau G r e hdegree) hcolours
  exact (div_le_iff₀ he).mpr
    (rootChildData_partition_zero_comparison tau G r d e hdegree hcolours)

/-- The exact complex normalized root-child quotient has norm at most
q^Delta at zero. Its denominator is positive by the same colour threshold. -/
theorem rootChildPartition_zero_ratio_norm_le
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex) (d e : C)
    {Δ : ℕ} (hdegree : ∀ u, G.degree u ≤ Δ) (hcolours : Δ + 1 ≤ Fintype.card C) :
    ‖rootChildPartition tau G r d 0 / rootChildPartition tau G r e 0‖ ≤
      (Fintype.card C : ℝ) ^ Δ := by
  simp only [rootChildPartition_eq_pinVertex,
    show (0 : ℂ) = ((0 : ℝ) : ℂ) from rfl, normalizedPartition_ofReal,
    norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (((pinVertex tau r d).toPinningData G).partition_nonneg le_rfl),
    abs_of_nonneg (((pinVertex tau r e).toPinningData G).partition_nonneg le_rfl)]
  convert rootChildData_partition_zero_ratio_le tau G r d e hdegree hcolours using 1
  all_goals congr 1

end
end CI2ZF.Potts
