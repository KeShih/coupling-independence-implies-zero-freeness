import CI2ZF.RootColourCharge
import CI2ZF.RegularColourTwo

/-! Sum the proved actual colour charges into the conditional hard budget. -/
namespace CI2ZF
open PottsCI PottsCI.Vigoda RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V C : Type*} [Fintype V] [Fintype C]

def unionRootNeighbours (FX FY : HardListInstance V C) (X : V → C) (v : V) (c : C) :
    Finset V := ((FX.graph ⊔ FY.graph).neighborFinset v).filter (fun w => X w = c)

omit [Fintype C] in
lemma mem_unionRootNeighbours (FX FY : HardListInstance V C) (X : V → C) (v w : V) (c : C) :
    w ∈ unionRootNeighbours FX FY X v c ↔
      (FX.graph.Adj v w ∨ FY.graph.Adj v w) ∧ X w = c := by
  simp only [unionRootNeighbours, Finset.mem_filter, SimpleGraph.mem_neighborFinset,
    SimpleGraph.sup_adj]

omit [Fintype C] in
lemma unionRootNeighbours_first
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    unionRootNeighbours FX FY X v a = rootNeighbours FY Y v a := by
  ext w
  rw [mem_unionRootNeighbours, mem_rootNeighbours]
  constructor
  · rintro ⟨he | he, hc⟩
    · exact (h.properX.1 v w he (h.X_root.trans hc.symm)).elim
    · exact ⟨he, (h.agree_off_root w he.ne.symm).symm.trans hc⟩
  · rintro ⟨he, hc⟩
    exact ⟨Or.inr he, (h.agree_off_root w he.ne.symm).trans hc⟩

omit [Fintype C] in
lemma unionRootNeighbours_second
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    unionRootNeighbours FX FY X v b = rootNeighbours FX X v b := by
  ext w
  rw [mem_unionRootNeighbours, mem_rootNeighbours]
  constructor
  · rintro ⟨he | he, hc⟩
    · exact ⟨he, hc⟩
    · have hy : Y w = b := (h.agree_off_root w he.ne.symm).symm.trans hc
      exact (h.properY.1 v w he (h.Y_root.trans hy.symm)).elim
  · rintro ⟨he, hc⟩
    exact ⟨Or.inl he, hc⟩

omit [Fintype C] in
lemma unionRootNeighbours_regular
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) :
    unionRootNeighbours FX FY X v c = rootNeighbours FX X v c := by
  ext w
  rw [mem_unionRootNeighbours, mem_rootNeighbours]
  constructor
  · rintro ⟨he | he, hc⟩
    · exact ⟨he, hc⟩
    · exact ⟨(h.regular_root_edge_iff w c he.ne.symm hc hca hcb).mpr he, hc⟩
  · rintro ⟨he, hc⟩
    exact ⟨Or.inl he, hc⟩

lemma sum_unionRootNeighbours_card (FX FY : HardListInstance V C)
    (X : V → C) (v : V) :
    ∑ c : C, (unionRootNeighbours FX FY X v c).card = (FX.graph ⊔ FY.graph).degree v := by
  exact (Finset.card_eq_sum_card_fiberwise (f := X)
    (s := (FX.graph ⊔ FY.graph).neighborFinset v) (t := Finset.univ) (by simp)).symm

variable [Nonempty V] [Nonempty C]

def hardColourCharge {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b : C} (h : RootLocalPair FX FY X Y v a b) (c : C) : ℝ :=
  if hca : c = a then rootColourCharge FX FY X Y v
  else if hcb : c = b then rootColourCharge FY FX Y X v
  else RegularColourCharge.perColourCharge h hca hcb

theorem hardColourCharge_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (c : C) :
    hardColourCharge h c ≤ (11 / 6 : ℝ) * (unionRootNeighbours FX FY X v c).card -
      if c ∈ FX.list v ∩ FY.list v then 1 else 0 := by
  have hXa : a ∈ FX.list v := by simpa only [h.X_root] using h.properX.2 v
  have hYb : b ∈ FY.list v := by simpa only [h.Y_root] using h.properY.2 v
  by_cases hca : c = a
  · subst c
    rw [hardColourCharge, dif_pos rfl]
    simpa only [unionRootNeighbours_first h,
      Finset.mem_inter, hXa, true_and] using rootColourCharge_le h
  · by_cases hcb : c = b
    · subst c
      rw [hardColourCharge, dif_neg hca, dif_pos rfl]
      simpa only [unionRootNeighbours_second h,
        Finset.mem_inter, hYb, and_true] using rootColourCharge_le h.symm
    · have hc : (c ∈ FX.list v ∧ c ∈ FY.list v) ↔ c ∈ FX.list v :=
        ⟨And.left, fun hc => ⟨hc, (h.root_list_regular_iff c hca hcb).mp hc⟩⟩
      simpa only [hardColourCharge, dif_neg hca, dif_neg hcb, unionRootNeighbours_regular h hca hcb,
        Finset.mem_inter, hc] using RegularColourCharge.perColourCharge_le h hca hcb

/-- All colour-charge estimates combine to the exact union-degree and
common-list budget required by the paper's conditional hard estimate. -/
theorem sum_hardColourCharge_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    ∑ c : C, hardColourCharge h c ≤
      (11 / 6 : ℝ) * (FX.graph ⊔ FY.graph).degree v -
        ((FX.list v ∩ FY.list v).card : ℝ) := by
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hardColourCharge_le h c)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Nat.cast_sum,
    sum_unionRootNeighbours_card] at hb
  have hs : (∑ c : C, if c ∈ FX.list v ∩ FY.list v then (1 : ℝ) else 0) =
      ((FX.list v ∩ FY.list v).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul, mul_one]
  rw [hs] at hb
  exact hb

theorem sum_hardColourCharge_eq
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    ∑ c : C, hardColourCharge h c =
      rootColourCharge FX FY X Y v + rootColourCharge FY FX Y X v +
        ∑ c : {c : C // c ≠ a ∧ c ≠ b},
          RegularColourCharge.perColourCharge h c.property.1 c.property.2 := by
  have heach (c : C) : hardColourCharge h c =
      (if c = a then rootColourCharge FX FY X Y v else 0) +
      (if c = b then rootColourCharge FY FX Y X v else 0) +
      (if c ≠ a ∧ c ≠ b then hardColourCharge h c else 0) := by
    by_cases hca : c = a
    · subst c
      simp [hardColourCharge, h.colours_ne]
    · by_cases hcb : c = b
      · subst c
        simp [hardColourCharge, hca]
      · simp [hca, hcb]
  have hreg : (∑ c : {c : C // c ≠ a ∧ c ≠ b},
        RegularColourCharge.perColourCharge h c.property.1 c.property.2) =
      ∑ c : C, if c ≠ a ∧ c ≠ b then hardColourCharge h c else 0 := by
    calc
      _ = ∑ c : {c : C // c ≠ a ∧ c ≠ b}, hardColourCharge h c.val := by
        apply Finset.sum_congr rfl
        intro c _
        simp only [hardColourCharge, dif_neg c.property.1, dif_neg c.property.2]
      _ = ∑ c ∈ Finset.univ.filter (fun c => c ≠ a ∧ c ≠ b), hardColourCharge h c :=
        (Finset.sum_subtype _ (by simp) _).symm
      _ = _ := by rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun c _ => heach c)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hreg]

end
end CI2ZF
