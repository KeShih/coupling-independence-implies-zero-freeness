import CI2ZF.Coupling.CV.ActualTwo
import CI2ZF.Coupling.CV.GlobalChoice

/-! A concrete global choice satisfying all low-multiplicity certificates.
The same selected representatives work for every gain/loss pair. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

def twoSelectorLeft {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) (hav : c ∈ FX.list v)
    (hm : (rootNeighbours FX X v c).card = 2) : V :=
  Classical.choose (exists_two_corrected_selectors h hca hcb hav hm)

def twoSelectorRight {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) (hav : c ∈ FX.list v)
    (hm : (rootNeighbours FX X v c).card = 2) : V :=
  Classical.choose (Classical.choose_spec (exists_two_corrected_selectors h hca hcb hav hm))

lemma twoSelector_spec {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) (hav : c ∈ FX.list v)
    (hm : (rootNeighbours FX X v c).card = 2) :
    twoSelectorLeft h hca hcb hav hm ∈ rootNeighbours FX X v c ∧
      twoSelectorRight h hca hcb hav hm ∈ rootNeighbours FY Y v c ∧
      ∀ gain loss : ℝ,
        canonicalColourCharge h hca hcb (twoSelectorLeft h hca hcb hav hm)
          (twoSelectorRight h hca hcb hav hm) +
          loss * (∑ i : RootIncidence FX X v c, componentSafe11 FX FY X Y v i.val c) -
          gain * (∑ i : RootIncidence FX X v c, componentSafe12 FX FY X Y v i.val c) ≤
          -1 + 2 * low gain loss :=
  Classical.choose_spec (Classical.choose_spec (exists_two_corrected_selectors h hca hcb hav hm))

/-- For an available two-incidence regular colour choose its synchronized
certificate indices; use actual largest-component representatives elsewhere. -/
def optimizedChoice {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) : GlobalChoice h where
  left c := if hc : c ≠ a ∧ c ≠ b ∧ c ∈ FX.list v ∧ (rootNeighbours FX X v c).card = 2 then
    twoSelectorLeft h hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 else (defaultGlobalChoice h).left c
  right c := if hc : c ≠ a ∧ c ≠ b ∧ c ∈ FX.list v ∧ (rootNeighbours FX X v c).card = 2 then
    twoSelectorRight h hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 else (defaultGlobalChoice h).right c
  left_mem c hN := by
    split_ifs with hc
    · exact (twoSelector_spec h hc.1 hc.2.1 hc.2.2.1 hc.2.2.2).1
    · exact (defaultGlobalChoice h).left_mem c hN
  right_mem c hN := by
    split_ifs with hc
    · exact (twoSelector_spec h hc.1 hc.2.1 hc.2.2.1 hc.2.2.2).2.1
    · exact (defaultGlobalChoice h).right_mem c hN

theorem optimizedChoice_two_corrected {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (hav : c ∈ FX.list v)
    (hm : (rootNeighbours FX X v c).card = 2) (gain loss : ℝ) :
    canonicalColourCharge h hca hcb ((optimizedChoice h).left c) ((optimizedChoice h).right c) +
      loss * (∑ i : RootIncidence FX X v c, componentSafe11 FX FY X Y v i.val c) -
      gain * (∑ i : RootIncidence FX X v c, componentSafe12 FX FY X Y v i.val c) ≤
      -1 + 2 * low gain loss := by
  have hc : c ≠ a ∧ c ≠ b ∧ c ∈ FX.list v ∧ (rootNeighbours FX X v c).card = 2 :=
    ⟨hca, hcb, hav, hm⟩
  simpa only [optimizedChoice, dif_pos hc] using (twoSelector_spec h hca hcb hav hm).2.2 gain loss

theorem choice_one_corrected {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h)
    (hca : c ≠ a) (hcb : c ≠ b) (hav : c ∈ FX.list v)
    (hm : (rootNeighbours FX X v c).card = 1) (gain loss : ℝ) :
    canonicalColourCharge h hca hcb (choice.left c) (choice.right c) +
      loss * (∑ i : RootIncidence FX X v c, componentSafe11 FX FY X Y v i.val c) -
      gain * (∑ i : RootIncidence FX X v c, componentSafe12 FX FY X Y v i.val c) ≤
      -1 + low gain loss := by
  obtain ⟨u, hN⟩ := Finset.card_eq_one.mp hm
  have hNY : rootNeighbours FY Y v c = {u} := by rwa [← h.rootNeighbours_eq hca hcb]
  have hl : choice.left c = u := by
    have hh := choice.left_mem c (by rw [hN]; exact Finset.singleton_nonempty _)
    simpa only [hN, Finset.mem_singleton] using hh
  have hr : choice.right c = u := by
    have hh := choice.right_mem c (by rw [hNY]; exact Finset.singleton_nonempty _)
    simpa only [hNY, Finset.mem_singleton] using hh
  have hsum (f : V → ℕ) : (∑ i : RootIncidence FX X v c, f i.val) = f u := by
    have heach (i : RootIncidence FX X v c) : i.val = u := by simpa only [hN, Finset.mem_singleton] using i.property
    simp only [heach, Finset.sum_const, Finset.card_univ, Fintype.card_coe, hm, one_nsmul]
  rw [hl, hr, hsum (fun u => componentSafe11 FX FY X Y v u c),
    hsum (fun u => componentSafe12 FX FY X Y v u c)]
  exact canonicalColourCharge_one_corrected h hca hcb hav u hN gain loss

end
end CI2ZF.Appendix.CV
