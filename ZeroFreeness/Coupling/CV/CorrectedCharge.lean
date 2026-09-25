import ZeroFreeness.Coupling.CV.SelectedChoice
import ZeroFreeness.Coupling.CV.CouplingCharge
import ZeroFreeness.Coupling.CV.Scalar

/-! All multiplicities of the actual corrected colour charge. The N₁₁
loss is absorbed at singleton incidences before summation. -/
namespace ZeroFreeness.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

def safety11Count (FX FY : HardListInstance V C) (X Y : V → C) (v : V) (c : C) : ℕ :=
  ∑ i : RootIncidence FX X v c, componentSafe11 FX FY X Y v i.val c

def safety12Count (FX FY : HardListInstance V C) (X Y : V → C) (v : V) (c : C) : ℕ :=
  ∑ i : RootIncidence FX X v c, componentSafe12 FX FY X Y v i.val c

lemma componentSafety_sum_le_one (FX FY : HardListInstance V C) (X Y : V → C)
    (v u : V) (c : C) :
    componentSafe11 FX FY X Y v u c + componentSafe12 FX FY X Y v u c ≤ 1 := by
  unfold componentSafe11 componentSafe12
  split_ifs <;> omega

lemma safetyCounts_le (FX FY : HardListInstance V C) (X Y : V → C) (v : V) (c : C) :
    safety11Count FX FY X Y v c + safety12Count FX FY X Y v c ≤
      (rootNeighbours FX X v c).card := by
  unfold safety11Count safety12Count
  rw [← Finset.sum_add_distrib]
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun (i : RootIncidence FX X v c) _ => componentSafety_sum_le_one FX FY X Y v i.val c)
  simpa [RootIncidence] using hs

lemma pair_charge_singleton_corrected {r s : ℕ} {p q loss : ℝ}
    (hr : 1 ≤ r) (hs : 1 ≤ s) (hp : p ≤ mass r) (hq : q ≤ mass s)
    (hloss : loss ≤ 81 / 250) (e : ℕ) (he : e ≤ 1)
    (heq : e = 1 → r = 1 ∧ s = 1) :
    (r : ℝ) * p + (s : ℝ) * q - min p q + loss * e ≤ 1 + 81 / 250 := by
  interval_cases e
  · simpa using pair_charge_le r s hr hs hp hq
  · obtain ⟨rfl, rfl⟩ := heq rfl
    change p ≤ 1 at hp
    change q ≤ 1 at hq
    simp only [Nat.cast_one, one_mul, mul_one]
    rcases le_total p q with hh | hh
    · rw [min_eq_left hh]
      linarith
    · rw [min_eq_right hh]
      linarith

theorem canonicalOffRootCharge_corrected_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (u w : V) {loss : ℝ} (hloss : loss ≤ 81 / 250) :
    canonicalOffRootCharge h hca hcb u w + loss * safety11Count FX FY X Y v c ≤
      (1 + 81 / 250 : ℝ) * (rootNeighbours FX X v c).card := by
  unfold canonicalOffRootCharge
  rw [CanonicalMatching.charge_as_incidence_sum _ _ (componentOf_surjective FX X v c)
    (oppositeComponentOf_surjective h hca hcb)]
  simp only [safety11Count, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _i : RootIncidence FX X v c, (1 + 81 / 250 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply pair_charge_singleton_corrected
        (Finset.card_pos.mpr (rootFamily_nonempty_component (componentOf FX X v c i).property))
        (Finset.card_pos.mpr (rootFamily_nonempty_component (oppositeComponentOf h hca hcb i).property))
        (canonical_component_share_le FX X v c u i) (canonical_opposite_share_le h hca hcb w i)
        hloss
      · exact (Nat.le_add_right _ _).trans (componentSafety_sum_le_one FX FY X Y v i.val c)
      · intro he
        unfold componentSafe11 at he
        split_ifs at he with hh
        · exact ⟨hh.1, hh.2.1⟩
    _ = _ := by simp [RootIncidence, mul_comm]; ring

theorem canonicalColourCharge_high_corrected
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h)
    (hca : c ≠ a) (hcb : c ≠ b) (hm : 3 ≤ (rootNeighbours FX X v c).card)
    {gain loss : ℝ} (hgain : 0 ≤ gain) (hloss : loss ≤ 81 / 250) :
    canonicalColourCharge h hca hcb (choice.left c) (choice.right c) +
      loss * safety11Count FX FY X Y v c - gain * safety12Count FX FY X Y v c ≤
      -1 + bulk * (rootNeighbours FX X v c).card := by
  have hN : (rootNeighbours FX X v c).Nonempty := Finset.card_pos.mp (by omega)
  have hNY : (rootNeighbours FY Y v c).Nonempty := by rwa [← h.rootNeighbours_eq hca hcb]
  rw [canonicalColourCharge, if_pos hN]
  have hX := rootCharge_le FX X v c (choice.left c) (choice.left_mem c hN)
  have hY := rootCharge_le FY Y v c (choice.right c) (choice.right_mem c hNY)
  have hO := canonicalOffRootCharge_corrected_le h hca hcb (choice.left c) (choice.right c) hloss
  have hnum := high_multiplicity_arithmetic (by exact_mod_cast hm : (3 : ℝ) ≤
    (rootNeighbours FX X v c).card)
  have hg := mul_nonneg hgain (Nat.cast_nonneg (safety12Count FX FY X Y v c))
  linarith

def correctedRegularCharge {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b : C} (h : RootLocalPair FX FY X Y v a b)
    (choice : GlobalChoice h) (c : C) (hca : c ≠ a) (hcb : c ≠ b) (gain loss : ℝ) : ℝ :=
  canonicalColourCharge h hca hcb (choice.left c) (choice.right c) +
    loss * (if c ∈ FX.list v then (safety11Count FX FY X Y v c : ℝ)
      else ((rootNeighbours FX X v c).card : ℝ)) -
    gain * (if c ∈ FX.list v then (safety12Count FX FY X Y v c : ℝ) else 0)

lemma correctedRegularCharge_unavailable_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h)
    (hca : c ≠ a) (hcb : c ≠ b) (hav : c ∉ FX.list v) (gain : ℝ)
    {loss : ℝ} (hloss : loss ≤ 81 / 500) :
    correctedRegularCharge h choice c hca hcb gain loss ≤
      (743 / 500 : ℝ) * (rootNeighbours FX X v c).card := by
  have hb := canonicalColourCharge_le_of_unavailable h hca hcb (choice.left c) (choice.right c) hav
  have hl := mul_le_mul_of_nonneg_right hloss
    (Nat.cast_nonneg (rootNeighbours FX X v c).card : (0 : ℝ) ≤ _)
  simp only [correctedRegularCharge, if_neg hav, mul_zero, sub_zero]
  linarith

lemma correctedRegularCharge_available_low_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (hav : c ∈ FX.list v)
    (hm : (rootNeighbours FX X v c).card ≤ 2) (gain loss : ℝ) :
    correctedRegularCharge h (optimizedChoice h) c hca hcb gain loss ≤
      -1 + low gain loss * (rootNeighbours FX X v c).card := by
  simp only [correctedRegularCharge, if_pos hav]
  interval_cases he : (rootNeighbours FX X v c).card
  · have he' : rootNeighbours FX X v c = ∅ := Finset.card_eq_zero.mp he
    have h11 : safety11Count FX FY X Y v c = 0 := by
      have hn := safetyCounts_le FX FY X Y v c
      omega
    have h12 : safety12Count FX FY X Y v c = 0 := by
      have hn := safetyCounts_le FX FY X Y v c
      omega
    simp [canonicalColourCharge, he', hav, h11, h12]
  · simpa only [safety11Count, safety12Count, Nat.cast_one, mul_one] using
      choice_one_corrected h (optimizedChoice h) hca hcb hav he gain loss
  · simpa only [safety11Count, safety12Count, Nat.cast_ofNat, mul_comm] using
      optimizedChoice_two_corrected h hca hcb hav he gain loss

lemma correctedRegularCharge_available_high_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h)
    (hca : c ≠ a) (hcb : c ≠ b) (hav : c ∈ FX.list v)
    (hm : 3 ≤ (rootNeighbours FX X v c).card)
    {gain loss : ℝ} (hgain : 0 ≤ gain) (hloss : loss ≤ 81 / 250) :
    correctedRegularCharge h choice c hca hcb gain loss ≤
      -1 + bulk * (rootNeighbours FX X v c).card := by
  simpa only [correctedRegularCharge, if_pos hav] using
    canonicalColourCharge_high_corrected h choice hca hcb hm hgain hloss

lemma low_le_uniform {gain loss : ℝ} (hgain : 51 / 2200 ≤ gain)
    (hloss : loss ≤ 81 / 500) : low gain loss ≤ 919 / 500 := by
  unfold low
  apply max_le
  · linarith
  · apply max_le <;> linarith

end
end ZeroFreeness.Appendix.CV
