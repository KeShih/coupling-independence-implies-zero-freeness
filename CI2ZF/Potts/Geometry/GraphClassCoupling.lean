import CI2ZF.Potts.Geometry.GraphClassInputs
import CI2ZF.Potts.Geometry.RootLawRelabel

/-! The original graph-class CI hypothesis applies to every realized
datum by using its actual active induced graph and transporting both
root-child laws through a Hamming-preserving vertex equivalence. -/
namespace CI2ZF.Potts
open PottsCI PottsCI.FinDist Separator
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 3000) graphClassCouplingDecEq (T : Type*) : DecidableEq T :=
  Classical.decEq T
universe u v

theorem root_W_le_of_parent_relabel {O A : Type u} {C : Type v}
    [Fintype O] [Fintype A] [Fintype C]
    (tau : PartialColouring A C) (G : SimpleGraph A)
    (e : Option O ≃ tau.FreeVertex) (I : PinningData (Option O) C)
    (hI : relabelData (tau.toPinningData G) e.symm = I)
    (x : PinningData.NonnegativeParameter) (a b : C)
    (ha : 0 < (optionChildData I a).partition x)
    (hb : 0 < (optionChildData I b).partition x) {cost : ℝ}
    (hci : ∀ (ha' : 0 < (rootChildData tau G (e none) a).partition x)
      (hb' : 0 < (rootChildData tau G (e none) b).partition x),
      W ham ((rootChildData tau G (e none) a).gibbs x x.property ha')
        ((rootChildData tau G (e none) b).gibbs x x.property hb') ≤ cost) :
    W ham ((optionChildData I a).gibbs x x.property ha)
      ((optionChildData I b).gibbs x x.property hb) ≤ cost := by
  let f := (optionRootRemainingEquiv tau e).symm
  have heA := rootChildData_relabel_of_parent tau G e I hI a
  have heB := rootChildData_relabel_of_parent tau G e I hI b
  have hpA : 0 < (rootChildData tau G (e none) a).partition x := by
    rw [← partition_relabel _ f x, heA]
    exact ha
  have hpB : 0 < (rootChildData tau G (e none) b).partition x := by
    rw [← partition_relabel _ f x, heB]
    exact hb
  have hpAe : 0 < (relabelData (rootChildData tau G (e none) a) f).partition x := by
    rw [heA]
    exact ha
  have hpBe : 0 < (relabelData (rootChildData tau G (e none) b) f).partition x := by
    rw [heB]
    exact hb
  have hw := W_gibbs_relabel_le (rootChildData tau G (e none) a)
    (rootChildData tau G (e none) b) f x x.property hpA hpB hpAe hpBe
  rw [gibbs_eq_of_data_eq _ _ heA x x.property hpAe ha,
    gibbs_eq_of_data_eq _ _ heB x x.property hpBe hb] at hw
  exact hw.trans (hci hpA hpB)

theorem relabelData_relabelData_symm {V W : Type*} {C : Type v} [Fintype V] [Fintype W]
    [Fintype C] (I : PinningData V C) (e : V ≃ W) :
    relabelData (relabelData I e) e.symm = I := by
  cases I
  simp only [relabelData, Equiv.symm_symm, Equiv.symm_apply_apply]
  congr 1
  ext v w
  simp

/-- Converse of `root_W_le_of_parent_relabel`: a bound for the relabelled
option-rooted laws bounds the actual root-child laws. -/
theorem root_W_le_of_option_relabel {O A : Type u} {C : Type v}
    [Fintype O] [Fintype A] [Fintype C]
    (tau : PartialColouring A C) (G : SimpleGraph A)
    (e : Option O ≃ tau.FreeVertex) (I : PinningData (Option O) C)
    (hI : relabelData (tau.toPinningData G) e.symm = I)
    (x : PinningData.NonnegativeParameter) {r : tau.FreeVertex} (hr : e none = r) (a b : C)
    (ha : 0 < (rootChildData tau G r a).partition x)
    (hb : 0 < (rootChildData tau G r b).partition x) {cost : ℝ}
    (hci : ∀ (ha' : 0 < (optionChildData I a).partition x)
      (hb' : 0 < (optionChildData I b).partition x),
      W ham ((optionChildData I a).gibbs x x.property ha')
        ((optionChildData I b).gibbs x x.property hb') ≤ cost) :
    W ham ((rootChildData tau G r a).gibbs x x.property ha)
      ((rootChildData tau G r b).gibbs x x.property hb) ≤ cost := by
  subst hr
  let f := (optionRootRemainingEquiv tau e).symm
  have heA := rootChildData_relabel_of_parent tau G e I hI a
  have heB := rootChildData_relabel_of_parent tau G e I hI b
  have hpA : 0 < (relabelData (rootChildData tau G (e none) a) f).partition x := by
    rw [partition_relabel]; exact ha
  have hpB : 0 < (relabelData (rootChildData tau G (e none) b) f).partition x := by
    rw [partition_relabel]; exact hb
  have hoA : 0 < (optionChildData I a).partition x := by rw [← heA]; exact hpA
  have hoB : 0 < (optionChildData I b).partition x := by rw [← heB]; exact hpB
  have h := hci hoA hoB
  rw [← gibbs_eq_of_data_eq _ _ heA x x.property hpA hoA,
    ← gibbs_eq_of_data_eq _ _ heB x x.property hpB hoB] at h
  have hback := W_gibbs_relabel_le (relabelData (rootChildData tau G (e none) a) f)
    (relabelData (rootChildData tau G (e none) b) f) f.symm x x.property hpA hpB
    (by rw [relabelData_relabelData_symm]; exact ha)
    (by rw [relabelData_relabelData_symm]; exact hb)
  rw [gibbs_eq_of_data_eq _ _ (relabelData_relabelData_symm _ f) x x.property _ ha,
    gibbs_eq_of_data_eq _ _ (relabelData_relabelData_symm _ f) x x.property _ hb] at hback
  exact hback.trans h

/-- Public ambient-to-actual CI transport. There is no color-threshold
assumption here; the caller provides the two genuine positive partitions. -/
theorem AmbientRealization.root_W_le_of_graphClass_ci
    {O A : Type u} {C : Type v} [Fintype O] [Fintype A] [Fintype C]
    {I : PinningData (Option O) C} {G : SimpleGraph A} (R : AmbientRealization I G)
    (F : GraphClass.{u}) (hG : F.contains G)
    (x : PinningData.NonnegativeParameter) {cost : ℝ}
    (hci : GraphClassRootCouplingBound F C x cost) (a b : C)
    (ha : 0 < (optionChildData I a).partition x)
    (hb : 0 < (optionChildData I b).partition x) :
    W ham ((optionChildData I a).gibbs x x.property ha)
      ((optionChildData I b).gibbs x x.property hb) ≤ cost := by
  apply root_W_le_of_parent_relabel R.activePinning R.activeGraph R.activeFreeEquiv I
    R.activePinning_data x a b ha hb
  intro ha' hb'
  exact hci R.activeGraph (F.activeGraph_mem hG R) R.activePinning
    (R.activeFreeEquiv none) a b ha' hb'

theorem GraphClassRootCouplingBound.to_pinningFamily
    {F : GraphClass.{u}} {C : Type v} [Fintype C] [Nonempty C]
    {x : PinningData.NonnegativeParameter} {cost : ℝ}
    (hci : GraphClassRootCouplingBound F C x cost)
    {Delta : ℕ} (hq : Delta + 1 ≤ Fintype.card C) :
    (F.pinningFamily C).RootCouplingBound Delta hq x cost := by
  intro O _ I hI hd a b
  obtain ⟨A, hA, G, hG, ⟨R⟩⟩ := hI
  let : Fintype A := hA
  exact R.root_W_le_of_graphClass_ci F hG x hci a b _ _

theorem GraphClassTransferInputs.to_pinningFamily
    {F : GraphClass.{u}} {C : Type v} [Fintype C] [Nonempty C]
    (hci : GraphClassTransferInputs F C) {Delta : ℕ}
    (hq : Delta + 1 ≤ Fintype.card C) :
    (F.pinningFamily C).TransferCouplingInputs Delta hq := by
  constructor
  · obtain ⟨cost, hc⟩ := hci.hard
    exact ⟨cost, hc.to_pinningFamily hq⟩
  · intro delta hd hd1
    obtain ⟨cost, hc⟩ := hci.positive delta hd hd1
    exact ⟨cost, fun x hx => GraphClassRootCouplingBound.to_pinningFamily (hc x hx) hq⟩

end
end CI2ZF.Potts
