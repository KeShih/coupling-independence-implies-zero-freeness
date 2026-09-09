import CI2ZF.Potts.Model.RootChildren
import CI2ZF.Potts.Model.OptionPinning
import CI2ZF.Potts.Geometry.GenericGibbsRelabel
import CI2ZF.Coupling.Foundations.FiniteCoupling

/-! Reindexing actual original-graph root children as the `Option`
children used by the induction, including their Gibbs laws at zero. -/
namespace CI2ZF.Potts
open PottsCI PottsCI.FinDist Separator
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 3000) rootLawRelabelDecEq (T : Type*) : DecidableEq T :=
  Classical.decEq T
set_option linter.unusedSectionVars false
variable {O A C : Type*} [Fintype O] [Fintype A] [Fintype C]

def optionRootRemainingMap (tau : PartialColouring A C)
    (e : Option O ≃ tau.FreeVertex) (o : O) : RootRemaining tau (e none) :=
  ⟨(e (some o)).val, by
    intro hm
    rcases Finset.mem_insert.mp hm with hr | hp
    · have he := e.injective (Subtype.ext hr)
      exact Option.some_ne_none o he
    · exact (e (some o)).property hp⟩

def optionRootRemainingEquiv (tau : PartialColouring A C)
    (e : Option O ≃ tau.FreeVertex) : O ≃ RootRemaining tau (e none) :=
  Equiv.ofBijective (optionRootRemainingMap tau e) ⟨by
    intro o p he
    apply Option.some.inj
    apply e.injective
    exact Subtype.ext (congrArg
      (fun a : RootRemaining tau (e none) => a.val) he),
  by
    intro a
    have hn : e.symm (rootRemainingToFree tau (e none) a) ≠ none := by
      intro hn
      have he := e.apply_symm_apply (rootRemainingToFree tau (e none) a)
      rw [hn] at he
      exact a.property (Finset.mem_insert.mpr (Or.inl (congrArg Subtype.val he).symm))
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp hn
    refine ⟨o, ?_⟩
    apply Subtype.ext
    have he := congrArg e ho
    rw [e.apply_symm_apply] at he
    exact (congrArg Subtype.val he).symm⟩

@[simp] theorem optionRootRemainingEquiv_val (tau : PartialColouring A C)
    (e : Option O ≃ tau.FreeVertex) (o : O) :
    (optionRootRemainingEquiv tau e o).val = (e (some o)).val := rfl

theorem rootChildData_relabel_of_parent (tau : PartialColouring A C) (G : SimpleGraph A)
    (e : Option O ≃ tau.FreeVertex) (I : PinningData (Option O) C)
    (hI : relabelData (tau.toPinningData G) e.symm = I) (a : C) :
    relabelData (rootChildData tau G (e none) a) (optionRootRemainingEquiv tau e).symm =
      optionChildData I a := by
  subst I
  change PinningData.mk _ _ = PinningData.mk _ _
  apply congrArg₂ PinningData.mk
  · rfl
  · funext o c
    change (rootChildData tau G (e none) a).boundaryCount (optionRootRemainingEquiv tau e o) c =
      (optionChildData (relabelData (tau.toPinningData G) e.symm) a).boundaryCount o c
    rw [rootChildData_boundaryCount, optionChildData_count]
    change tau.boundaryCount G (e (some o)) c +
      (if G.Adj (e (some o)).val (e none).val ∧ a = c then 1 else 0) =
      tau.boundaryCount G (e (some o)) c +
      (if G.Adj (e none).val (e (some o)).val ∧ c = a then 1 else 0)
    congr 1
    split_ifs <;> simp_all [G.adj_comm, eq_comm]

theorem ham_relabelColouring {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (sigma tau : V → C) :
    ham (relabelColouring e sigma) (relabelColouring e tau) = ham sigma tau := by
  unfold ham hamCard
  congr 1
  simp only [Finset.card_filter]
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

theorem W_gibbs_relabel_le {V W : Type*} [Fintype V] [Fintype W]
    (I J : PinningData V C) (e : V ≃ W) (x : ℝ) (hx : 0 ≤ x)
    (hI : 0 < I.partition x) (hJ : 0 < J.partition x)
    (hIe : 0 < (relabelData I e).partition x)
    (hJe : 0 < (relabelData J e).partition x) :
    FinDist.W ham ((relabelData I e).gibbs x hx hIe) ((relabelData J e).gibbs x hx hJe) ≤
      FinDist.W ham (I.gibbs x hx hI) (J.gibbs x hx hJ) := by
  rw [gibbs_relabel I e x hx hI hIe, gibbs_relabel J e x hx hJ hJe]
  have hw := W_mapLaw_le (μ := I.gibbs x hx hI) (ν := J.gibbs x hx hJ)
    (relabelColouring (C := C) e) (relabelColouring (C := C) e) ham ham_nonneg
  simpa only [ham_relabelColouring] using hw

theorem gibbs_eq_of_data_eq {V : Type*} [Fintype V]
    (I J : PinningData V C) (h : I = J) (x : ℝ) (hx : 0 ≤ x)
    (hI : 0 < I.partition x) (hJ : 0 < J.partition x) :
    I.gibbs x hx hI = J.gibbs x hx hJ := by
  subst J
  rfl

end
end CI2ZF.Potts
