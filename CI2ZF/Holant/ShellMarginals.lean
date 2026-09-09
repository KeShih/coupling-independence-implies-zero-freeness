import CI2ZF.Holant.InstanceSeparator
import CI2ZF.Coupling.Foundations.CommonCoins

/-!
# The separator laws are actual Gibbs marginals

The shell masses in the analytic response formula are proved equal to the
pushforward of the actual finite-subset Gibbs laws.  Infeasible ambient states
have zero mass; the common typed shell space retains zero-activity states.
-/

namespace CI2ZF.Holant
open scoped BigOperators
open PottsCI PottsCI.FinDist CI2ZF.HolantCoupling
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {V E R : Type*} [Fintype V] [DecidableEq E]

theorem union_inter_shell (S J ξ B : Finset E) (hd : Disjoint S J)
    (hξ : ξ ⊆ S) (hB : B ⊆ J) : (ξ ∪ B) ∩ S = ξ := by
  rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hξ,
    Finset.disjoint_iff_inter_eq_empty.mp (hd.mono_right hB).symm, Finset.union_empty]

/-- Exact reindexing of a prescribed shell fiber. -/
theorem sum_powerset_fiber [AddCommMonoid R] (S J ξ : Finset E) (hd : Disjoint S J)
    (hξ : ξ ⊆ S) (F : Finset E → R) :
    (∑ T ∈ (S ∪ J).powerset, if T ∩ S = ξ then F T else 0) =
      ∑ B ∈ J.powerset, F (ξ ∪ B) := by
  rw [sum_powerset_union S J hd, Finset.sum_eq_single ξ]
  · apply Finset.sum_congr rfl
    intro B hB
    rw [union_inter_shell S J ξ B hd hξ (Finset.mem_powerset.mp hB), if_pos rfl]
  · intro η hη hne
    apply Finset.sum_eq_zero
    intro B hB
    rw [union_inter_shell S J η B hd (Finset.mem_powerset.mp hη)
      (Finset.mem_powerset.mp hB), if_neg hne]
  · intro hnot
    exact (hnot (Finset.mem_powerset.mpr hξ)).elim

/-- Summing exactly one actual shell fiber gives its separator factor. -/
theorem partition_shell_fiber [Field R] (inc : E → V → Prop) (I S O ξ : Finset E)
    (f : V → ℕ → R) (z : E → R) (hSI : Disjoint S I) (hSO : Disjoint S O)
    (hIO : Disjoint I O) (hsep : EdgeSeparated inc I O) (hξ : ξ ⊆ S)
    (htail : ∀ v j k, f v j = 0 → f v (j + k) = 0) :
    (∑ T ∈ (S ∪ (I ∪ O)).powerset, if T ∩ S = ξ then weight inc f z T else 0) =
      separatorCoefficient inc I O ξ f z * partition inc O (exteriorSignature inc O ξ f) z := by
  rw [sum_powerset_fiber S (I ∪ O) ξ (Finset.disjoint_union_right.mpr ⟨hSI, hSO⟩) hξ,
    sum_powerset_union I O hIO]
  simp_rw [separatorCoefficient, partition, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := O.powerset)]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro B hB
  exact separator_weight_factorization inc I O ξ A B f z hsep
    (Finset.mem_powerset.mp hA) (Finset.mem_powerset.mp hB)
    (hSI.mono hξ (Finset.mem_powerset.mp hA))
    (hSO.mono hξ (Finset.mem_powerset.mp hB))
    (hIO.mono (Finset.mem_powerset.mp hA) (Finset.mem_powerset.mp hB)) htail

section Gibbs
variable [Fintype E] [DecidableEq V]

/-- The ambient zero extension and the actual powerset sum have identical fibers. -/
theorem sum_restrictedWeight_indicator (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (p : Finset E → Prop) [DecidablePred p] :
    (∑ T : Finset E, if p T then restrictedWeight inc edges f x T else 0) =
      ∑ T ∈ edges.powerset, if p T then weight inc f x T else 0 := by
  have hi (T : Finset E) : (if p T then restrictedWeight inc edges f x T else 0) =
      if T ⊆ edges then (if p T then weight inc f x T else 0) else 0 := by
    unfold restrictedWeight
    split_ifs <;> rfl
  simp_rw [hi]
  rw [← Finset.sum_filter]
  congr 1
  ext T
  simp

/-- The pointwise actual Gibbs shell marginal is the normalized fiber sum. -/
theorem gibbs_shell_mass (inc : E → V → Prop) (edges S ξ : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (hf : ∀ v k, 0 ≤ f v k)
    (hf0 : ∀ v, 0 < f v 0) (hx : ∀ e ∈ edges, 0 ≤ x e) :
    (mapLaw (gibbs inc edges f x hf hf0 hx) (fun T => T ∩ S)).w ξ =
      (∑ T ∈ edges.powerset, if T ∩ S = ξ then weight inc f x T else 0) /
        partition inc edges f x := by
  simp only [mapLaw, FinDist.bind_w, FinDist.pure, gibbs_apply, mul_ite, mul_one, mul_zero]
  calc
    _ = (∑ T : Finset E, if T ∩ S = ξ then restrictedWeight inc edges f x T else 0) /
        partition inc edges f x := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro T _
      by_cases h : T ∩ S = ξ
      · simp [h]
      · simp [h, Ne.symm h]
    _ = _ := congrArg (fun t : ℝ => t / partition inc edges f x)
      (sum_restrictedWeight_indicator inc edges f x (fun T => T ∩ S = ξ))

theorem gibbs_shell_mass_of_subset (inc : E → V → Prop) (I S O ξ : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (hf : ∀ v k, 0 ≤ f v k)
    (hf0 : ∀ v, 0 < f v 0) (hx : ∀ e ∈ S ∪ (I ∪ O), 0 ≤ x e)
    (hSI : Disjoint S I) (hSO : Disjoint S O) (hIO : Disjoint I O)
    (hsep : EdgeSeparated inc I O) (hξ : ξ ⊆ S)
    (htail : ∀ v j k, f v j = 0 → f v (j + k) = 0) :
    (mapLaw (gibbs inc (S ∪ (I ∪ O)) f x hf hf0 hx) (fun T => T ∩ S)).w ξ =
      separatorCoefficient inc I O ξ f x * partition inc O (exteriorSignature inc O ξ f) x /
        partition inc (S ∪ (I ∪ O)) f x := by
  erw [gibbs_shell_mass, partition_shell_fiber inc I S O ξ f x hSI hSO hIO hsep hξ htail]

theorem exterior_partition_ofReal (inc : E → V → Prop) (O ξ : Finset E)
    (f : V → Signature) (x : E → ℝ) :
    partition inc O (exteriorSignature inc O ξ (complexValues f)) (fun e => (x e : ℂ)) =
      ((partition inc O (exteriorSignature inc O ξ (realValues f)) x : ℝ) : ℂ) := by
  simp [partition, weight, signatureWeight, exteriorSignature, complexValues, realValues,
    apply_ite Complex.ofReal]

namespace RootSeparator
variable {H : NormalizedInstance V E} {e : E}

theorem exterior_signature_common_real (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (b : Bool) (ξ : Finset E) :
    exteriorSignature H.incidence P.exterior ξ (realValues (P.child he hs b).signature) =
      exteriorSignature H.incidence P.exterior ξ (realValues (H.zeroChild e).signature) := by
  cases b with
  | false => rfl
  | true =>
    funext v k
    unfold exteriorSignature
    split_ifs with hv
    · simp only [child, ↓reduceIte, realValues,
        H.oneChild_signature_eq_zeroChild_off_root e he hs v (P.root_exterior v hv)]
    · rfl

theorem exteriorInstance_realPartition (P : RootSeparator H e) (ξ : P.State) (x : E → ℝ) :
    (P.exteriorInstance ξ).toInstance.realPartition x =
      partition H.incidence P.exterior
        (exteriorSignature H.incidence P.exterior ξ.val (realValues (H.zeroChild e).signature)) x := by
  have h := (H.zeroChild e).exteriorInstance_complexPartition P.exterior ξ.val
    ((H.zeroChild e).exterior_bound P.exterior ξ.val P.exterior_subset
      ((P.state_subset ξ).trans P.shell_subset)
      (P.shell_exterior.mono_left (P.state_subset ξ))) (P.state_feasible ξ) (fun e => (x e : ℂ))
  change (P.exteriorInstance ξ).toInstance.complexPartition (fun e => (x e : ℂ)) = _ at h
  rw [Instance.complexPartition_ofReal, exterior_partition_ofReal] at h
  exact_mod_cast h

/-- Every common exterior is bounded by either real child, including common
states which are structurally impossible in the one-child. -/
theorem exterior_real_le_child (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (b : Bool) (ξ : P.State) (x : E → ℝ)
    (hx : ∀ a ∈ H.edges.erase e, 0 ≤ x a) :
    (P.exteriorInstance ξ).toInstance.realPartition x ≤
      (P.child he hs b).toInstance.realPartition x := by
  rw [P.exteriorInstance_realPartition,
    ← P.exterior_signature_common_real he hs b ξ.val]
  have hp := exterior_partition_le_parent H.incidence P.interior P.shell P.exterior ξ.val
    (realValues (P.child he hs b).signature) x P.shell_interior P.shell_exterior
    P.interior_exterior P.separated (signature_zero_tail _)
    (fun v k => ((P.child he hs b).signature v).nonneg k)
    (P.child he hs b).normalized (fun a ha => hx a (P.interior_subset ha))
    (fun a ha => hx a (P.shell_subset ha)) (fun a ha => hx a (P.exterior_subset ha))
    (signature_shift_le _ (P.child he hs b).normalized)
  simpa only [P.cover, Instance.realPartition, child_incidence, child_edges] using hp

/-- The actual Gibbs law on the fixed ambient powerset, for either child. -/
def gibbsLaw (P : RootSeparator H e) (he : e ∈ H.edges) (hs : H.OneSurvives e)
    (b : Bool) (x : E → ℝ) (hx : ∀ a ∈ H.edges.erase e, 0 ≤ x a) : FinDist (Finset E) :=
  gibbs H.incidence (H.edges.erase e) (realValues (P.child he hs b).signature) x
    (fun v k => ((P.child he hs b).signature v).nonneg k)
    (fun v => ((P.child he hs b).signature v).zero_pos) hx

def ambientLaw (P : RootSeparator H e) (he : e ∈ H.edges) (hs : H.OneSurvives e)
    (b : Bool) (x : E → ℝ) (hx : ∀ a ∈ H.edges.erase e, 0 ≤ x a) : FinDist (Finset E) :=
  mapLaw (P.gibbsLaw he hs b x hx) (fun T => T ∩ P.shell)

/-- Each typed shell mass is exactly the actual Gibbs intersection marginal. -/
theorem ambientLaw_mass (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (b : Bool) (x : E → ℝ)
    (hx : ∀ a ∈ H.edges.erase e, 0 ≤ x a) (ξ : P.State) :
    (P.ambientLaw he hs b x hx).w ξ.val = (P.law he hs b x hx).w ξ := by
  unfold ambientLaw gibbsLaw
  erw [gibbs_shell_mass, ← P.cover,
    partition_shell_fiber H.incidence P.interior P.shell P.exterior ξ.val _ x
      P.shell_interior P.shell_exterior P.interior_exterior P.separated
      (P.state_subset ξ) (signature_zero_tail _),
    P.exterior_signature_common_real he hs b ξ.val, ← P.exteriorInstance_realPartition ξ x]
  simp only [law, coefficientReal, Instance.realPartition, child_incidence, child_edges, P.cover]

theorem ambientLaw_zero_of_not_subset (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (b : Bool) (x : E → ℝ)
    (hx : ∀ a ∈ H.edges.erase e, 0 ≤ x a) (ξ : Finset E) (hξ : ¬ ξ ⊆ P.shell) :
    (P.ambientLaw he hs b x hx).w ξ = 0 := by
  unfold ambientLaw gibbsLaw
  erw [gibbs_shell_mass]
  have hz : (∑ T ∈ (H.edges.erase e).powerset,
      if T ∩ P.shell = ξ then weight H.incidence (realValues (P.child he hs b).signature) x T else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro T _
    apply if_neg
    intro h
    exact hξ (h ▸ Finset.inter_subset_right)
  rw [hz, zero_div]

/-- The ambient shell law has zero mass outside the common feasible support. -/
theorem ambientLaw_zero_of_not_state (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (b : Bool) (x : E → ℝ)
    (hx : ∀ a ∈ H.edges.erase e, 0 ≤ x a) (ξ : Finset E) (hξ : ξ ∉ P.states) :
    (P.ambientLaw he hs b x hx).w ξ = 0 := by
  by_cases hsub : ξ ⊆ P.shell
  · have hcommon : ¬ ShellSurvives H.incidence (complexValues (H.zeroChild e).signature) ξ := by
      intro hc
      exact hξ (((H.zeroChild e).mem_shellStates P.shell ξ).2
        ⟨hsub, (shell_survives_iff_feasible _ _ _).1 hc⟩)
    have hdead : ¬ ShellSurvives H.incidence (realValues (P.child he hs b).signature) ξ := by
      intro hr
      have hc : ShellSurvives H.incidence (complexValues (P.child he hs b).signature) ξ := by
        intro v
        exact Complex.ofReal_ne_zero.mpr (hr v)
      exact hcommon (P.survives_imp_common he hs b ξ hc)
    unfold ambientLaw gibbsLaw
    erw [gibbs_shell_mass, ← P.cover,
      partition_shell_fiber H.incidence P.interior P.shell P.exterior ξ _ x
        P.shell_interior P.shell_exterior P.interior_exterior P.separated hsub (signature_zero_tail _),
      separatorCoefficient_zero_of_not_survives _ _ _ _ _ _ (signature_zero_tail _) hdead,
      zero_mul, zero_div]
  · exact P.ambientLaw_zero_of_not_subset he hs b x hx ξ hsub

/-- Regard a feasible ambient shell as a typed state.  The fallback is used only
on states to which every child shell marginal assigns mass zero. -/
def liftShell (P : RootSeparator H e) (ξ : Finset E) : P.State :=
  if h : ξ ∈ P.states then ⟨ξ, h⟩ else P.emptyState

def shellProjection (P : RootSeparator H e) (T : Finset E) : P.State :=
  P.liftShell (T ∩ P.shell)

@[simp] theorem liftShell_state (P : RootSeparator H e) (ξ : P.State) :
    P.liftShell ξ.val = ξ := by simp [liftShell, ξ.property]

theorem lift_ambientLaw (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (b : Bool) (x : E → ℝ)
    (hx : ∀ a ∈ H.edges.erase e, 0 ≤ x a) :
    mapLaw (P.ambientLaw he hs b x hx) P.liftShell = P.law he hs b x hx := by
  apply FinDist.ext
  funext ξ
  simp only [mapLaw, FinDist.bind_w, FinDist.pure]
  rw [Finset.sum_eq_single ξ.val]
  · simp [P.ambientLaw_mass he hs b x hx ξ]
  · intro η _ hne
    by_cases hη : η ∈ P.states
    · have hdiff : ξ ≠ P.liftShell η := by
        intro h
        have hh := congrArg Subtype.val h
        exact hne (by simpa only [liftShell, dif_pos hη] using hh.symm)
      rw [if_neg hdiff, mul_zero]
    · rw [P.ambientLaw_zero_of_not_state he hs b x hx η hη, zero_mul]
  · simp

/-- The analytic law is literally the pushforward of the actual Gibbs law
onto the common structurally feasible shell space. -/
theorem law_eq_projected_gibbs (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (b : Bool) (x : E → ℝ)
    (hx : ∀ a ∈ H.edges.erase e, 0 ≤ x a) :
    mapLaw (P.gibbsLaw he hs b x hx) P.shellProjection = P.law he hs b x hx := by
  rw [show P.shellProjection = (fun T => P.liftShell (T ∩ P.shell)) from rfl,
    ← CI2ZF.mapLaw_comp]
  exact P.lift_ambientLaw he hs b x hx

/-- On every configuration of nonzero Gibbs mass, the typed projection is
the literal intersection with the shell. -/
theorem shellProjection_val_of_ne_zero (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (b : Bool) (x : E → ℝ)
    (hx : ∀ a ∈ H.edges.erase e, 0 ≤ x a) (T : Finset E)
    (hT : (P.gibbsLaw he hs b x hx).w T ≠ 0) :
    (P.shellProjection T).val = T ∩ P.shell := by
  have hle : (P.gibbsLaw he hs b x hx).w T ≤
      (P.ambientLaw he hs b x hx).w (T ∩ P.shell) := by
    have h := Finset.single_le_sum
      (f := fun U => (P.gibbsLaw he hs b x hx).w U *
        (if T ∩ P.shell = U ∩ P.shell then (1 : ℝ) else 0))
      (fun U _ => mul_nonneg ((P.gibbsLaw he hs b x hx).nonneg U)
        (by split_ifs <;> norm_num)) (Finset.mem_univ T)
    simpa [ambientLaw, mapLaw, FinDist.bind_w, FinDist.pure] using h
  have hm : T ∩ P.shell ∈ P.states := by
    by_contra hm
    rw [P.ambientLaw_zero_of_not_state he hs b x hx _ hm] at hle
    exact hT (le_antisymm hle ((P.gibbsLaw he hs b x hx).nonneg T))
  simp [shellProjection, liftShell, hm]

/-- Project any actual root coupling onto the common typed shell support. -/
def projectedCoupling (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (x : E → ℝ) (hx : ∀ a ∈ H.edges.erase e, 0 ≤ x a)
    (π : Coupling (P.gibbsLaw he hs false x hx) (P.gibbsLaw he hs true x hx)) :
    Coupling (P.law he hs false x hx) (P.law he hs true x hx) where
  w := (mapCoupling π P.shellProjection P.shellProjection).w
  nonneg := (mapCoupling π P.shellProjection P.shellProjection).nonneg
  sum_row ξ := by
    rw [← P.law_eq_projected_gibbs he hs false x hx]
    exact (mapCoupling π P.shellProjection P.shellProjection).sum_row ξ
  sum_col ξ := by
    rw [← P.law_eq_projected_gibbs he hs true x hx]
    exact (mapCoupling π P.shellProjection P.shellProjection).sum_col ξ

/-- Typed projection has exactly the ordinary intersection cost.  The
arbitrary fallback on zero-mass ambient states contributes no transport cost. -/
theorem projectedCoupling_cost (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (x : E → ℝ) (hx : ∀ a ∈ H.edges.erase e, 0 ≤ x a)
    (π : Coupling (P.gibbsLaw he hs false x hx) (P.gibbsLaw he hs true x hx))
    (d : Finset E → Finset E → ℝ) :
    (P.projectedCoupling he hs x hx π).cost (fun ξ η => d ξ.val η.val) =
      π.cost (fun T U => d (T ∩ P.shell) (U ∩ P.shell)) := by
  change (mapCoupling π P.shellProjection P.shellProjection).cost _ = _
  rw [cost_mapCoupling]
  unfold Coupling.cost
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro U _
  dsimp only
  by_cases hπ : π.w T U = 0
  · rw [hπ, zero_mul, zero_mul]
  · have hT : (P.gibbsLaw he hs false x hx).w T ≠ 0 := fun h => hπ (π.eq_zero_of_row h U)
    have hU : (P.gibbsLaw he hs true x hx).w U ≠ 0 := fun h => hπ (π.eq_zero_of_col h T)
    rw [P.shellProjection_val_of_ne_zero he hs false x hx T hT,
      P.shellProjection_val_of_ne_zero he hs true x hx U hU]

/-- Transport on the typed feasible shell laws is bounded by the transport
cost of literal shell intersections on the original child configurations. -/
theorem W_law_le_intersection (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (x : E → ℝ) (hx : ∀ a ∈ H.edges.erase e, 0 ≤ x a)
    (d : Finset E → Finset E → ℝ) (hd : ∀ T U, 0 ≤ d T U) :
    W (fun ξ η : P.State => d ξ.val η.val)
        (P.law he hs false x hx) (P.law he hs true x hx) ≤
      W (fun T U => d (T ∩ P.shell) (U ∩ P.shell))
        (P.gibbsLaw he hs false x hx) (P.gibbsLaw he hs true x hx) := by
  apply le_W
  intro π
  have hbound := W_le_cost (d := fun ξ η : P.State => d ξ.val η.val)
    (fun ξ η => hd ξ.val η.val) (P.projectedCoupling he hs x hx π)
  exact hbound.trans_eq (P.projectedCoupling_cost he hs x hx π d)

end RootSeparator
end Gibbs
end
end CI2ZF.Holant
