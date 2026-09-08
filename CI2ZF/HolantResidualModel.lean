import CI2ZF.HolantSignatures
import CI2ZF.HolantSeparator

/-!
# Actual residual Holant instances

This module connects signature log-concavity to the finite-subset partition
semantics.  Child instances contain actual signatures of the deleted graph's
arity.  Zero-tail, normalized child monotonicity, separator factorization and
residual-family closure are conclusions of the signature definitions.
-/

namespace CI2ZF.Holant
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq E]

def realValues (f : V → Signature) : V → ℕ → ℝ := fun v => (f v).value

def complexValues (f : V → Signature) : V → ℕ → ℂ := fun v k => ((f v).value k : ℂ)

theorem signature_zero_tail (f : V → Signature) (v : V) (j k : ℕ)
    (hj : realValues f v j = 0) : realValues f v (j + k) = 0 :=
  (f v).zero_of_zero_le hj (Nat.le_add_right _ _)

theorem signature_complex_zero_tail (f : V → Signature) (v : V) (j k : ℕ)
    (hj : complexValues f v j = 0) : complexValues f v (j + k) = 0 := by
  have hr : (f v).value j = 0 := by simpa only [complexValues, Complex.ofReal_eq_zero] using hj
  simpa only [complexValues, Complex.ofReal_eq_zero] using
    (f v).zero_of_zero_le hr (Nat.le_add_right j k)

/-- The shift comparison also holds when the denominator is zero. -/
theorem signature_shift_le (f : V → Signature) (hnorm : ∀ v, (f v).value 0 = 1)
    (v : V) (t k : ℕ) : realValues f v (t + k) / realValues f v t ≤ realValues f v k := by
  by_cases ht : (f v).value t = 0
  · simp only [realValues, ht, div_zero]
    exact (f v).nonneg k
  · exact (f v).shift_monotonicity (hnorm v)
      (lt_of_le_of_ne ((f v).nonneg t) (Ne.symm ht))

theorem shell_survives_iff_feasible (inc : E → V → Prop) (f : V → Signature) (ξ : Finset E) :
    ShellSurvives inc (complexValues f) ξ ↔ Feasible inc (realValues f) ξ := by
  constructor
  · intro h v
    have hn : (f v).value (selectedDegree inc ξ v) ≠ 0 := by
      simpa only [complexValues, Complex.ofReal_ne_zero] using h v
    exact lt_of_le_of_ne ((f v).nonneg _) (Ne.symm hn)
  · intro h v
    simpa only [complexValues, realValues, Complex.ofReal_ne_zero] using (h v).ne'

/-- A shell is structurally feasible exactly when it admits a structurally
feasible completion.  Initial support permits deleting every completion edge. -/
theorem signature_feasible_iff_completion (inc : E → V → Prop) (f : V → Signature)
    (I O ξ : Finset E) :
    Feasible inc (realValues f) ξ ↔
      ∃ A ∈ I.powerset, ∃ B ∈ O.powerset, Feasible inc (realValues f) (ξ ∪ (A ∪ B)) := by
  constructor
  · intro h
    exact ⟨∅, Finset.empty_mem_powerset I, ∅, Finset.empty_mem_powerset O, by simpa using h⟩
  · rintro ⟨A, _, B, _, h⟩
    exact feasible_downward inc (realValues f)
      (fun v _ _ hij hj => (f v).initial_support hij hj) (Finset.subset_union_left) h

/-- The actual multivariate partition is continuous jointly in all activities. -/
theorem partition_continuous (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℂ) : Continuous (fun z : E → ℂ => partition inc edges f z) := by
  unfold partition weight
  fun_prop

/-- A finite incidence instance carries signatures of exactly the actual degrees. -/
structure Instance (V E : Type*) [Fintype V] [DecidableEq E] where
  incidence : E → V → Prop
  edges : Finset E
  signature : V → Signature
  arity_eq : ∀ v, (signature v).arity = selectedDegree incidence edges v

/-- Normalized instances are the inductively closed class used in the proof. -/
structure NormalizedInstance (V E : Type*) [Fintype V] [DecidableEq E]
    extends Instance V E where
  normalized : ∀ v, (signature v).value 0 = 1

namespace Instance

def realPartition (H : Instance V E) (x : E → ℝ) : ℝ :=
  partition H.incidence H.edges (realValues H.signature) x

def complexPartition (H : Instance V E) (z : E → ℂ) : ℂ :=
  partition H.incidence H.edges (complexValues H.signature) z

theorem realPartition_pos (H : Instance V E) (x : E → ℝ)
    (hx : ∀ e ∈ H.edges, 0 ≤ x e) : 0 < H.realPartition x :=
  partition_pos H.incidence H.edges _ x (fun v k => (H.signature v).nonneg k)
    (fun v => (H.signature v).zero_pos) hx

theorem complexPartition_ofReal (H : Instance V E) (x : E → ℝ) :
    H.complexPartition (fun e => (x e : ℂ)) = (H.realPartition x : ℂ) :=
  partition_ofReal H.incidence H.edges (realValues H.signature) x

theorem complexPartition_real_ne_zero (H : Instance V E) (x : E → ℝ)
    (hx : ∀ e ∈ H.edges, 0 ≤ x e) : H.complexPartition (fun e => (x e : ℂ)) ≠ 0 := by
  rw [H.complexPartition_ofReal]
  exact_mod_cast (H.realPartition_pos x hx).ne'

theorem complexPartition_continuous (H : Instance V E) : Continuous H.complexPartition :=
  partition_continuous H.incidence H.edges (complexValues H.signature)

/-- Convert any graph with matching arities to the finite-incidence semantics. -/
def ofGraph [DecidableEq V] (G : SimpleGraph V) (f : V → Signature)
    (harity : ∀ v, (f v).arity = G.degree v) : Instance V (Sym2 V) where
  incidence := graphIncidence
  edges := G.edgeFinset
  signature := f
  arity_eq v := (harity v).trans (selectedDegree_graph G v).symm

@[simp] theorem ofGraph_complexPartition [DecidableEq V] (G : SimpleGraph V)
    (f : V → Signature) (harity : ∀ v, (f v).arity = G.degree v) (z : Sym2 V → ℂ) :
    (ofGraph G f harity).complexPartition z = graphPartition G (complexValues f) z := rfl

/-- Normalize every vertex at zero without changing the graph or its activities. -/
def normalize (H : Instance V E) : NormalizedInstance V E where
  incidence := H.incidence
  edges := H.edges
  signature v := (H.signature v).normalizedResidual 0 (H.signature v).arity
    (by omega) (H.signature v).zero_pos
  arity_eq v := H.arity_eq v
  normalized v := (H.signature v).normalizedResidual_zero 0 (H.signature v).arity
    (by omega) (H.signature v).zero_pos

theorem normalize_value (H : Instance V E) (v : V) (k : ℕ) :
    (H.normalize.signature v).value k = (H.signature v).value k / (H.signature v).value 0 := by
  by_cases hk : k ≤ (H.signature v).arity
  · simp [normalize, Signature.normalizedResidual, hk]
  · have hz := (H.signature v).outside k (by omega)
    simp [normalize, Signature.normalizedResidual, hk, hz]

/-- Exact original-to-normalized conversion, as an identity for independent
complex activities, with a positive activity-independent scalar. -/
theorem complexPartition_normalize (H : Instance V E) (z : E → ℂ) :
    H.complexPartition z = (∏ v, ((H.signature v).value 0 : ℂ)) *
      H.normalize.toInstance.complexPartition z := by
  unfold complexPartition
  rw [partition_normalization H.incidence H.edges (complexValues H.signature) z
    (fun v => by simpa only [complexValues, Complex.ofReal_ne_zero] using (H.signature v).zero_pos.ne')]
  congr 1
  apply congrArg (fun f => partition H.incidence H.edges f z)
  funext v k
  simpa only [normalizedSignature, complexValues, Complex.ofReal_div] using
    congrArg Complex.ofReal (H.normalize_value v k).symm

theorem normalization_scalar_pos (H : Instance V E) :
    0 < ∏ v, (H.signature v).value 0 :=
  Finset.prod_pos (fun v _ => (H.signature v).zero_pos)

theorem normalize_family (H : Instance V E) (F : Finset Signature)
    (hF : ∀ v, H.signature v ∈ F) (v : V) : H.normalize.signature v ∈ residualFamily F := by
  apply (mem_residualFamily F _).2
  exact ⟨H.signature v, hF v, 0, (H.signature v).arity, by omega,
    (H.signature v).zero_pos, rfl⟩

end Instance

namespace NormalizedInstance

/-- Restrict to any subset of free edges, retaining normalized zero-pinned
residual signatures at every vertex. -/
def restrict (H : NormalizedInstance V E) (A : Finset E) (hA : A ⊆ H.edges) :
    NormalizedInstance V E where
  incidence := H.incidence
  edges := A
  signature v := (H.signature v).normalizedResidual 0 (selectedDegree H.incidence A v)
    (by rw [H.arity_eq]; simpa using selectedDegree_mono H.incidence hA v)
    (H.signature v).zero_pos
  arity_eq _ := rfl
  normalized v := (H.signature v).normalizedResidual_zero 0 _ _ _

theorem restrict_complexPartition (H : NormalizedInstance V E) (A : Finset E)
    (hA : A ⊆ H.edges) (z : E → ℂ) :
    (H.restrict A hA).toInstance.complexPartition z =
      partition H.incidence A (complexValues H.signature) z := by
  apply partition_congr_signatures
  intro v k hk
  change k ≤ selectedDegree H.incidence A v at hk
  simp [complexValues, restrict, Signature.normalizedResidual, hk, H.normalized]

theorem restrict_family (H : NormalizedInstance V E) (F : Finset Signature)
    (hF : ∀ v, H.signature v ∈ residualFamily F) (A : Finset E) (hA : A ⊆ H.edges) (v : V) :
    (H.restrict A hA).signature v ∈ residualFamily F := by
  apply residualFamily_closed F (hF v)
  refine ⟨0, selectedDegree H.incidence A v, ?_, (H.signature v).zero_pos, rfl⟩
  rw [H.arity_eq]
  simpa only [zero_add] using selectedDegree_mono H.incidence hA v

/-- The restricted zero-child is represented by an actual residual signature. -/
def zeroChild (H : NormalizedInstance V E) (e : E) : NormalizedInstance V E where
  incidence := H.incidence
  edges := H.edges.erase e
  signature v := (H.signature v).normalizedResidual 0
    (selectedDegree H.incidence (H.edges.erase e) v)
    (by rw [H.arity_eq]; simpa using selectedDegree_mono H.incidence (Finset.erase_subset e H.edges) v)
    (H.signature v).zero_pos
  arity_eq _ := rfl
  normalized v := (H.signature v).normalizedResidual_zero 0 _ _ _

@[simp] theorem zeroChild_edges (H : NormalizedInstance V E) (e : E) :
    (H.zeroChild e).edges = H.edges.erase e := rfl

theorem zeroChild_card_lt (H : NormalizedInstance V E) (e : E) (he : e ∈ H.edges) :
    (H.zeroChild e).edges.card < H.edges.card := Finset.card_erase_lt_of_mem he

/-- Structural survival depends solely on signature first entries. -/
def OneSurvives (H : NormalizedInstance V E) (e : E) : Prop :=
  ∀ v, H.incidence e v → 0 < (H.signature v).value 1

/-- Deleting a present edge removes one incident input at each endpoint. -/
theorem deletion_degree (H : NormalizedInstance V E) (e : E) (he : e ∈ H.edges) (v : V) :
    selectedDegree H.incidence (H.edges.erase e) v + (if H.incidence e v then 1 else 0) =
      (H.signature v).arity := by
  rw [H.arity_eq, ← selectedDegree_insert H.incidence e (H.edges.erase e)
    (Finset.notMem_erase e H.edges), Finset.insert_erase he]

/-- The normalized one-child is defined independently of the edge activity,
including at a zero base activity. -/
def oneChild (H : NormalizedInstance V E) (e : E) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) : NormalizedInstance V E where
  incidence := H.incidence
  edges := H.edges.erase e
  signature v := (H.signature v).normalizedResidual (if H.incidence e v then 1 else 0)
    (selectedDegree H.incidence (H.edges.erase e) v)
    (by have h := H.deletion_degree e he v; omega)
    (by split_ifs with hv; exact hs v hv; exact (H.signature v).zero_pos)
  arity_eq _ := rfl
  normalized v := (H.signature v).normalizedResidual_zero _ _ _ _

@[simp] theorem oneChild_edges (H : NormalizedInstance V E) (e : E)
    (he : e ∈ H.edges) (hs : H.OneSurvives e) :
    (H.oneChild e he hs).edges = H.edges.erase e := rfl

theorem zeroChild_family (H : NormalizedInstance V E) (F : Finset Signature)
    (hF : ∀ v, H.signature v ∈ residualFamily F) (e : E) (v : V) :
    (H.zeroChild e).signature v ∈ residualFamily F := by
  apply residualFamily_closed F (hF v)
  refine ⟨0, selectedDegree H.incidence (H.edges.erase e) v, ?_, (H.signature v).zero_pos, rfl⟩
  rw [H.arity_eq]
  simpa only [zero_add] using selectedDegree_mono H.incidence (Finset.erase_subset e H.edges) v

theorem oneChild_family (H : NormalizedInstance V E) (F : Finset Signature)
    (hF : ∀ v, H.signature v ∈ residualFamily F) (e : E)
    (he : e ∈ H.edges) (hs : H.OneSurvives e) (v : V) :
    (H.oneChild e he hs).signature v ∈ residualFamily F := by
  apply residualFamily_closed F (hF v)
  refine ⟨if H.incidence e v then 1 else 0, selectedDegree H.incidence (H.edges.erase e) v, ?_, ?_, rfl⟩
  · have hd := H.deletion_degree e he v
    omega
  · split_ifs with hv
    · exact hs v hv
    · exact (H.signature v).zero_pos

theorem zeroChild_realPartition (H : NormalizedInstance V E) (e : E) (x : E → ℝ) :
    (H.zeroChild e).toInstance.realPartition x =
      partition H.incidence (H.edges.erase e) (realValues H.signature) x := by
  apply partition_congr_signatures
  intro v k hk
  change k ≤ selectedDegree H.incidence (H.edges.erase e) v at hk
  simp [realValues, zeroChild, Signature.normalizedResidual, hk, H.normalized]

theorem zeroChild_complexPartition (H : NormalizedInstance V E) (e : E) (z : E → ℂ) :
    (H.zeroChild e).toInstance.complexPartition z =
      partition H.incidence (H.edges.erase e) (complexValues H.signature) z := by
  apply partition_congr_signatures
  intro v k hk
  change k ≤ selectedDegree H.incidence (H.edges.erase e) v at hk
  simp [complexValues, zeroChild, Signature.normalizedResidual, hk, H.normalized]

theorem oneChild_realPartition (H : NormalizedInstance V E) (e : E) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (x : E → ℝ) :
    (H.oneChild e he hs).toInstance.realPartition x =
      partition H.incidence (H.edges.erase e) (normalizedChildSignature H.incidence
        (realValues H.signature) e) x := by
  apply partition_congr_signatures
  intro v k hk
  change k ≤ selectedDegree H.incidence (H.edges.erase e) v at hk
  by_cases hv : H.incidence e v
  · simp [realValues, oneChild, Signature.normalizedResidual, normalizedChildSignature,
      hk, hv, Nat.add_comm]
  · simp [realValues, oneChild, Signature.normalizedResidual, normalizedChildSignature,
      hk, hv, H.normalized]

theorem oneChild_complexPartition (H : NormalizedInstance V E) (e : E) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (z : E → ℂ) :
    (H.oneChild e he hs).toInstance.complexPartition z =
      partition H.incidence (H.edges.erase e) (normalizedChildSignature H.incidence
        (complexValues H.signature) e) z := by
  apply partition_congr_signatures
  intro v k hk
  change k ≤ selectedDegree H.incidence (H.edges.erase e) v at hk
  by_cases hv : H.incidence e v
  · simp [complexValues, oneChild, Signature.normalizedResidual, normalizedChildSignature,
      hk, hv, Nat.add_comm]
  · simp [complexValues, oneChild, Signature.normalizedResidual, normalizedChildSignature,
      hk, hv, H.normalized]

/-- The exact normalized deletion recursion for actual residual child instances. -/
theorem complexPartition_deletion (H : NormalizedInstance V E) (e : E)
    (he : e ∈ H.edges) (hs : H.OneSurvives e) (z : E → ℂ) :
    H.toInstance.complexPartition z = (H.zeroChild e).toInstance.complexPartition z +
      z e * childCoefficient H.incidence (complexValues H.signature) e *
        (H.oneChild e he hs).toInstance.complexPartition z := by
  rw [H.zeroChild_complexPartition, H.oneChild_complexPartition]
  exact partition_normalized_deletion H.incidence H.edges _ z e he
    (fun v hv => by simpa only [complexValues, Complex.ofReal_ne_zero] using (hs v hv).ne')

theorem realPartition_deletion (H : NormalizedInstance V E) (e : E)
    (he : e ∈ H.edges) (hs : H.OneSurvives e) (x : E → ℝ) :
    H.toInstance.realPartition x = (H.zeroChild e).toInstance.realPartition x +
      x e * childCoefficient H.incidence (realValues H.signature) e *
        (H.oneChild e he hs).toInstance.realPartition x := by
  rw [H.zeroChild_realPartition, H.oneChild_realPartition]
  exact partition_normalized_deletion H.incidence H.edges _ x e he
    (fun v hv => (hs v hv).ne')

/-- Actual normalized child monotonicity, now derived from log-concavity. -/
theorem child_partition_le (H : NormalizedInstance V E) (e : E)
    (he : e ∈ H.edges) (hs : H.OneSurvives e) (x : E → ℝ)
    (hx : ∀ a ∈ H.edges.erase e, 0 ≤ x a) :
    (H.oneChild e he hs).toInstance.realPartition x ≤
      (H.zeroChild e).toInstance.realPartition x := by
  rw [H.oneChild_realPartition, H.zeroChild_realPartition]
  apply CI2ZF.Holant.child_partition_le H.incidence H.edges (realValues H.signature) x e
    (fun v k => (H.signature v).nonneg k) hx
  intro v k hv _
  exact (H.signature v).first_shift_le (H.normalized v) (hs v hv) k

/-- Non-surviving one-children have an identically zero unnormalized polynomial. -/
theorem shifted_partition_zero (H : NormalizedInstance V E) (e : E)
    (hs : ¬ H.OneSurvives e) (z : E → ℂ) :
    partition H.incidence (H.edges.erase e)
      (shiftedSignature H.incidence (complexValues H.signature) e) z = 0 := by
  simp only [OneSurvives, not_forall, not_lt] at hs
  obtain ⟨v, hv, hf⟩ := hs
  have hf0 : (H.signature v).value 1 = 0 := le_antisymm hf ((H.signature v).nonneg 1)
  apply CI2ZF.Holant.shifted_partition_zero
  refine ⟨v, hv, fun k => ?_⟩
  simpa only [complexValues, Complex.ofReal_eq_zero] using
    (H.signature v).zero_of_zero_le hf0 (show 1 ≤ k + 1 by omega)

theorem complexPartition_dead_edge (H : NormalizedInstance V E) (e : E)
    (he : e ∈ H.edges) (hs : ¬ H.OneSurvives e) (z : E → ℂ) :
    H.toInstance.complexPartition z = (H.zeroChild e).toInstance.complexPartition z := by
  rw [H.zeroChild_complexPartition]
  unfold Instance.complexPartition
  rw [partition_deletion H.incidence H.edges _ z e he, H.shifted_partition_zero e hs,
    mul_zero, add_zero]

/-- Empty normalized instances have partition one, including isolated vertices. -/
@[simp] theorem complexPartition_empty (H : NormalizedInstance V E) (hE : H.edges = ∅)
    (z : E → ℂ) : H.toInstance.complexPartition z = 1 := by
  unfold Instance.complexPartition
  rw [hE, partition_empty]
  simp [complexValues, H.normalized]

/-- A separated component decomposition remains entirely within the actual
normalized residual class. -/
theorem complexPartition_components (H : NormalizedInstance V E) (I O : Finset E)
    (hI : I ⊆ H.edges) (hO : O ⊆ H.edges) (hcover : I ∪ O = H.edges)
    (hd : Disjoint I O) (hsep : EdgeSeparated H.incidence I O) (z : E → ℂ) :
    H.toInstance.complexPartition z =
      (H.restrict I hI).toInstance.complexPartition z *
        (H.restrict O hO).toInstance.complexPartition z := by
  rw [H.restrict_complexPartition, H.restrict_complexPartition]
  unfold Instance.complexPartition
  rw [← hcover]
  exact partition_disjoint_factorization H.incidence I O _ z hd hsep
    (fun v => by simp [complexValues, H.normalized])

/-- A structurally surviving shell produces actual normalized residual
signatures of exactly the exterior degrees. -/
def exteriorInstance (H : NormalizedInstance V E) (O ξ : Finset E)
    (hbound : ∀ v, selectedDegree H.incidence ξ v + selectedDegree H.incidence O v ≤
      (H.signature v).arity)
    (hξ : Feasible H.incidence (realValues H.signature) ξ) : NormalizedInstance V E where
  incidence := H.incidence
  edges := O
  signature v := (H.signature v).normalizedResidual (selectedDegree H.incidence ξ v)
    (selectedDegree H.incidence O v) (hbound v) (hξ v)
  arity_eq _ := rfl
  normalized v := (H.signature v).normalizedResidual_zero _ _ _ _

theorem exteriorInstance_family (H : NormalizedInstance V E) (F : Finset Signature)
    (hF : ∀ v, H.signature v ∈ residualFamily F) (O ξ : Finset E)
    (hbound : ∀ v, selectedDegree H.incidence ξ v + selectedDegree H.incidence O v ≤
      (H.signature v).arity)
    (hξ : Feasible H.incidence (realValues H.signature) ξ) (v : V) :
    (H.exteriorInstance O ξ hbound hξ).signature v ∈ residualFamily F := by
  apply residualFamily_closed F (hF v)
  exact ⟨selectedDegree H.incidence ξ v, selectedDegree H.incidence O v, hbound v, hξ v, rfl⟩

/-- The arity bounds for the exterior follow from disjointness and the actual
parent degrees, without any extra structural assumption. -/
theorem exterior_bound (H : NormalizedInstance V E) (O ξ : Finset E)
    (hO : O ⊆ H.edges) (hξ : ξ ⊆ H.edges) (hd : Disjoint ξ O) (v : V) :
    selectedDegree H.incidence ξ v + selectedDegree H.incidence O v ≤
      (H.signature v).arity := by
  rw [H.arity_eq, ← selectedDegree_union H.incidence ξ O hd]
  exact selectedDegree_mono H.incidence (Finset.union_subset hξ hO) v

/-- The finite-sum exterior is the polynomial of an actual residual instance;
neutral isolated-vertex factors agree with its normalized zero entry. -/
theorem exteriorInstance_complexPartition (H : NormalizedInstance V E) (O ξ : Finset E)
    (hbound : ∀ v, selectedDegree H.incidence ξ v + selectedDegree H.incidence O v ≤
      (H.signature v).arity)
    (hξ : Feasible H.incidence (realValues H.signature) ξ) (z : E → ℂ) :
    (H.exteriorInstance O ξ hbound hξ).toInstance.complexPartition z =
      partition H.incidence O (exteriorSignature H.incidence O ξ (complexValues H.signature)) z := by
  apply partition_congr_signatures
  intro v k hk
  change k ≤ selectedDegree H.incidence O v at hk
  by_cases hv : ExteriorVertex H.incidence O v
  · simp [complexValues, exteriorInstance, Signature.normalizedResidual, exteriorSignature, hk, hv]
  · have hdeg := outside_degree_zero H.incidence O O (Finset.Subset.refl O) v hv
    have hk0 : k = 0 := by omega
    subst k
    simp [complexValues, exteriorInstance, Signature.normalizedResidual, exteriorSignature,
      hv, show (H.signature v).value (selectedDegree H.incidence ξ v) ≠ 0 from (hξ v).ne']

end NormalizedInstance
end
end CI2ZF.Holant
