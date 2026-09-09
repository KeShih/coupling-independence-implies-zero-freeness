import CI2ZF.Appendix.GirthHeatBath

/-! Explicit conditional averaging over arbitrary sets of leaves, and
its identification from the joint fixed-point equations of the actual
leaf heat-bath projections. -/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators InnerProductSpace
open PottsCI Finset

noncomputable section
attribute [local instance] Classical.propDecidable

variable {C D : Type*} [Fintype C] [Fintype D]

theorem expectReal_comm {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (μ : FinDist Ω) (ν : FinDist Λ) (f : Ω → Λ → ℝ) :
    expectReal μ (fun ω => expectReal ν (f ω)) =
      expectReal ν (fun t => expectReal μ (fun ω => f ω t)) := by
  unfold expectReal
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem productProjection_stationary (p : D → FinDist C) (i : D) (f : (D → C) → ℝ) :
    expectReal (productLaw p) (productProjection p i f) = expectReal (productLaw p) f := by
  have h := productProjection_selfAdjoint p i f (fun _ => 1)
  have he : productProjection p i (fun _ => 1) = (fun _ => 1) := by
    funext σ
    exact expectReal_const (p i) 1
  simpa only [he, mul_one] using h

def retainCoordinates (J : Finset D) (σ τ : D → C) : D → C :=
  fun i => if i ∈ J then σ i else τ i

omit [Fintype C] in
theorem retainCoordinates_univ (σ τ : D → C) : retainCoordinates Finset.univ σ τ = σ := by
  funext i
  simp [retainCoordinates]

omit [Fintype C] [Fintype D] in
theorem retainCoordinates_empty (σ τ : D → C) : retainCoordinates ∅ σ τ = τ := by
  funext i
  simp [retainCoordinates]

omit [Fintype C] [Fintype D] in
theorem retainCoordinates_erase_update (J : Finset D) {i : D} (hi : i ∈ J)
    (σ τ : D → C) (t : C) :
    retainCoordinates J (Function.update σ i t) τ =
      retainCoordinates (J.erase i) σ (Function.update τ i t) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [retainCoordinates, hi]
  · simp [retainCoordinates, hji]

def partialProductProjection (p : D → FinDist C) (J : Finset D)
    (f : (D → C) → ℝ) (σ : D → C) : ℝ :=
  expectReal (productLaw p) (fun τ => f (retainCoordinates J σ τ))

theorem partialProductProjection_univ (p : D → FinDist C) (f : (D → C) → ℝ) :
    partialProductProjection p Finset.univ f = f := by
  funext σ
  unfold partialProductProjection
  simp only [retainCoordinates_univ]
  exact expectReal_const _ _

theorem productProjection_partial (p : D → FinDist C) (J : Finset D)
    {i : D} (hi : i ∈ J) (f : (D → C) → ℝ) :
    productProjection p i (partialProductProjection p J f) =
      partialProductProjection p (J.erase i) f := by
  funext σ
  unfold productProjection partialProductProjection
  rw [expectReal_comm]
  simp_rw [retainCoordinates_erase_update J hi]
  exact productProjection_stationary p i (fun τ => f (retainCoordinates (J.erase i) σ τ))

namespace ConditionalStar

variable [DecidableEq C] (S : ConditionalStar C D)

def partialProjection (J : Finset D) (f : C × (D → C) → ℝ) (σ : C × (D → C)) : ℝ :=
  partialProductProjection (fun i => edgeChannel (S.cavity i) S.s S.s_le_one σ.1
    (S.edge_positive i σ.1)) J (fun τ => f (σ.1, τ)) σ.2

theorem partialProjection_univ (f : C × (D → C) → ℝ) :
    S.partialProjection Finset.univ f = f := by
  funext σ
  exact congrFun (partialProductProjection_univ _ (fun τ => f (σ.1, τ))) σ.2

theorem leafProjection_partial (J : Finset D) {i : D} (hi : i ∈ J)
    (f : C × (D → C) → ℝ) :
    S.leafProjection i (S.partialProjection J f) = S.partialProjection (J.erase i) f := by
  funext σ
  exact congrFun (productProjection_partial _ J hi (fun τ => f (σ.1, τ))) σ.2

theorem supported_partial_of_fixed (A : Finset D) (z : SupportedSpace S.jointLaw)
    (hz : ∀ i ∈ A, (S.leafHeatBath i).operator z = z) :
    supportedEmbed S.jointLaw (S.partialProjection (Finset.univ \ A)
      (supportedRepresent S.jointLaw z)) = z := by
  induction A using Finset.induction_on with
  | empty =>
    simp only [Finset.sdiff_empty, S.partialProjection_univ, supportedEmbed_represent]
  | @insert i A hi ih =>
    have hA := ih (fun j hj => hz j (Finset.mem_insert_of_mem hj))
    have h := congrArg (S.leafHeatBath i).operator hA
    rw [SupportedOperator.intertwine, hz i (Finset.mem_insert_self i A)] at h
    change supportedEmbed S.jointLaw (S.leafProjection i
      (S.partialProjection (Finset.univ \ A) (supportedRepresent S.jointLaw z))) = z at h
    rw [S.leafProjection_partial _ (by simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]; exact hi)] at h
    have he : (Finset.univ \ A).erase i = Finset.univ \ insert i A := by ext j; simp
    rwa [he] at h

theorem supported_partial_eq_self (J : Finset D) (z : SupportedSpace S.jointLaw)
    (hz : ∀ i, i ∉ J → (S.leafHeatBath i).operator z = z) :
    supportedEmbed S.jointLaw (S.partialProjection J (supportedRepresent S.jointLaw z)) = z := by
  have h := S.supported_partial_of_fixed (Finset.univ \ J) z
    (fun i hi => hz i (Finset.mem_sdiff.mp hi).2)
  have he : Finset.univ \ (Finset.univ \ J) = J := by ext i; simp
  rwa [he] at h

def rootAverage (f : C × (D → C) → ℝ) (c : C) : ℝ :=
  expectReal (S.leafChannel c) (fun τ => f (c, τ))

theorem partialProjection_empty (f : C × (D → C) → ℝ) :
    S.partialProjection ∅ f = (fun σ => S.rootAverage f σ.1) := by
  funext σ
  unfold partialProjection partialProductProjection rootAverage leafChannel
  simp only [retainCoordinates_empty]

theorem supported_root_of_fixed (z : SupportedSpace S.jointLaw)
    (hz : ∀ i, (S.leafHeatBath i).operator z = z) :
    supportedEmbed S.jointLaw (fun σ => S.rootAverage (supportedRepresent S.jointLaw z) σ.1) = z := by
  have h := S.supported_partial_eq_self ∅ z (fun i _ => hz i)
  rwa [S.partialProjection_empty] at h

def singletonAverage (f : C × (D → C) → ℝ) (i : D) (c t : C) : ℝ :=
  expectReal (S.leafChannel c) (fun τ => f (c, Function.update τ i t))

theorem partialProjection_singleton (f : C × (D → C) → ℝ) (i : D) :
    S.partialProjection {i} f = (fun σ => S.singletonAverage f i σ.1 (σ.2 i)) := by
  funext σ
  unfold partialProjection partialProductProjection singletonAverage leafChannel
  apply congrArg (expectReal _)
  funext τ
  congr 1
  funext j
  by_cases h : j = i
  · subst j; simp [retainCoordinates]
  · simp [retainCoordinates, h ]

theorem supported_singleton_of_fixed (z : SupportedSpace S.jointLaw) (i : D)
    (hz : ∀ j, j ≠ i → (S.leafHeatBath j).operator z = z) :
    supportedEmbed S.jointLaw (fun σ => S.singletonAverage (supportedRepresent S.jointLaw z)
      i σ.1 (σ.2 i)) = z := by
  have h := S.supported_partial_eq_self {i} z (fun j hj => hz j (by simpa using hj))
  rwa [S.partialProjection_singleton] at h

end ConditionalStar
end
end CI2ZF.Appendix.Girth
