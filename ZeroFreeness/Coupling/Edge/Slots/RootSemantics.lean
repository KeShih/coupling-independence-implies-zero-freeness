import ZeroFreeness.Coupling.Edge.Slots.Conditioning
import ZeroFreeness.Potts.Model.RootChildren

/-! The root-excluded conditional law is the actual enlarged-pinning child,
on the common original-vertex subtype used by the analytic transfer. -/

namespace ZeroFreeness.Appendix.Edge
open PottsCI PottsCI.FinDist ZeroFreeness.Potts FiniteLaw FiniteSystem EndpointGeometry
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
variable {V C : Type*} [Fintype V] [Fintype C] [Nonempty C]
local instance (priority := 2000) : DecidableEq V := Classical.decEq V
local instance (priority := 2000) : DecidableEq C := Classical.decEq C

lemma parentWeight_childToParent (τ : PartialColouring V C) (G : SimpleGraph V)
    (r : τ.FreeVertex) (c : C) (x : ℝ) (η : RootRemaining τ r → C) :
    (τ.toPinningData G).weight x (childToParent τ r c η) =
      x ^ τ.boundaryCount G r c * (rootChildData τ G r c).weight x η := by
  change ((pinVertex τ r c).FreeVertex → C) at η
  change (τ.toPinningData G).weight x (childToParent τ r c η) =
    x ^ τ.boundaryCount G r c * ((pinVertex τ r c).toPinningData G).weight x η
  rw [τ.childWeight_eq_pow, (pinVertex τ r c).childWeight_eq_pow]
  rw [← pow_add, root_exponent_split, childToParent_root, pow_add,
    ← child_exponent_pinVertex, pow_add]

lemma parentWeight_coordinate_sum (τ : PartialColouring V C) (G : SimpleGraph V)
    (r : τ.FreeVertex) (c : C) (x : ℝ) :
    (∑ σ : τ.FreeVertex → C, if σ r = c then (τ.toPinningData G).weight x σ else 0) =
      x ^ τ.boundaryCount G r c * (rootChildData τ G r c).partition x := by
  rw [← Finset.sum_filter, Finset.sum_subtype _ (p := fun σ : τ.FreeVertex → C => σ r = c)
    (by simp)]
  rw [← Fintype.sum_equiv (childConfigEquiv τ r c)
    (fun η => (τ.toPinningData G).weight x (childToParent τ r c η))
    (fun σ => (τ.toPinningData G).weight x σ.val) (fun _ => rfl)]
  simp only [parentWeight_childToParent, ← Finset.mul_sum]
  rfl

lemma childToParent_eq_iff (τ : PartialColouring V C) (r : τ.FreeVertex) (c : C)
    (η : RootRemaining τ r → C) (σ : τ.FreeVertex → C) :
    σ = childToParent τ r c η ↔ σ r = c ∧ η = parentToChild τ r c σ := by
  constructor
  · rintro rfl
    exact ⟨childToParent_root τ r c η, ((childConfigEquiv τ r c).left_inv η).symm⟩
  · rintro ⟨hr, rfl⟩
    exact (congrArg Subtype.val ((childConfigEquiv τ r c).right_inv ⟨σ, hr⟩)).symm

lemma mapLaw_childToParent_w (τ : PartialColouring V C) (r : τ.FreeVertex) (c : C)
    (μ : FinDist (RootRemaining τ r → C)) (σ : τ.FreeVertex → C) :
    (ZeroFreeness.mapLaw μ (childToParent τ r c)).w σ =
      if σ r = c then μ.w (parentToChild τ r c σ) else 0 := by
  unfold ZeroFreeness.mapLaw FinDist.bind
  simp only [FinDist.pure, childToParent_eq_iff]
  by_cases he : σ r = c <;> simp [he]

lemma parentGibbs_coordinate_mass (τ : PartialColouring V C) (G : SimpleGraph V)
    (r : τ.FreeVertex) (c : C) (x : ℝ) (hx : 0 < x) :
    eventMass ((τ.toPinningData G).gibbs x hx.le ((τ.toPinningData G).partition_pos_of_parameter_pos hx))
      (fun σ => σ r = c) =
      x ^ τ.boundaryCount G r c * (rootChildData τ G r c).partition x /
        (τ.toPinningData G).partition x := by
  rw [← parentWeight_coordinate_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : σ r = c <;> simp [PinningData.gibbs, h]

lemma parentGibbs_coordinate_pos (τ : PartialColouring V C) (G : SimpleGraph V)
    (r : τ.FreeVertex) (c : C) (x : ℝ) (hx : 0 < x) :
    0 < eventMass ((τ.toPinningData G).gibbs x hx.le ((τ.toPinningData G).partition_pos_of_parameter_pos hx))
      (fun σ => σ r = c) := by
  rw [parentGibbs_coordinate_mass τ G r c x hx]
  exact div_pos (mul_pos (pow_pos hx _) ((rootChildData τ G r c).partition_pos_of_parameter_pos hx))
    ((τ.toPinningData G).partition_pos_of_parameter_pos hx)

theorem conditional_parentGibbs (τ : PartialColouring V C) (G : SimpleGraph V)
    (r : τ.FreeVertex) (c : C) (x : ℝ) (hx : 0 < x) :
    conditional ((τ.toPinningData G).gibbs x hx.le ((τ.toPinningData G).partition_pos_of_parameter_pos hx))
      (fun σ => σ r = c) =
      ZeroFreeness.mapLaw ((rootChildData τ G r c).gibbs x hx.le
        ((rootChildData τ G r c).partition_pos_of_parameter_pos hx)) (childToParent τ r c) := by
  apply FinDist.ext
  funext σ
  rw [conditional_w _ _ (parentGibbs_coordinate_pos τ G r c x hx),
    parentGibbs_coordinate_mass τ G r c x hx, mapLaw_childToParent_w]
  by_cases hr : σ r = c
  · rw [if_pos hr, if_pos hr]
    have hrestore : childToParent τ r c (parentToChild τ r c σ) = σ :=
      congrArg Subtype.val ((childConfigEquiv τ r c).right_inv ⟨σ, hr⟩)
    have hw := parentWeight_childToParent τ G r c x (parentToChild τ r c σ)
    rw [hrestore] at hw
    change (τ.toPinningData G).weight x σ / (τ.toPinningData G).partition x /
      (x ^ τ.boundaryCount G r c * (rootChildData τ G r c).partition x /
        (τ.toPinningData G).partition x) =
      (rootChildData τ G r c).weight x (parentToChild τ r c σ) /
        (rootChildData τ G r c).partition x
    rw [hw, div_div_div_cancel_right₀ ((τ.toPinningData G).partition_pos_of_parameter_pos hx).ne',
      mul_div_mul_left _ _ (pow_pos hx _).ne']
  · simp only [if_neg hr, zero_div]

def rootRemainderEquiv (τ : PartialColouring V C) (r : τ.FreeVertex) :
    RootRemaining τ r ≃ {u : τ.FreeVertex // u ≠ r} where
  toFun u := ⟨rootRemainingToFree τ r u, fun hu => u.property
    (Finset.mem_insert.mpr (Or.inl (congrArg Subtype.val hu)))⟩
  invFun u := ⟨u.val.val, fun h => (Finset.mem_insert.mp h).elim
    (fun hr => u.property (Subtype.ext hr)) u.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def canonicalRemainingConfig (τ : PartialColouring V C) (r : τ.FreeVertex)
    (σ : {u : τ.FreeVertex // u ≠ r} → C) : RootRemaining τ r → C :=
  fun u => σ (rootRemainderEquiv τ r u)

lemma ham_canonicalRemainingConfig (τ : PartialColouring V C) (r : τ.FreeVertex)
    (σ η : {u : τ.FreeVertex // u ≠ r} → C) :
    ham (canonicalRemainingConfig τ r σ) (canonicalRemainingConfig τ r η) = ham σ η := by
  rw [ham_eq_sum, ham_eq_sum]
  exact Fintype.sum_equiv (rootRemainderEquiv τ r) _ _ (fun _ => rfl)

theorem rootExcludedColourLaw_map_eq_child (τ : PartialColouring V C) (G : SimpleGraph V)
    (r : τ.FreeVertex) (c : C) (x : ℝ) (hx : 0 < x) :
    ZeroFreeness.mapLaw (rootExcludedColourLaw ((τ.toPinningData G).gibbs x hx.le
      ((τ.toPinningData G).partition_pos_of_parameter_pos hx)) r c) (canonicalRemainingConfig τ r) =
      (rootChildData τ G r c).gibbs x hx.le
        ((rootChildData τ G r c).partition_pos_of_parameter_pos hx) := by
  rw [rootExcludedColourLaw, conditional_parentGibbs τ G r c x hx,
    ZeroFreeness.mapLaw_comp, ZeroFreeness.mapLaw_comp]
  have heq : (fun σ : RootRemaining τ r → C =>
      canonicalRemainingConfig τ r (restrictConfig r (childToParent τ r c σ))) = id := by
    funext σ
    exact (childConfigEquiv τ r c).left_inv σ
  rw [heq]
  apply FinDist.ext
  funext σ
  simp [ZeroFreeness.mapLaw, FinDist.bind, FinDist.pure]

theorem W_rootChildren_le_rootExcluded (τ : PartialColouring V C) (G : SimpleGraph V)
    (r : τ.FreeVertex) (c d : C) (x : ℝ) (hx : 0 < x) :
    W ham ((rootChildData τ G r c).gibbs x hx.le
      ((rootChildData τ G r c).partition_pos_of_parameter_pos hx))
      ((rootChildData τ G r d).gibbs x hx.le
        ((rootChildData τ G r d).partition_pos_of_parameter_pos hx)) ≤
      W ham (rootExcludedColourLaw ((τ.toPinningData G).gibbs x hx.le
        ((τ.toPinningData G).partition_pos_of_parameter_pos hx)) r c)
        (rootExcludedColourLaw ((τ.toPinningData G).gibbs x hx.le
          ((τ.toPinningData G).partition_pos_of_parameter_pos hx)) r d) := by
  rw [← rootExcludedColourLaw_map_eq_child τ G r c x hx,
    ← rootExcludedColourLaw_map_eq_child τ G r d x hx]
  have h := ZeroFreeness.W_mapLaw_le
    (μ := rootExcludedColourLaw ((τ.toPinningData G).gibbs x hx.le
      ((τ.toPinningData G).partition_pos_of_parameter_pos hx)) r c)
    (ν := rootExcludedColourLaw ((τ.toPinningData G).gibbs x hx.le
      ((τ.toPinningData G).partition_pos_of_parameter_pos hx)) r d)
    (canonicalRemainingConfig τ r) (canonicalRemainingConfig τ r)
    ham ham_nonneg
  simpa only [ham_canonicalRemainingConfig] using h

end
end ZeroFreeness.Appendix.Edge
