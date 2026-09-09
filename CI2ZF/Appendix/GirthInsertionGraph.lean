import CI2ZF.Appendix.GirthInsertionBalance
import CI2ZF.Separator

/-! The two-layer product model is the actual graph Gibbs distribution.
Only the stated graph separation and independence of the first layer are
used; edges within the shell and exterior are retained. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI
open CI2ZF.Potts.Separator
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {U S O C : Type*} [Fintype U] [Fintype S] [Fintype O] [Fintype C]
  [DecidableEq U] [DecidableEq S] [DecidableEq O] [DecidableEq C] [Nonempty C]

namespace InsertionGraph
variable (I : PinningData (Vertex U S O) C) (x : ℝ) (hx : 0 < x)

def Independent : Prop := ∀ u v, ¬ I.graph.Adj (Sum.inl u) (Sum.inl v)

include hx in
theorem positive_sitePartition (σ : Vertex U S O → C) (v : Vertex U S O) :
    0 < GraphHeatBath.sitePartition I x σ v := by
  apply Finset.sum_pos
  · intro c _
    exact pow_pos hx _
  · exact Finset.univ_nonempty

def cavity (c₀ : C) (ξ : S → C) (u : U) : FinDist C :=
  GraphHeatBath.siteLaw I x hx.le (positive_sitePartition I x hx)
    (join (fun _ => c₀) ξ (fun _ => c₀)) (Sum.inl u)

theorem cavity_pos (c₀ : C) (ξ : S → C) (u : U) (c : C) : 0 < (cavity I x hx c₀ ξ u).w c :=
  div_pos (pow_pos hx _) (positive_sitePartition I x hx _ _)

theorem siteCount_join (hi : Independent I) (hs : Separates I)
    (α β : U → C) (ξ : S → C) (o t : O → C) (u : U) (c : C) :
    GraphHeatBath.siteCount I (join α ξ o) (Sum.inl u) c =
      GraphHeatBath.siteCount I (join β ξ t) (Sum.inl u) c := by
  unfold GraphHeatBath.siteCount
  congr 2
  apply Finset.filter_congr
  intro v hv
  have hadj : I.graph.Adj (Sum.inl u) v := by simpa using hv
  rcases v with v | v | v
  · exact (hi u v hadj).elim
  · rfl
  · exact (hs u v hadj).elim

theorem siteLaw_join (hi : Independent I) (hs : Separates I)
    (c₀ : C) (α : U → C) (ξ : S → C) (o : O → C) (u : U) :
    GraphHeatBath.siteLaw I x hx.le (positive_sitePartition I x hx) (join α ξ o) (Sum.inl u) =
      cavity I x hx c₀ ξ u := by
  apply FinDist.ext
  funext c
  simp only [cavity, GraphHeatBath.siteLaw, GraphHeatBath.sitePartition, GraphHeatBath.siteWeight,
    siteCount_join I hi hs α (fun _ => c₀) ξ o (fun _ => c₀)]

theorem join_update (α : U → C) (ξ : S → C) (o : O → C) (u : U) (c : C) :
    join (Function.update α u c) ξ o = Function.update (join α ξ o) (Sum.inl u) c := by
  funext v
  rcases v with v | v | v
  · by_cases hv : v = u
    · subst v
      simp [join]
    · simp [join, hv]
  · simp [join]
  · simp [join]

def law (hZ : 0 < I.partition x) : FinDist ((S → C) × ((U → C) × (O → C))) :=
  mapLaw (I.gibbs x hx.le hZ) coloringEquiv

theorem law_weight (hZ : 0 < I.partition x) (ξ : S → C) (α : U → C) (o : O → C) :
    (law I x hx hZ).w (ξ,(α,o)) = (I.gibbs x hx.le hZ).w (join α ξ o) := by
  rw [law, CI2ZF.mapLaw_equiv_w]
  rfl

theorem localBalance (hi : Independent I) (hs : Separates I) (c₀ : C)
    (hZ : 0 < I.partition x) :
    InsertionBalance.LocalBalance (law I x hx hZ) (cavity I x hx c₀) := by
  intro ξ α o u c
  rw [law_weight, law_weight, join_update]
  have h := GraphHeatBath.gibbs_swap_weight I x hx.le (positive_sitePartition I x hx)
    hZ (join α ξ o) (Sum.inl u) c
  rw [← join_update, siteLaw_join I x hx hi hs c₀, siteLaw_join I x hx hi hs c₀] at h
  rw [join_update] at h
  exact h

theorem shell_positive (hZ : 0 < I.partition x) (ξ : S → C) :
    0 < (InsertionBalance.shellLaw (law I x hx hZ)).w ξ := by
  apply Finset.sum_pos
  · intro α _
    apply Finset.sum_pos
    · intro o _
      rw [law_weight]
      exact div_pos (I.weight_pos hx _) hZ
    · exact Finset.univ_nonempty
  · exact Finset.univ_nonempty

def model (c₀ : C) (hZ : 0 < I.partition x) : InsertionModel (S → C) U (O → C) C :=
  InsertionBalance.model (law I x hx hZ) (cavity I x hx c₀) (shell_positive I x hx hZ)

/-- Exact second-layer disintegration of the original finite Gibbs law.
The shell marginal is arbitrary and the exterior graph is untouched. -/
theorem law_eq_model (hi : Independent I) (hs : Separates I) (c₀ : C)
    (hZ : 0 < I.partition x) : law I x hx hZ = (model I x hx c₀ hZ).law :=
  InsertionBalance.law_eq_model _ _ (cavity_pos I x hx c₀)
    (localBalance I x hx hi hs c₀ hZ) (shell_positive I x hx hZ)

end InsertionGraph
end
end CI2ZF.Appendix.Girth
