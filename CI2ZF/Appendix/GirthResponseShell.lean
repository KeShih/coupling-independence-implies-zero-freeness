import CI2ZF.Appendix.GirthResponseSeparatorSource
import CI2ZF.Appendix.GirthDoobResponseBounds

/-! The full conditional shell source is controlled by the induction
hypothesis through actual successively pinned residual graphs. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI CI2ZF.Potts CI2ZF.Potts.Separator
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
universe u v
variable {U S O : Type u} {C : Type v} [Fintype U] [Fintype S] [Fintype O] [Fintype C]
  [DecidableEq U] [DecidableEq S] [DecidableEq O] [DecidableEq C] [Nonempty C]

namespace InsertionGraph
variable (I : PinningData (Vertex U S O) C) (x : ℝ) (hx : 0 < x)

theorem shellSource_variance_of_response {Δ n : ℕ} {χ B A R : ℝ}
    (hglobal : ResponseBoundsUpTo.{u,v} C Δ χ B A R n)
    (hi : Independent I) (hs : Separates I) (c₀ : C)
    (hsize : Fintype.card (Vertex U S O) ≤ n) (hd : I.DegreeBound Δ)
    (hg : 5 ≤ I.graph.egirth) (hx1 : x < 1) (F : WeightedSource I χ) :
    variance (model I x hx c₀ (I.partition_pos_of_parameter_pos hx)).shell
      (F.shellSource (model I x hx c₀ (I.partition_pos_of_parameter_pos hx))) ≤
        A ^ 2 * ∑ w : S, F.weight (Sum.inr (Sum.inl w)) ^ 2 := by
  let js : List S := (Finset.univ : Finset S).toList
  let ks : List (Vertex U S O) := js.map (fun w => Sum.inr (Sum.inl w))
  have hcover : ∀ w, w ∈ js := by intro w; exact Finset.mem_toList.mpr (Finset.mem_univ w)
  have hnodup : ks.Nodup := by
    apply (Finset.nodup_toList (Finset.univ : Finset S)).map
    intro w z h
    exact Sum.inl.inj (Sum.inr.inj h)
  have hscore := responseBoundsUpTo_boundedScores hglobal I hsize hd hg x hx hx1 F ks hnodup
  let M := model I x hx c₀ (I.partition_pos_of_parameter_pos hx)
  have hk : Doob.pullScores (coloringEquiv (U := U) (S := S) (O := O) (C := C))
      (Doob.weightedCoordinateKeys js (fun w => F.weight (Sum.inr (Sum.inl w)))) =
      Doob.vertexKeys ks F.weight := by
    simp only [Doob.pullScores, Doob.weightedCoordinateKeys, Doob.vertexKeys, ks,
      List.map_map, Function.comp_def]
    rfl
  have hf : (fun σ : Vertex U S O → C => F.splitSource (coloringEquiv σ)) = F.observable :=
    funext F.splitSource_coloringEquiv
  have hmodel : Doob.BoundedScores (1-x) (A ^ 2) F.splitSource
      (Doob.weightedCoordinateKeys js (fun w => F.weight (Sum.inr (Sum.inl w)))) M.law := by
    rw [← law_eq_model I x hx hi hs c₀ (I.partition_pos_of_parameter_pos hx)]
    change Doob.BoundedScores _ _ _ _ (mapLaw (positiveLaw I x hx) coloringEquiv)
    rw [Doob.boundedScores_map, hk, hf]
    exact hscore
  have h := Doob.variance_shellSource_le M js hcover F.firstTerms F.shellTerms F.exteriorTerms
    (fun w => F.weight (Sum.inr (Sum.inl w))) (sub_nonneg.mpr hx1.le) (by linarith) hmodel
  simpa only [js, Finset.sum_map_toList, WeightedSource.shellSource, M] using h

theorem shellSource_variance_radius_two {Δ n : ℕ} {χ B A R D a : ℝ}
    (hglobal : ResponseBoundsUpTo.{u,v} C Δ χ B A R n)
    (hi : Independent I) (hs : Separates I) (c₀ : C)
    (hsize : Fintype.card (Vertex U S O) ≤ n) (hd : I.DegreeBound Δ)
    (hg : 5 ≤ I.graph.egirth) (hx1 : x < 1) (F : WeightedSource I χ)
    (ha : 0 ≤ a) (hcard : (Fintype.card S : ℝ) ≤ D ^ 2)
    (hweight : ∀ w : S, F.weight (Sum.inr (Sum.inl w)) ≤ χ ^ 2 * a) :
    variance (model I x hx c₀ (I.partition_pos_of_parameter_pos hx)).shell
      (F.shellSource (model I x hx c₀ (I.partition_pos_of_parameter_pos hx))) ≤
        (D * χ ^ 2 * a * A) ^ 2 := by
  have hsum : (∑ w : S, F.weight (Sum.inr (Sum.inl w)) ^ 2) ≤ D ^ 2 * (χ ^ 2 * a) ^ 2 := by
    calc
      _ ≤ ∑ _w : S, (χ ^ 2 * a) ^ 2 := Finset.sum_le_sum fun w _ =>
        (sq_le_sq₀ (F.positive _).le (by positivity)).mpr (hweight w)
      _ = (Fintype.card S : ℝ) * (χ ^ 2 * a) ^ 2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
  calc
    _ ≤ A ^ 2 * ∑ w : S, F.weight (Sum.inr (Sum.inl w)) ^ 2 :=
      shellSource_variance_of_response I x hx hglobal hi hs c₀ hsize hd hg hx1 F
    _ ≤ A ^ 2 * (D ^ 2 * (χ ^ 2 * a) ^ 2) := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := by ring

end InsertionGraph
end
end CI2ZF.Appendix.Girth
