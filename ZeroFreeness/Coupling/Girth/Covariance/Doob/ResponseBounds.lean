import ZeroFreeness.Coupling.Girth.Covariance.Doob.PinningVertex
import ZeroFreeness.Coupling.Girth.Covariance.Response.Instance

/-! Uniform graph response bounds imply the actual successive-pinning
score hypotheses for every list of distinct revealed vertices. -/
namespace ZeroFreeness.Appendix.Girth
open scoped BigOperators
open PottsCI ZeroFreeness.Potts ZeroFreeness.Potts.Separator Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
universe u v
variable {V : Type u} {C : Type v} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C] [Nonempty C]

namespace Doob
def vertexKeys (js : List V) (a : V → ℝ) : List (((V → C) → C) × ℝ) :=
  js.map (fun j => ((fun σ => σ j), a j))

theorem squareBudget_vertexKeys (js : List V) (a : V → ℝ) :
    squareBudget (vertexKeys (C := C) js a) = (js.map (fun j => a j ^ 2)).sum := by
  simp only [squareBudget, vertexKeys, List.map_map, Function.comp_def]
end Doob

namespace DoobPinning
def remainingVertices (v : V) (js : List V) (h : v ∉ js) : List (Remaining v) :=
  js.attach.map (fun u => ⟨u.val, fun he => h (he ▸ u.property)⟩)

theorem remainingVertices_val (v : V) (js : List V) (h : v ∉ js) :
    (remainingVertices v js h).map Subtype.val = js := by
  simp [remainingVertices, List.map_map]

theorem remainingVertices_nodup (v : V) (js : List V) (h : v ∉ js) (hn : js.Nodup) :
    (remainingVertices v js h).Nodup := by
  apply List.Nodup.of_map Subtype.val
  rw [remainingVertices_val]
  exact hn

theorem vertexKeys_pull (v : V) (c : C) (js : List V) (h : v ∉ js) (a : V → ℝ) :
    Doob.pullScores (extendColouring v c) (Doob.vertexKeys js a) =
      Doob.vertexKeys (remainingVertices v js h) (fun u => a u.val) := by
  conv_lhs => rw [← remainingVertices_val v js h]
  simp only [Doob.pullScores, Doob.vertexKeys, List.map_map, Function.comp_def]
  congr 1
  funext u
  congr 1
  funext σ
  exact extendColouring_remaining v c σ u
end DoobPinning

theorem responseBoundsUpTo_boundedScores {Δ n : ℕ} {χ B U R : ℝ}
    (hglobal : ResponseBoundsUpTo.{u,v} C Δ χ B U R n)
    (I : PinningData V C) (hsize : Fintype.card V ≤ n)
    (hdegree : I.DegreeBound Δ) (hgirth : 5 ≤ I.graph.egirth)
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (F : WeightedSource I χ)
    (js : List V) (hjs : js.Nodup) :
    Doob.BoundedScores (1 - x) (U ^ 2) F.observable (Doob.vertexKeys js F.weight)
      (positiveLaw I x hx) := by
  suffices h : ∀ m (W : Type u) [Fintype W] [DecidableEq W] (J : PinningData W C),
      Fintype.card W ≤ m → Fintype.card W ≤ n → J.DegreeBound Δ → 5 ≤ J.graph.egirth →
      ∀ (F : WeightedSource J χ) (js : List W), js.Nodup →
        Doob.BoundedScores (1 - x) (U ^ 2) F.observable (Doob.vertexKeys js F.weight)
          (positiveLaw J x hx) from
    h (Fintype.card V) V I le_rfl hsize hdegree hgirth F js hjs
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro W _ _ J hm hn hd hg F js hjs
    cases js with
    | nil => trivial
    | cons w ws =>
      obtain ⟨hwn, hws⟩ := List.nodup_cons.mp hjs
      change (∀ c, 1 - (1 - x) * (coordinateMarginal (positiveLaw J x hx) (fun σ => σ w)).w c ≠ 0) ∧
        (∑ c, instanceScore J x hx F w c ^ 2) ≤ U ^ 2 * F.weight w ^ 2 ∧ _
      refine ⟨?_, ?_, ?_⟩
      · intro c
        have hp := probability_atom_le_one (coordinateMarginal (positiveLaw J x hx) (fun σ => σ w)) c
        have hh := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hx1.le)
        nlinarith
      · have hb := (hglobal W J hn hd hg x hx hx1 F w).1
        have hnscore := colourNorm_nonneg (instanceScore J x hx F w)
        rw [← colourNorm_sq]
        nlinarith [sq_nonneg (U * F.weight w - colourNorm (instanceScore J x hx F w))]
      · intro c _
        change Doob.BoundedScores (1 - x) (U ^ 2) (additiveObservable F.term)
          (Doob.vertexKeys ws F.weight)
          (Doob.given (DoobPinning.law J x hx) (fun σ => σ w) c)
        rw [DoobPinning.boundedScores_given, DoobPinning.vertexKeys_pull w c ws hwn]
        let F' : WeightedSource (DoobPinning.childData J w c) χ :=
          F.pull _ Subtype.val (fun _ _ h => h)
        have hlt := (DoobPinning.remaining_card_lt w).trans_le hm
        exact ih _ hlt (DoobPinning.Remaining w) (DoobPinning.childData J w c) le_rfl
          ((DoobPinning.remaining_card_lt w).le.trans hn) (DoobPinning.child_degreeBound J hd w c)
          (DoobPinning.child_girth J hg w c) F' (DoobPinning.remainingVertices w ws hwn)
          (DoobPinning.remainingVertices_nodup w ws hwn hws)

theorem responseBoundsUpTo_revealVariance {Δ n : ℕ} {χ B U R : ℝ}
    (hglobal : ResponseBoundsUpTo.{u,v} C Δ χ B U R n)
    (I : PinningData V C) (hsize : Fintype.card V ≤ n)
    (hdegree : I.DegreeBound Δ) (hgirth : 5 ≤ I.graph.egirth)
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (F : WeightedSource I χ)
    (js : List V) (hjs : js.Nodup) :
    variance (positiveLaw I x hx)
      (Doob.revealMean (js.map (fun v σ => σ v)) (positiveLaw I x hx) F.observable) ≤
        U ^ 2 * (js.map (fun v => F.weight v ^ 2)).sum := by
  have hh := Doob.variance_reveal_le (Doob.vertexKeys js F.weight) (positiveLaw I x hx)
    F.observable (sub_nonneg.mpr hx1.le) (by linarith : 1 - x ≤ 1)
    (responseBoundsUpTo_boundedScores hglobal I hsize hdegree hgirth x hx hx1 F js hjs)
  simpa only [Doob.squareBudget, Doob.vertexKeys, List.map_map, Function.comp_def] using hh

end
end ZeroFreeness.Appendix.Girth
