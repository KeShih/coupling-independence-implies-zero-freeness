import CI2ZF.Coupling.Girth.Five.ClosedPoincare
import CI2ZF.Coupling.Girth.Spectral.Graph.HeatBathSystem

/-!
# Companion Theorem 9.7 (`thm:potts-gap-girth5`) in operator form

Paper statement (companion, `appendices/fixed-girth-ci.tex`):

> Fix `0 < δ ≤ 1`, `Δ ≥ Δ₀(δ)` and `q ≥ (1+δ)Δ`. Every finite Potts instance on
> a simple graph with `deg_H(v) + k_H(v) ≤ Δ` at each free vertex, after any
> normalized pinning whose free residual graph has girth at least five, and for
> every `x ∈ [0,1]`, has the nonnegative rate-one Glauber Laplacian
> `𝓛 := ∑_v (I - P_v)` satisfying `𝓛² ⪰ γ_δ 𝓛`, `γ_δ = δ / (4(2+δ))`.

All operator inequalities are on the supported `L²` space of the current Gibbs
law (header of the subsection), and `P_v` is the conditional expectation given
all spins except `σ_v`.  Here:

* `SupportedSpace (I.gibbs x hx hZ)` is the supported `L²(μ)` (a genuine
  finite-dimensional real inner-product space);
* `GraphHeatBath.heatBath … v` is the one-site heat-bath conditional
  expectation `P_v` acting on it (see `projection_is_conditional_expectation`);
* `glauberLaplacian = ∑_v (id - P_v)`;
* `A ⪰ B` ("`A - B` is positive semidefinite") is stated as
  `(A - B).IsSymmetric ∧ ∀ z, 0 ≤ ⟪(A - B) z, z⟫`, which is verbatim mathlib's
  `LinearMap.IsPositive (A - B)` over `ℝ` (its `re` is the identity), i.e. `B ≤ A`
  in mathlib's `LinearMap.instLoewnerPartialOrder`.  (The module
  `Mathlib.Analysis.InnerProductSpace.Positive` is not among the prebuilt oleans
  of this project, so the definition is written out.)
-/

namespace CI2ZF.Appendix.Girth.OperatorGap

open scoped BigOperators InnerProductSpace
open PottsCI CI2ZF.Potts CI2ZF.Appendix.Girth Schur

noncomputable section

variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

/-! ## The generator -/

/-- The rate-one Glauber (heat-bath) Laplacian `𝓛 = ∑_v (I - P_v)` on the
supported `L²` space of the Gibbs law at activity `x`. -/
def glauberLaplacian (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x)
    (hlocal : ∀ σ v, 0 < GraphHeatBath.sitePartition I x σ v) (hZ : 0 < I.partition x) :
    Module.End ℝ (SupportedSpace (I.gibbs x hx hZ)) :=
  ∑ v, (LinearMap.id - (GraphHeatBath.heatBath I x hx hlocal hZ v).operator)

section Generator
variable (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x)
  (hlocal : ∀ σ v, 0 < GraphHeatBath.sitePartition I x σ v) (hZ : 0 < I.partition x)

theorem glauberLaplacian_eq_system :
    glauberLaplacian I x hx hlocal hZ = (GraphHeatBath.system I x hx hlocal hZ).laplacian := rfl

theorem glauberLaplacian_symmetric (a b : SupportedSpace (I.gibbs x hx hZ)) :
    ⟪glauberLaplacian I x hx hlocal hZ a, b⟫_ℝ = ⟪a, glauberLaplacian I x hx hlocal hZ b⟫_ℝ :=
  (GraphHeatBath.system I x hx hlocal hZ).laplacian_symmetric a b

theorem glauberLaplacian_one :
    glauberLaplacian I x hx hlocal hZ (supportedOne (I.gibbs x hx hZ)) = 0 :=
  GraphHeatBath.laplacian_one I x hx hlocal hZ

/-- The quadratic form of `𝓛` on an embedded function is the Dirichlet form
`∑_v E_μ[(f - P_v f)²]`, at every `x ≥ 0` (including the hard endpoint). -/
theorem inner_glauberLaplacian_embed (f : (V → C) → ℝ) :
    ⟪supportedEmbed (I.gibbs x hx hZ) f,
        glauberLaplacian I x hx hlocal hZ (supportedEmbed (I.gibbs x hx hZ) f)⟫_ℝ =
      ∑ v, expectReal (I.gibbs x hx hZ)
        (fun σ => (f σ - GraphHeatBath.projection I x hx hlocal v f σ) ^ 2) := by
  rw [glauberLaplacian_eq_system]
  change energy _ _ = _
  rw [GraphProjections.laplacian_energy]
  apply Finset.sum_congr rfl
  intro v _
  have he : (GraphHeatBath.system I x hx hlocal hZ).Q v (supportedEmbed (I.gibbs x hx hZ) f) =
      supportedEmbed (I.gibbs x hx hZ)
        (fun σ => f σ - GraphHeatBath.projection I x hx hlocal v f σ) := by
    change supportedEmbed _ f -
      (GraphHeatBath.heatBath I x hx hlocal hZ v).operator (supportedEmbed _ f) = _
    rw [SupportedOperator.intertwine, ← map_sub]
    rfl
  rw [he, supportedEmbed_norm_sq]

/-- `P_v` is the `μ`-conditional expectation given all spins except `σ_v`:
`P_v f` does not depend on `σ_v`, and `E_μ[(P_v f) g] = E_μ[f g]` for every
`g` that does not depend on `σ_v`. -/
theorem projection_is_conditional_expectation (v : V) (f : (V → C) → ℝ) :
    (∀ σ c, GraphHeatBath.projection I x hx hlocal v f (Function.update σ v c) =
      GraphHeatBath.projection I x hx hlocal v f σ) ∧
    ∀ g : (V → C) → ℝ, (∀ σ c, g (Function.update σ v c) = g σ) →
      expectReal (I.gibbs x hx hZ)
          (fun σ => GraphHeatBath.projection I x hx hlocal v f σ * g σ) =
        expectReal (I.gibbs x hx hZ) (fun σ => f σ * g σ) := by
  refine ⟨fun σ c => ?_, ?_⟩
  · unfold GraphHeatBath.projection
    simp only [Function.update_idem,
      GraphHeatBath.siteLaw_update_of_not_adj I x hx hlocal σ v v I.graph.irrefl]
  intro g hg
  rw [GraphHeatBath.projection_selfAdjoint I x hx hlocal hZ v f g]
  have hPg : GraphHeatBath.projection I x hx hlocal v g = g := by
    funext σ
    unfold GraphHeatBath.projection
    simp only [hg]
    exact expectReal_const _ _
  rw [hPg]

end Generator

/-! ## From Poincaré to the operator inequality -/

/-- Abstract step: if `γ ‖g‖² ≤ ⟨g, T g⟩` then `γ ⟨g, T g⟩ ≤ ‖T g‖²`
(Cauchy–Schwarz). -/
theorem square_gap_of_poincare {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →ₗ[ℝ] E) {γ : ℝ} (hγ : 0 ≤ γ) (g : E) (hP : γ * ‖g‖ ^ 2 ≤ ⟪g, T g⟫_ℝ) :
    γ * ⟪g, T g⟫_ℝ ≤ ‖T g‖ ^ 2 := by
  have hcs : ⟪g, T g⟫_ℝ ≤ ‖g‖ * ‖T g‖ := real_inner_le_norm _ _
  nlinarith [sq_nonneg (‖T g‖ - γ * ‖g‖), mul_le_mul_of_nonneg_left hcs hγ,
    mul_le_mul_of_nonneg_left hP hγ]

omit [DecidableEq C] in
theorem colours_succ_le {δ : ℝ} {Δ : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hΔ : girthFiveThreshold δ ≤ Δ) (hq : (1 + δ) * Δ ≤ (Fintype.card C : ℝ)) :
    Δ + 1 ≤ Fintype.card C := by
  have hh := girthFive_colour_slack hδ hδ1 hΔ hq
  omega

/-- Under the hypotheses of the theorem the Gibbs law exists at every `x ∈ [0,1]`
(no `Nonempty C` assumption: it follows from `q ≥ Δ + 1`). -/
theorem residual_partition_pos (I : PinningData V C) {x : ℝ} (hx : 0 ≤ x) {δ : ℝ} {Δ : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hΔ : girthFiveThreshold δ ≤ Δ)
    (hdegree : I.DegreeBound Δ) (hq : (1 + δ) * Δ ≤ (Fintype.card C : ℝ)) :
    0 < I.partition x := by
  have hq1 := colours_succ_le (C := C) hδ hδ1 hΔ hq
  have : Nonempty C := Fintype.card_pos_iff.mp (by omega)
  exact partition_pos_of_succ_le I hx hdegree hq1

theorem residual_sitePartition_pos (I : PinningData V C) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {δ : ℝ} {Δ : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hΔ : girthFiveThreshold δ ≤ Δ)
    (hdegree : I.DegreeBound Δ) (hq : (1 + δ) * Δ ≤ (Fintype.card C : ℝ)) :
    ∀ σ v, 0 < GraphHeatBath.sitePartition I x σ v :=
  GraphHeatBath.sitePartition_pos I hx hx1 hdegree (colours_succ_le hδ hδ1 hΔ hq)

/-- The operator inequality `⟨z, 𝓛 z⟫ γ_δ ≤ ⟨𝓛 z, 𝓛 z⟩` for every vector of the
supported `L²(μ)`, at every `x ∈ [0,1]`. -/
theorem square_gap_inner (I : PinningData V C) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {δ : ℝ} {Δ : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hΔ : girthFiveThreshold δ ≤ Δ)
    (hdegree : I.DegreeBound Δ) (hg : 5 ≤ I.graph.egirth)
    (hq : (1 + δ) * Δ ≤ (Fintype.card C : ℝ))
    (hlocal : ∀ σ v, 0 < GraphHeatBath.sitePartition I x σ v) (hZ : 0 < I.partition x)
    (z : SupportedSpace (I.gibbs x hx hZ)) :
    δ / (4 * (2 + δ)) * ⟪z, glauberLaplacian I x hx hlocal hZ z⟫_ℝ ≤
      ⟪glauberLaplacian I x hx hlocal hZ z, glauberLaplacian I x hx hlocal hZ z⟫_ℝ := by
  have hq1 := colours_succ_le (C := C) hδ hδ1 hΔ hq
  have : Nonempty C := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨f, rfl⟩ : ∃ f, supportedEmbed (I.gibbs x hx hZ) f = z :=
    ⟨_, supportedEmbed_represent _ z⟩
  have hS := glauberLaplacian_symmetric I x hx hlocal hZ
  have hL1 := glauberLaplacian_one I x hx hlocal hZ
  set L := glauberLaplacian I x hx hlocal hZ with hL
  set m : ℝ := expectReal (I.gibbs x hx hZ) f with hm
  set g : SupportedSpace (I.gibbs x hx hZ) :=
    supportedEmbed (I.gibbs x hx hZ) (fun σ => f σ - m) with hgdef
  have hg_eq : g = supportedEmbed (I.gibbs x hx hZ) f - m • supportedOne (I.gibbs x hx hZ) := by
    rw [hgdef, supportedOne, ← map_smul, ← map_sub]
    congr 1
    funext σ
    simp
  have hLg : L g = L (supportedEmbed (I.gibbs x hx hZ) f) := by
    rw [hg_eq, map_sub, map_smul, hL1, smul_zero, sub_zero]
  have hEg : ⟪g, L g⟫_ℝ =
      ⟪supportedEmbed (I.gibbs x hx hZ) f, L (supportedEmbed (I.gibbs x hx hZ) f)⟫_ℝ := by
    rw [hLg, hg_eq, inner_sub_left, real_inner_smul_left,
      ← hS (supportedOne (I.gibbs x hx hZ)) (supportedEmbed (I.gibbs x hx hZ) f), hL1,
      inner_zero_left, mul_zero, sub_zero]
  have hnorm : ‖g‖ ^ 2 = variance (I.gibbs x hx hZ) f := by
    rw [hgdef, supportedEmbed_norm_sq]
    rfl
  have hdir := inner_glauberLaplacian_embed I x hx hlocal hZ f
  have hP : GraphProjections.spectralGap δ * variance (I.gibbs x hx hZ) f ≤
      ∑ v, expectReal (I.gibbs x hx hZ)
        (fun σ => (f σ - GraphHeatBath.projection I x hx hlocal v f σ) ^ 2) :=
    girth_five_closed_poincare I hx hx1 hδ hδ1 hΔ hdegree hg hq f
  have hPg : GraphProjections.spectralGap δ * ‖g‖ ^ 2 ≤ ⟪g, L g⟫_ℝ := by
    rw [hnorm, hEg, hL, hdir]
    exact hP
  have hsq := square_gap_of_poincare L (GraphProjections.spectralGap_pos hδ).le g hPg
  rw [hEg, hLg, ← real_inner_self_eq_norm_sq] at hsq
  unfold GraphProjections.spectralGap at hsq
  exact hsq

/-- `𝓛` is a nonnegative self-adjoint operator on the supported `L²(μ)`
(mathlib's `LinearMap.IsPositive 𝓛`, written out over `ℝ`). -/
theorem glauberLaplacian_nonneg (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x)
    (hlocal : ∀ σ v, 0 < GraphHeatBath.sitePartition I x σ v) (hZ : 0 < I.partition x) :
    (glauberLaplacian I x hx hlocal hZ).IsSymmetric ∧
      ∀ z, 0 ≤ ⟪glauberLaplacian I x hx hlocal hZ z, z⟫_ℝ := by
  refine ⟨glauberLaplacian_symmetric I x hx hlocal hZ, fun z => ?_⟩
  rw [real_inner_comm]
  exact (GraphHeatBath.system I x hx hlocal hZ).laplacian_positive z

/-- The Loewner inequality `𝓛² ⪰ γ_δ 𝓛`: `𝓛² - γ_δ 𝓛` is self-adjoint and
positive semidefinite, for arbitrary proofs of the two normalizer positivity
side conditions. -/
theorem square_gap_loewner (I : PinningData V C) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {δ : ℝ} {Δ : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hΔ : girthFiveThreshold δ ≤ Δ)
    (hdegree : I.DegreeBound Δ) (hg : 5 ≤ I.graph.egirth)
    (hq : (1 + δ) * Δ ≤ (Fintype.card C : ℝ))
    (hlocal : ∀ σ v, 0 < GraphHeatBath.sitePartition I x σ v) (hZ : 0 < I.partition x) :
    (glauberLaplacian I x hx hlocal hZ ^ 2 -
        (δ / (4 * (2 + δ))) • glauberLaplacian I x hx hlocal hZ).IsSymmetric ∧
      ∀ z, 0 ≤ ⟪(glauberLaplacian I x hx hlocal hZ ^ 2 -
        (δ / (4 * (2 + δ))) • glauberLaplacian I x hx hlocal hZ) z, z⟫_ℝ := by
  have hS := glauberLaplacian_symmetric I x hx hlocal hZ
  set L := glauberLaplacian I x hx hlocal hZ with hL
  refine ⟨fun a b => ?_, fun z => ?_⟩
  · simp only [pow_two, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
      inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [hS (L a) b, hS a (L b), hS a b]
  · simp only [pow_two, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
      inner_sub_left, real_inner_smul_left]
    rw [hS (L z) z, real_inner_comm z (L z)]
    have h := square_gap_inner I hx hx1 hδ hδ1 hΔ hdegree hg hq hlocal hZ z
    linarith

/-! ## Headline statement -/

/-- **Companion Theorem 9.7 (`thm:potts-gap-girth5`).**  Fix `0 < δ ≤ 1`,
`Δ ≥ Δ₀(δ)` and `q = |C| ≥ (1+δ)Δ`.  For every residual instance `I` (free simple
graph plus arbitrary boundary counts) with `deg_H(v) + k_H(v) ≤ Δ` at every free
vertex and free graph of girth at least five, and every `x ∈ [0,1]`, the
rate-one Glauber Laplacian `𝓛 = ∑_v (I - P_v)` on the supported `L²` space of the
Gibbs law is nonnegative (self-adjoint, `⟨𝓛 z, z⟩ ≥ 0`) and satisfies
`𝓛² ⪰ γ_δ 𝓛` with `γ_δ = δ / (4(2+δ))`: the operator `𝓛² - γ_δ 𝓛` is self-adjoint
and positive semidefinite. -/
theorem potts_gap_girth5 (I : PinningData V C) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {δ : ℝ} {Δ : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hΔ : girthFiveThreshold δ ≤ Δ)
    (hdegree : I.DegreeBound Δ) (hg : 5 ≤ I.graph.egirth)
    (hq : (1 + δ) * Δ ≤ (Fintype.card C : ℝ)) :
    let hZ : 0 < I.partition x := residual_partition_pos I hx hδ hδ1 hΔ hdegree hq
    let hlocal := residual_sitePartition_pos I hx hx1 hδ hδ1 hΔ hdegree hq
    let 𝓛 := glauberLaplacian I x hx hlocal hZ
    (𝓛.IsSymmetric ∧ ∀ z, 0 ≤ ⟪𝓛 z, z⟫_ℝ) ∧
      ((𝓛 ^ 2 - (δ / (4 * (2 + δ))) • 𝓛).IsSymmetric ∧
        ∀ z, 0 ≤ ⟪(𝓛 ^ 2 - (δ / (4 * (2 + δ))) • 𝓛) z, z⟫_ℝ) :=
  ⟨glauberLaplacian_nonneg I x hx _ _,
    square_gap_loewner I hx hx1 hδ hδ1 hΔ hdegree hg hq _ _⟩

/-! ## The same statement on functions, with `⟨f, g⟩_μ = E_μ[f g]` -/

/-- `𝓛 f = ∑_v (f - P_v f)` as a function of the configuration. -/
def glauberLaplacianFun (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x)
    (hlocal : ∀ σ v, 0 < GraphHeatBath.sitePartition I x σ v) (f : (V → C) → ℝ) :
    (V → C) → ℝ :=
  fun σ => ∑ v, (f σ - GraphHeatBath.projection I x hx hlocal v f σ)

theorem embed_glauberLaplacianFun (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x)
    (hlocal : ∀ σ v, 0 < GraphHeatBath.sitePartition I x σ v) (hZ : 0 < I.partition x)
    (f : (V → C) → ℝ) :
    supportedEmbed (I.gibbs x hx hZ) (glauberLaplacianFun I x hx hlocal f) =
      glauberLaplacian I x hx hlocal hZ (supportedEmbed (I.gibbs x hx hZ) f) := by
  have hfun : glauberLaplacianFun I x hx hlocal f =
      ∑ v, (fun σ => f σ - GraphHeatBath.projection I x hx hlocal v f σ) := by
    funext σ
    simp only [glauberLaplacianFun, Finset.sum_apply]
  rw [hfun, map_sum]
  unfold glauberLaplacian
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro v _
  rw [LinearMap.sub_apply, LinearMap.id_apply, SupportedOperator.intertwine, ← map_sub]
  rfl

/-- Function form of Theorem 9.7: for every `f`, with `⟨f, g⟩_μ := E_μ[f g]`,
`⟨f, 𝓛 f⟩_μ ≥ 0`, `𝓛` is `μ`-self-adjoint, and
`γ_δ ⟨f, 𝓛 f⟩_μ ≤ ⟨f, 𝓛² f⟩_μ = ⟨𝓛 f, 𝓛 f⟩_μ`. -/
theorem potts_gap_girth5_functions (I : PinningData V C) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {δ : ℝ} {Δ : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hΔ : girthFiveThreshold δ ≤ Δ)
    (hdegree : I.DegreeBound Δ) (hg : 5 ≤ I.graph.egirth)
    (hq : (1 + δ) * Δ ≤ (Fintype.card C : ℝ)) :
    let hZ : 0 < I.partition x := residual_partition_pos I hx hδ hδ1 hΔ hdegree hq
    let hlocal := residual_sitePartition_pos I hx hx1 hδ hδ1 hΔ hdegree hq
    let μ := I.gibbs x hx hZ
    let 𝓛 := glauberLaplacianFun I x hx hlocal
    (∀ f g : (V → C) → ℝ,
      expectReal μ (fun σ => 𝓛 f σ * g σ) = expectReal μ (fun σ => f σ * 𝓛 g σ)) ∧
    (∀ f : (V → C) → ℝ, 0 ≤ expectReal μ (fun σ => f σ * 𝓛 f σ)) ∧
    ∀ f : (V → C) → ℝ,
      δ / (4 * (2 + δ)) * expectReal μ (fun σ => f σ * 𝓛 f σ) ≤
        expectReal μ (fun σ => f σ * 𝓛 (𝓛 f) σ) ∧
      expectReal μ (fun σ => f σ * 𝓛 (𝓛 f) σ) = expectReal μ (fun σ => 𝓛 f σ * 𝓛 f σ) := by
  intro hZ hlocal μ 𝓛
  have hemb (f : (V → C) → ℝ) : supportedEmbed μ (𝓛 f) =
      glauberLaplacian I x hx hlocal hZ (supportedEmbed μ f) :=
    embed_glauberLaplacianFun I x hx hlocal hZ f
  have hS := glauberLaplacian_symmetric I x hx hlocal hZ
  refine ⟨fun f g => ?_, fun f => ?_, fun f => ⟨?_, ?_⟩⟩
  · rw [← supportedEmbed_inner, ← supportedEmbed_inner, hemb, hemb, hS]
  · rw [← supportedEmbed_inner, hemb]
    have h := (GraphHeatBath.system I x hx hlocal hZ).laplacian_positive (supportedEmbed μ f)
    exact h
  · rw [← supportedEmbed_inner, ← supportedEmbed_inner, hemb, hemb, hemb,
      ← hS (supportedEmbed μ f) (glauberLaplacian I x hx hlocal hZ (supportedEmbed μ f))]
    exact square_gap_inner I hx hx1 hδ hδ1 hΔ hdegree hg hq hlocal hZ (supportedEmbed μ f)
  · rw [← supportedEmbed_inner, ← supportedEmbed_inner, hemb, hemb,
      ← hS (supportedEmbed μ f) (glauberLaplacian I x hx hlocal hZ (supportedEmbed μ f))]

end

end CI2ZF.Appendix.Girth.OperatorGap

