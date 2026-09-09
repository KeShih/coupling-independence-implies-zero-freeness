import CI2ZF.Coupling.Girth.Spectral.Graph.Poincare
import CI2ZF.Coupling.Girth.Spectral.Graph.HeatBathSystem

/-! The actual positive-activity Gibbs Poincaré inequality. The kernel is
proved to consist of constants by one-coordinate updates on the full
configuration support; it is not an irreducibility assumption. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators InnerProductSpace
open PottsCI Schur
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] [Nonempty C]

/-- A function invariant under every single-site update is constant. -/
theorem update_invariant_constant (f : (V → C) → ℝ)
    (hf : ∀ σ v c, f (Function.update σ v c) = f σ) (σ τ : V → C) : f σ = f τ := by
  have hfin (S : Finset V) : ∀ σ τ : V → C, (∀ v, v ∉ S → σ v = τ v) → f σ = f τ := by
    induction S using Finset.induction_on with
    | empty =>
      intro σ τ h
      have he : σ = τ := funext (fun v => h v (by simp))
      rw [he]
    | @insert v S hv ih =>
      intro σ τ h
      calc
        f σ = f (Function.update σ v (τ v)) := (hf σ v (τ v)).symm
        _ = f τ := ih _ _ (by
          intro u hu
          by_cases huv : u = v
          · subst u
            exact Function.update_self _ _ _
          · rw [Function.update_of_ne huv]
            exact h u (by simp [hu, huv]))
  exact hfin Finset.univ σ τ (by simp)

namespace GraphProjections
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {G : SimpleGraph V} (P : GraphProjections G E)

theorem kernel_iff (f : E) : P.laplacian f = 0 ↔ ∀ v, P.Q v f = 0 := by
  constructor
  · intro h v
    have hsum : (∑ u, ‖P.Q u f‖ ^ 2) = 0 := by
      rw [← P.laplacian_energy, energy, h, inner_zero_right]
    have hv : ‖P.Q v f‖ ^ 2 ≤ 0 := by
      rw [← hsum]
      exact Finset.single_le_sum (fun u _ => sq_nonneg ‖P.Q u f‖) (Finset.mem_univ v)
    have hn : ‖P.Q v f‖ = 0 := by nlinarith [norm_nonneg (P.Q v f)]
    exact norm_eq_zero.mp hn
  · intro h
    simp only [laplacian, LinearMap.sum_apply, h, Finset.sum_const_zero]

end GraphProjections

namespace GraphHeatBath
variable (I : PinningData V C) (x : ℝ) (hx : 0 < x)
  (hlocal : ∀ σ v, 0 < sitePartition I x σ v) (hZ : 0 < I.partition x)

theorem projection_update (v : V) (f : (V → C) → ℝ) (σ : V → C) (c : C) :
    projection I x hx.le hlocal v f (Function.update σ v c) = projection I x hx.le hlocal v f σ := by
  unfold projection
  simp only [Function.update_idem,
    siteLaw_update_of_not_adj I x hx.le hlocal σ v v I.graph.irrefl]

theorem positive_kernel_constant (z : SupportedSpace (I.gibbs x hx.le hZ))
    (hz : (system I x hx.le hlocal hZ).laplacian z = 0) :
    ∃ a : ℝ, z = a • supportedOne (I.gibbs x hx.le hZ) := by
  let μ := I.gibbs x hx.le hZ
  let f := supportedRepresent μ z
  have hfull (σ : V → C) : 0 < μ.w σ := div_pos (I.weight_pos hx σ) hZ
  have hQ := (system I x hx.le hlocal hZ).kernel_iff z |>.mp hz
  have hfixed (v : V) : projection I x hx.le hlocal v f = f := by
    have hh : (heatBath I x hx.le hlocal hZ v).operator z = z := by
      have h := hQ v
      change z - (heatBath I x hx.le hlocal hZ v).operator z = 0 at h
      exact (sub_eq_zero.mp h).symm
    have hembed : supportedEmbed μ (projection I x hx.le hlocal v f) = supportedEmbed μ f := by
      rw [supportedEmbed_represent]
      exact hh
    funext σ
    exact (supportedEmbed_eq_iff μ _ _).mp hembed σ (hfull σ)
  have hupdate (σ : V → C) (v : V) (c : C) : f (Function.update σ v c) = f σ := by
    rw [← hfixed v]
    exact projection_update I x hx hlocal v f σ c
  let σ₀ : V → C := fun _ => Classical.choice inferInstance
  have hconst : f = fun _ => f σ₀ := funext (fun σ => update_invariant_constant f hupdate σ σ₀)
  refine ⟨f σ₀, ?_⟩
  calc
    z = supportedEmbed μ f := (supportedEmbed_represent μ z).symm
    _ = supportedEmbed μ (fun _ => f σ₀) := congrArg (supportedEmbed μ) hconst
    _ = f σ₀ • supportedOne μ := by
      rw [supportedOne, ← map_smul]
      congr 1
      funext σ
      simp

/-- The true conditional-residual Dirichlet form of rate-one heat bath. -/
def dirichlet (f : (V → C) → ℝ) : ℝ :=
  ∑ v, expectReal (I.gibbs x hx.le hZ) (fun σ =>
    (f σ - projection I x hx.le hlocal v f σ) ^ 2)

theorem dirichlet_eq_energy (f : (V → C) → ℝ) :
    dirichlet I x hx hlocal hZ f =
      energy (system I x hx.le hlocal hZ).laplacian (supportedEmbed (I.gibbs x hx.le hZ) f) := by
  rw [GraphProjections.laplacian_energy]
  unfold dirichlet
  apply Finset.sum_congr rfl
  intro v _
  have he : (system I x hx.le hlocal hZ).Q v (supportedEmbed (I.gibbs x hx.le hZ) f) =
      supportedEmbed (I.gibbs x hx.le hZ) (fun σ => f σ - projection I x hx.le hlocal v f σ) := by
    change supportedEmbed _ f - (heatBath I x hx.le hlocal hZ v).operator (supportedEmbed _ f) = _
    rw [SupportedOperator.intertwine, ← map_sub]
    rfl
  rw [he, supportedEmbed_norm_sq]

/-- Actual variance and actual conditional energies, at every positive
activity where the internally proved local star estimate applies. -/
theorem positive_poincare {δ : ℝ} (hδ : 0 < δ) (hg : 5 ≤ I.graph.egirth)
    (hstar : (system I x hx.le hlocal hZ).LocalStarBound (StarData.theta δ))
    (f : (V → C) → ℝ) :
    GraphProjections.spectralGap δ * variance (I.gibbs x hx.le hZ) f ≤ dirichlet I x hx hlocal hZ f := by
  let μ := I.gibbs x hx.le hZ
  let P := system I x hx.le hlocal hZ
  let z : SupportedSpace μ := centeredEmbed μ f
  have hzorth : ∀ g, P.laplacian g = 0 → ⟪z, g⟫_ℝ = 0 := by
    intro g hgker
    obtain ⟨a, rfl⟩ := positive_kernel_constant I x hx hlocal hZ g hgker
    rw [real_inner_smul_right, real_inner_comm]
    have hm : ⟪supportedOne μ, z⟫_ℝ = 0 := (centeredEmbed μ f).property
    rw [hm, mul_zero]
  have h := P.girth_five_poincare hδ hg hstar z hzorth
  have hnorm : ‖z‖ ^ 2 = variance μ f := centeredEmbed_norm_sq μ f
  have he : energy P.laplacian z = energy P.laplacian (supportedEmbed μ f) := by
    have hrepr : z = supportedEmbed μ f - expectReal μ f • supportedOne μ := by
      change supportedEmbed μ (fun σ => f σ - expectReal μ f) = _
      rw [supportedOne, ← map_smul, ← map_sub]
      congr 1
      funext σ
      simp
    rw [hrepr]
    have hOne : P.laplacian (supportedOne μ) = 0 := laplacian_one I x hx.le hlocal hZ
    unfold energy
    simp only [map_sub, map_smul, hOne, smul_zero, sub_zero, inner_sub_left,
      real_inner_smul_left]
    have hcross : ⟪supportedOne μ, P.laplacian (supportedEmbed μ f)⟫_ℝ = 0 := by
      rw [← P.laplacian_symmetric, hOne, inner_zero_left]
    rw [hcross, mul_zero, sub_zero]
  rw [hnorm, he, ← dirichlet_eq_energy I x hx hlocal hZ] at h
  exact h

end GraphHeatBath
end
end CI2ZF.Appendix.Girth
