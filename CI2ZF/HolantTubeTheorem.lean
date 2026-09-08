import CI2ZF.HolantPaths
import CI2ZF.HolantPolytube

/-! Lifting the residual-instance path theorem to the original graph
polynomial and its coordinatewise complex neighborhoods.  The width is
an input chosen before the graph, and the orthant union uses a common
real upper bound for every coordinate. -/
namespace CI2ZF.Holant
open Set Metric
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Activities outside the selected edge set never enter the partition. -/
theorem partition_congr_activities {E K : Type*} [DecidableEq E] [CommSemiring K]
    (inc : E → V → Prop) (edges : Finset E) (f : V → ℕ → K)
    (x z : E → K) (hxz : ∀ e ∈ edges, x e = z e) :
    partition inc edges f x = partition inc edges f z := by
  apply Finset.sum_congr rfl
  intro S hS
  unfold weight
  congr 1
  exact Finset.prod_congr rfl (fun e he => hxz e ((Finset.mem_powerset.mp hS) he))

/-- The already-proved path property, restricted to residual instances
inside one finite ambient simple graph. -/
def GraphFamilyPathNonzero (F : Finset Signature) (Δ : ℕ) (R ε : ℝ) : Prop :=
  ∀ G : SimpleGraph V, (∀ v, G.degree v ≤ Δ) →
    ∀ H : NormalizedInstance V (Sym2 V), H.incidence = graphIncidence →
      H.edges ⊆ G.edgeFinset → (∀ v, H.signature v ∈ residualFamily F) →
      ∀ p : ActivityPath H.edges R ε, ∀ t ∈ ball (0 : ℂ) p.radius,
        H.toInstance.complexPartition (p.activity t) ≠ 0

/-- Original, unnormalized graph signatures inherit the uniform path
theorem. Only the actual edges must lie in the coordinatewise tube. -/
theorem graphPartition_ne_zero_of_paths (F : Finset Signature) (Δ : ℕ)
    {R ε : ℝ} (hε : 0 < ε) (hpath : GraphFamilyPathNonzero (V := V) F Δ R ε)
    (G : SimpleGraph V) (hΔ : ∀ v, G.degree v ≤ Δ)
    (f : V → Signature) (hF : ∀ v, f v ∈ F)
    (harity : ∀ v, (f v).arity = G.degree v)
    (x : Sym2 V → ℝ) (z : Sym2 V → ℂ)
    (hx : ∀ e ∈ G.edgeFinset, x e ∈ Icc 0 R)
    (hz : ∀ e ∈ G.edgeFinset, ‖z e - (x e : ℂ)‖ < ε) :
    graphPartition G (complexValues f) z ≠ 0 := by
  let H := Instance.ofGraph G f harity
  obtain ⟨p, hr, hp⟩ := exists_activity_path_to H.normalize.edges hε x z hx hz
  have ht : (1 : ℂ) ∈ ball (0 : ℂ) p.radius := by
    simpa [mem_ball, dist_eq_norm] using hr
  have hNZ := hpath G hΔ H.normalize rfl (Finset.Subset.refl _)
    (H.normalize_family F hF) p 1 ht
  have heq : H.normalize.toInstance.complexPartition (p.activity 1) =
      H.normalize.toInstance.complexPartition z :=
    partition_congr_activities _ _ _ _ _ hp
  rw [heq] at hNZ
  change H.complexPartition z ≠ 0
  rw [H.complexPartition_normalize]
  apply mul_ne_zero _ hNZ
  exact Finset.prod_ne_zero_iff.mpr (fun v _ => by
    exact_mod_cast (H.signature v).zero_pos.ne')

/-- Product-neighborhood formulation with independent complex activities. -/
theorem graphPartition_polytube_ne_zero_of_paths (F : Finset Signature) (Δ : ℕ)
    {R ε : ℝ} (hε : 0 < ε) (hpath : GraphFamilyPathNonzero (V := V) F Δ R ε)
    (G : SimpleGraph V) (hΔ : ∀ v, G.degree v ≤ Δ)
    (f : V → Signature) (hF : ∀ v, f v ∈ F)
    (harity : ∀ v, (f v).arity = G.degree v)
    (z : Sym2 V → ℂ) (hz : z ∈ polytube (Sym2 V) ε 0 R) :
    graphPartition G (complexValues f) z ≠ 0 := by
  obtain ⟨x, hx, hzx⟩ := (mem_polytube_iff z ε 0 R).mp hz
  exact graphPartition_ne_zero_of_paths F Δ hε hpath G hΔ f hF harity x z
    (fun e _ => hx e) (fun e _ => hzx e)

/-- A single width function gives an open neighborhood of the nonnegative
orthant in every finite dimension; union is taken after the Cartesian product. -/
theorem graphPartition_orthant_ne_zero_of_paths (F : Finset Signature) (Δ : ℕ)
    (width : ℝ → ℝ) (hwidth : ∀ R > 0, 0 < width R)
    (hpath : ∀ R > 0, GraphFamilyPathNonzero (V := V) F Δ R (width R))
    (G : SimpleGraph V) (hΔ : ∀ v, G.degree v ≤ Δ)
    (f : V → Signature) (hF : ∀ v, f v ∈ F)
    (harity : ∀ v, (f v).arity = G.degree v)
    (z : Sym2 V → ℂ) (hz : z ∈ orthantNeighborhood (Sym2 V) width) :
    graphPartition G (complexValues f) z ≠ 0 := by
  obtain ⟨R, hR, hzR⟩ := mem_iUnion₂.mp hz
  exact graphPartition_polytube_ne_zero_of_paths F Δ (hwidth R hR) (hpath R hR)
    G hΔ f hF harity z hzR

/-- The same graph-independent scalar neighborhood works for all diagonal
specializations of the graph family. -/
theorem graphPartition_diagonal_ne_zero_of_paths (F : Finset Signature) (Δ : ℕ)
    (width : ℝ → ℝ) (hwidth : ∀ R > 0, 0 < width R)
    (hpath : ∀ R > 0, GraphFamilyPathNonzero (V := V) F Δ R (width R))
    (G : SimpleGraph V) (hΔ : ∀ v, G.degree v ≤ Δ)
    (f : V → Signature) (hF : ∀ v, f v ∈ F)
    (harity : ∀ v, (f v).arity = G.degree v)
    (z : ℂ) (hz : z ∈ diagonalNeighborhood width) :
    graphPartition G (complexValues f) (fun _ => z) ≠ 0 :=
  graphPartition_orthant_ne_zero_of_paths F Δ width hwidth hpath G hΔ f hF harity
    (fun _ => z) (diagonal_mem_orthantNeighborhood width hz)

end
end CI2ZF.Holant
