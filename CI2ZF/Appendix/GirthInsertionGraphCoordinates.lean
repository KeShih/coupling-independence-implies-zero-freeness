import CI2ZF.Appendix.GirthInsertionPoincare
import CI2ZF.Appendix.GirthInsertionCovariance

/-! Actual separator-coordinate energies for the insertion residual.
The only graph geometry is the unique first-layer neighbour of a shell
vertex, which holds for the two-layer decomposition in girth at least five. -/
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

theorem join_restrictions (σ : Vertex U S O → C) :
    join (fun u => σ (Sum.inl u)) (shell σ) (fun o => σ (Sum.inr (Sum.inr o))) = σ := by
  funext v
  rcases v with u | s | o <;> rfl

theorem cavity_shell (hi : Independent I) (hs : Separates I) (c₀ : C)
    (σ : Vertex U S O → C) (u : U) :
    cavity I x hx c₀ (shell σ) u =
      GraphHeatBath.siteLaw I x hx.le (positive_sitePartition I x hx) σ (Sum.inl u) := by
  rw [← siteLaw_join I x hx hi hs c₀ (fun u => σ (Sum.inl u))
    (shell σ) (fun o => σ (Sum.inr (Sum.inr o))) u, join_restrictions]

theorem shell_update_inside (σ : Vertex U S O → C) (u : U) (c : C) :
    shell (Function.update σ (Sum.inl u) c) = shell σ := by
  funext w
  simp [shell]

theorem shell_update_outside (σ : Vertex U S O → C) (o : O) (c : C) :
    shell (Function.update σ (Sum.inr (Sum.inr o)) c) = shell σ := by
  funext w
  simp [shell]

theorem shell_update_shell (σ : Vertex U S O → C) (w : S) (c : C) :
    shell (Function.update σ (Sum.inr (Sum.inl w)) c) = Function.update (shell σ) w c := by
  funext t
  by_cases ht : t = w
  · subst t
    simp [shell]
  · simp [shell, ht]

theorem pi_shell (hi : Independent I) (hs : Separates I) (c₀ : C)
    (hZ : 0 < I.partition x) (σ : Vertex U S O → C) (u : U) (c : C) :
    (model I x hx c₀ hZ).pi u c (shell σ) =
      (GraphHeatBath.siteLaw I x hx.le (positive_sitePartition I x hx) σ (Sum.inl u)).w c := by
  change (cavity I x hx c₀ (shell σ) u).w c = _
  rw [cavity_shell I x hx hi hs c₀]

/-- The shell coordinate sees the exact deleted-edge cavity posterior. -/
theorem G_coordinate_variance (hi : Independent I) (hs : Separates I) (c₀ : C)
    (hZ : 0 < I.partition x) (hx1 : x ≤ 1) {Δ : ℕ} (hd : I.DegreeBound Δ)
    {m : ℝ} (hm : 0 < m) (hq : m ≤ (Fintype.card C : ℝ) - Δ)
    (owner : S → U)
    (howner : ∀ w u, I.graph.Adj (Sum.inl u) (Sum.inr (Sum.inl w)) ↔ u = owner w)
    (z : C → ℝ) (σ : Vertex U S O → C) (w : S) :
    GraphHeatBath.localVariance I x hx (positive_sitePartition I x hx)
      (Sum.inr (Sum.inl w)) (fun τ => ∑ c, z c * (model I x hx c₀ hZ).G (1-x) c (shell τ)) σ ≤
      (1 / m) * ((1 + Real.sqrt ((Fintype.card C : ℝ) / (m + 1))) / m) ^ 2 *
        ∑ c, z c ^ 2 * (model I x hx c₀ hZ).beta (1-x) (owner w) c (shell σ) ^ 2 := by
  let M := model I x hx c₀ hZ
  let r := GraphHeatBath.cavityLaw I x hx σ (Sum.inl (owner w)) (Sum.inr (Sum.inl w))
  let ρ := GraphHeatBath.siteLaw I x hx.le (positive_sitePartition I x hx) σ (Sum.inr (Sum.inl w))
  have ha : I.graph.Adj (Sum.inl (owner w)) (Sum.inr (Sum.inl w)) := (howner w _).mpr rfl
  have hr (c : C) : r.w c ≤ 1 / (m+1) :=
    GraphHeatBath.cavityLaw_atom_le I x hx hx1 hd hm hq σ _ _ ha c
  have hρ (c : C) : ρ.w c ≤ 1/m :=
    GraphHeatBath.siteLaw_atom_le I x hx (positive_sitePartition I x hx) hx1 hd hm hq σ _ c
  have ho (t : C) (j : U) (hj : j ≠ owner w) (c : C) :
      M.pi j c (shell (Function.update σ (Sum.inr (Sum.inl w)) t)) = M.pi j c (shell σ) := by
    change (model I x hx c₀ hZ).pi j c _ = (model I x hx c₀ hZ).pi j c _
    rw [pi_shell I x hx hi hs c₀, pi_shell I x hx hi hs c₀]
    rw [GraphHeatBath.siteLaw_update_of_not_adj I x hx.le (positive_sitePartition I x hx)
      σ (Sum.inl j) (Sum.inr (Sum.inl w)) (fun h => hj ((howner w j).mp h))]
  have he (t c : C) : M.pi (owner w) c (shell (Function.update σ (Sum.inr (Sum.inl w)) t)) =
      r.w c * (1 - (1-x) * colourIndicator t c) / (1 - (1-x) * r.w t) := by
    change (model I x hx c₀ hZ).pi (owner w) c _ = _
    rw [pi_shell I x hx hi hs c₀]
    exact GraphHeatBath.siteLaw_update_cavity I x hx (positive_sitePartition I x hx) σ _ _ ha t c
  exact M.colour_direction_coordinate_variance (owner w) (shell σ)
    (fun t => shell (Function.update σ (Sum.inr (Sum.inl w)) t))
    (by linarith) (by linarith) hm (by positivity) r ρ hr hρ ho he z

end InsertionGraph
end
end CI2ZF.Appendix.Girth
