import CI2ZF.Appendix.GirthInsertionGraphCovariance
import CI2ZF.Appendix.GirthInsertionAdapter

/-! Variance of the individual cavity marginals and their complete sum.
These are derived from the true graph Dirichlet form, with one shell
coordinate assigned to its unique first-layer neighbour. -/
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

theorem cavitySum_coordinate_variance (hi : Independent I) (hs : Separates I) (c₀ : C)
    (hZ : 0 < I.partition x) (hx1 : x ≤ 1) {Δ : ℕ} (hd : I.DegreeBound Δ)
    {m : ℝ} (hm : 0 < m) (hq : m ≤ (Fintype.card C : ℝ) - Δ)
    (owner : S → U)
    (howner : ∀ w u, I.graph.Adj (Sum.inl u) (Sum.inr (Sum.inl w)) ↔ u = owner w)
    (z : U → ℝ) (c : C) (σ : Vertex U S O → C) (w : S) :
    GraphHeatBath.localVariance I x hx (positive_sitePartition I x hx)
      (Sum.inr (Sum.inl w)) (fun τ => ∑ u, z u * (model I x hx c₀ hZ).pi u c (shell τ)) σ ≤
      (1/m) * ((1 + Real.sqrt ((Fintype.card C : ℝ) / (m+1))) / m) ^ 2 * z (owner w) ^ 2 := by
  let M := model I x hx c₀ hZ
  let r := GraphHeatBath.cavityLaw I x hx σ (Sum.inl (owner w)) (Sum.inr (Sum.inl w))
  let ρ := GraphHeatBath.siteLaw I x hx.le (positive_sitePartition I x hx) σ (Sum.inr (Sum.inl w))
  let h : C → ℝ := fun a => z (owner w) * colourIndicator c a
  let a : ℝ := ∑ j ∈ Finset.univ.erase (owner w), z j * M.pi j c (shell σ)
  have ha : I.graph.Adj (Sum.inl (owner w)) (Sum.inr (Sum.inl w)) := (howner w _).mpr rfl
  have hr (k : C) : r.w k ≤ 1 / (m+1) :=
    GraphHeatBath.cavityLaw_atom_le I x hx hx1 hd hm hq σ _ _ ha k
  have hρ (k : C) : ρ.w k ≤ 1/m :=
    GraphHeatBath.siteLaw_atom_le I x hx (positive_sitePartition I x hx) hx1 hd hm hq σ _ k
  have ho (t : C) (j : U) (hj : j ≠ owner w) :
      M.pi j c (shell (Function.update σ (Sum.inr (Sum.inl w)) t)) = M.pi j c (shell σ) := by
    change (model I x hx c₀ hZ).pi j c _ = (model I x hx c₀ hZ).pi j c _
    rw [pi_shell I x hx hi hs c₀, pi_shell I x hx hi hs c₀,
      GraphHeatBath.siteLaw_update_of_not_adj I x hx.le (positive_sitePartition I x hx)
        σ (Sum.inl j) (Sum.inr (Sum.inl w)) (fun h => hj ((howner w j).mp h))]
  have he (t : C) : M.pi (owner w) c (shell (Function.update σ (Sum.inr (Sum.inl w)) t)) =
      r.w c * (1 - (1-x) * colourIndicator t c) / (1 - (1-x) * r.w t) := by
    change (model I x hx c₀ hZ).pi (owner w) c _ = _
    rw [pi_shell I x hx hi hs c₀]
    exact GraphHeatBath.siteLaw_update_cavity I x hx (positive_sitePartition I x hx) σ _ _ ha t c
  have hh (t : C) : z (owner w) * M.pi (owner w) c (shell (Function.update σ (Sum.inr (Sum.inl w)) t)) =
      edgeResponse (1-x) r h t := by
    rw [he]
    have hE : expectReal r h = z (owner w) * r.w c := by
      rw [expectReal_const_mul, expect_colourIndicator]
    rw [edgeResponse, hE]
    by_cases ht : t = c
    · subst t
      simp only [h, colourIndicator, if_true, mul_one]
      ring
    · simp only [h, colourIndicator, if_neg ht, if_neg (Ne.symm ht), mul_zero, sub_zero]
      ring
  have hf (t : C) : (∑ j, z j * M.pi j c (shell (Function.update σ (Sum.inr (Sum.inl w)) t))) =
      edgeResponse (1-x) r h t + a := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (owner w)), hh]
    have hh' : (∑ j ∈ Finset.univ.erase (owner w),
        z j * M.pi j c (shell (Function.update σ (Sum.inr (Sum.inl w)) t))) = a := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [ho t j (Finset.ne_of_mem_erase hj)]
    rw [hh', add_comm]
  change variance ρ (fun t => ∑ j, z j * M.pi j c (shell (Function.update σ (Sum.inr (Sum.inl w)) t))) ≤ _
  simp_rw [hf]
  rw [variance_add_const]
  have hb := one_edge_variance_bound (by linarith : 0 ≤ 1-x) (by linarith : 1-x ≤ 1)
    hm (by positivity : 0 ≤ 1/m) r ρ hr hρ h
  have hn : (∑ k, h k ^ 2) = z (owner w) ^ 2 := by simp [h, colourIndicator]
  rwa [hn] at hb

theorem cavitySum_variance (hi : Independent I) (hs : Separates I) (c₀ : C)
    (hZ : 0 < I.partition x) (hx1 : x ≤ 1) {Δ : ℕ} (hd : I.DegreeBound Δ)
    {m γ : ℝ} (hm : 0 < m) (hq : m ≤ (Fintype.card C : ℝ) - Δ) (hγ : 0 < γ)
    (owner : S → U)
    (howner : ∀ w u, I.graph.Adj (Sum.inl u) (Sum.inr (Sum.inl w)) ↔ u = owner w)
    (hP : ∀ f, γ * variance (I.gibbs x hx.le hZ) f ≤
      ∑ v, expectReal (I.gibbs x hx.le hZ)
        (GraphHeatBath.localVariance I x hx (positive_sitePartition I x hx) v f))
    (z : U → ℝ) (c : C) :
    variance (model I x hx c₀ hZ).shell (fun ξ => ∑ u, z u * (model I x hx c₀ hZ).pi u c ξ) ≤
      (1/m) * ((1 + Real.sqrt ((Fintype.card C : ℝ) / (m+1))) / m) ^ 2 / γ *
        ∑ w, z (owner w) ^ 2 := by
  let M := model I x hx c₀ hZ
  let L := (1 + Real.sqrt ((Fintype.card C : ℝ) / (m+1))) / m
  have hpoint (w : S) : expectReal (I.gibbs x hx.le hZ)
      (GraphHeatBath.localVariance I x hx (positive_sitePartition I x hx) (Sum.inr (Sum.inl w))
        (fun τ => ∑ u, z u * M.pi u c (shell τ))) ≤ (1/m) * L ^ 2 * z (owner w) ^ 2 := by
    calc
      _ ≤ expectReal (I.gibbs x hx.le hZ) (fun _ => (1/m) * L ^ 2 * z (owner w) ^ 2) :=
        expectReal_mono _ (fun σ => cavitySum_coordinate_variance I x hx hi hs c₀ hZ hx1 hd hm hq owner howner z c σ w)
      _ = _ := expectReal_const _ _
  have h := (shell_poincare I x hx c₀ hZ hP
      (fun ξ => ∑ u, z u * M.pi u c ξ)).trans (Finset.sum_le_sum fun w _ => hpoint w)
  rw [← Finset.mul_sum] at h
  calc
    _ ≤ ((1/m) * L ^ 2 * ∑ w, z (owner w) ^ 2) / γ :=
      (le_div_iff₀ hγ).mpr (by simpa only [mul_comm] using h)
    _ = _ := by dsimp [L]; ring

theorem owner_fibre_card_le (owner : S → U)
    (howner : ∀ w u, I.graph.Adj (Sum.inl u) (Sum.inr (Sum.inl w)) ↔ u = owner w)
    {Δ : ℕ} (hd : I.DegreeBound Δ) (u : U) : Fintype.card {w : S // owner w = u} ≤ Δ := by
  let f : {w : S // owner w = u} → {v // v ∈ I.graph.neighborFinset (Sum.inl u)} :=
    fun w => ⟨Sum.inr (Sum.inl w.val), by simpa using (howner w.val u).mpr w.property.symm⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact Sum.inl.inj (Sum.inr.inj (congrArg Subtype.val hab))
  have hc := Fintype.card_le_of_injective f hf
  have he : Fintype.card {v // v ∈ I.graph.neighborFinset (Sum.inl u)} = I.graph.degree (Sum.inl u) := by
    rw [Fintype.card_coe, SimpleGraph.card_neighborFinset_eq_degree]
  rw [he] at hc
  exact hc.trans ((Nat.le_add_right _ _).trans (hd (Sum.inl u)))

theorem pi_variance (hi : Independent I) (hs : Separates I) (c₀ : C)
    (hZ : 0 < I.partition x) (hx1 : x ≤ 1) {Δ : ℕ} (hd : I.DegreeBound Δ)
    {m γ : ℝ} (hm : 0 < m) (hq : m ≤ (Fintype.card C : ℝ) - Δ) (hγ : 0 < γ)
    (owner : S → U)
    (howner : ∀ w u, I.graph.Adj (Sum.inl u) (Sum.inr (Sum.inl w)) ↔ u = owner w)
    (hP : ∀ f, γ * variance (I.gibbs x hx.le hZ) f ≤
      ∑ v, expectReal (I.gibbs x hx.le hZ)
        (GraphHeatBath.localVariance I x hx (positive_sitePartition I x hx) v f))
    (u : U) (c : C) :
    variance (model I x hx c₀ hZ).shell ((model I x hx c₀ hZ).pi u c) ≤
      (Δ : ℝ) * (1/m) * ((1 + Real.sqrt ((Fintype.card C : ℝ) / (m+1))) / m) ^ 2 / γ := by
  have h := cavitySum_variance I x hx hi hs c₀ hZ hx1 hd hm hq hγ owner howner hP
    (fun j => if j = u then 1 else 0) c
  have hsum : (∑ w : S, (if owner w = u then (1 : ℝ) else 0) ^ 2) =
      (Fintype.card {w : S // owner w = u} : ℝ) := by
    simp [Fintype.card_subtype, Finset.sum_boole]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  rw [hsum] at h
  have hc : (Fintype.card {w : S // owner w = u} : ℝ) ≤ Δ := by
    exact_mod_cast owner_fibre_card_le I owner howner hd u
  refine h.trans ?_
  calc
    _ ≤ ((1/m) * ((1 + Real.sqrt ((Fintype.card C : ℝ) / (m+1))) / m) ^ 2 / γ) * Δ :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

theorem centredCavitySum_variance (hi : Independent I) (hs : Separates I) (c₀ : C)
    (hZ : 0 < I.partition x) (hx1 : x ≤ 1) {Δ : ℕ} (hd : I.DegreeBound Δ)
    {m γ : ℝ} (hm : 0 < m) (hq : m ≤ (Fintype.card C : ℝ) - Δ) (hγ : 0 < γ)
    (hsize : (Fintype.card S : ℝ) ≤ (Δ : ℝ) ^ 2)
    (owner : S → U)
    (howner : ∀ w u, I.graph.Adj (Sum.inl u) (Sum.inr (Sum.inl w)) ↔ u = owner w)
    (hP : ∀ f, γ * variance (I.gibbs x hx.le hZ) f ≤
      ∑ v, expectReal (I.gibbs x hx.le hZ)
        (GraphHeatBath.localVariance I x hx (positive_sitePartition I x hx) v f))
    (c : C) :
    variance (model I x hx c₀ hZ).shell ((model I x hx c₀ hZ).centredCavitySum c) ≤
      (Δ : ℝ) ^ 2 * (1/m) * ((1 + Real.sqrt ((Fintype.card C : ℝ) / (m+1))) / m) ^ 2 / γ := by
  let M := model I x hx c₀ hZ
  have hf : M.centredCavitySum c = fun ξ => (∑ u, M.pi u c ξ) + (-(∑ u, M.p u c)) := by
    funext ξ
    simp only [InsertionModel.centredCavitySum, sub_eq_add_neg,
      Finset.sum_add_distrib, Finset.sum_neg_distrib]
  change variance M.shell (M.centredCavitySum c) ≤ _
  rw [hf, variance_add_const]
  have h := cavitySum_variance I x hx hi hs c₀ hZ hx1 hd hm hq hγ owner howner hP (fun _ => 1) c
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  refine h.trans ?_
  calc
    _ ≤ ((1/m) * ((1 + Real.sqrt ((Fintype.card C : ℝ) / (m+1))) / m) ^ 2 / γ) * (Δ : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hsize (by positivity)
    _ = _ := by ring

end InsertionGraph
end
end CI2ZF.Appendix.Girth
