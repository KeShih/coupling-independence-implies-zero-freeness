import ZeroFreeness.Coupling.Vigoda.ActivationAverage

/-! The union active degree at an adjacent pair is its actual common-coin count. -/

namespace ZeroFreeness
open PottsCI PottsCI.Vigoda
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V C : Type*} [Fintype V] [Fintype C]

omit [Fintype C] in
theorem activeGraph_le_original (I : PinningData V C) (A : Finset I.Constraint) :
    activeGraph I A ≤ I.graph := by
  intro u v h
  obtain ⟨e, _, he⟩ := h
  have hg := e.property
  rw [he, SimpleGraph.mem_edgeFinset] at hg
  exact hg

omit [Fintype C] in
theorem activeGraph_root_adj_iff (I : PinningData V C) (A : Finset I.Constraint)
    (v : V) (u : I.graph.neighborSet v) :
    (activeGraph I A).Adj v u.1 ↔ rootFreeConstraint I v u ∈ A := by
  constructor
  · rintro ⟨e, heA, heval⟩
    have heq : (Sum.inl e : I.Constraint) = rootFreeConstraint I v u :=
      congrArg Sum.inl (Subtype.ext heval)
    exact heq ▸ heA
  · intro h
    exact ⟨⟨s(v, u.1), by rw [SimpleGraph.mem_edgeFinset]; exact u.property⟩, h, rfl⟩

theorem active_union_root_adj_iff_coin (I : PinningData V C) (X Y : V → C)
    (ω : I.Constraint → Bool) (v : V) (u : I.graph.neighborSet v)
    (hroot : X v ≠ Y v) (hagree : X u.1 = Y u.1) :
    ((activeGraph I (activatedSet I X ω)) ⊔ (activeGraph I (activatedSet I Y ω))).Adj v u.1 ↔
      ω (rootFreeConstraint I v u) = true := by
  change (activeGraph I (activatedSet I X ω)).Adj v u.1 ∨
      (activeGraph I (activatedSet I Y ω)).Adj v u.1 ↔ _
  rw [activeGraph_root_adj_iff, activeGraph_root_adj_iff,
    mem_activatedSet, mem_activatedSet]
  have hs : I.constraintSatisfied X (rootFreeConstraint I v u) ∨
      I.constraintSatisfied Y (rootFreeConstraint I v u) := by
    change X v ≠ X u.1 ∨ Y v ≠ Y u.1
    by_cases h : X v = X u.1
    · right
      intro hy
      exact hroot (h.trans (hagree.trans hy.symm))
    · exact Or.inl h
  tauto

/-- For adjacent configurations, each free root edge is satisfied on at
least one side, so its union activation is exactly the successful coin. -/
theorem union_active_degree_eq_coin_count (I : PinningData V C) (X Y : V → C)
    (ω : I.Constraint → Bool) (v : V) (hroot : X v ≠ Y v)
    (hagree : ∀ u, u ≠ v → X u = Y u) :
    ((((activeGraph I (activatedSet I X ω)) ⊔
      (activeGraph I (activatedSet I Y ω))).degree v) : ℝ) = rootFreeCoinCount I v ω := by
  let H := (activeGraph I (activatedSet I X ω)) ⊔ (activeGraph I (activatedSet I Y ω))
  have hle : H ≤ I.graph := sup_le
    (activeGraph_le_original I _) (activeGraph_le_original I _)
  let e : H.neighborSet v ≃
      {u : I.graph.neighborSet v // ω (rootFreeConstraint I v u) = true} :=
    { toFun := fun u => ⟨⟨u.1, hle u.2⟩,
        (active_union_root_adj_iff_coin I X Y ω v ⟨u.1, hle u.2⟩ hroot
          (hagree u.1 (hle u.2).ne.symm)).mp u.2⟩
      invFun := fun u => ⟨u.1.1,
        (active_union_root_adj_iff_coin I X Y ω v u.1 hroot
          (hagree u.1.1 u.1.2.ne.symm)).mpr u.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc := Fintype.card_congr e
  change (H.degree v : ℝ) = _
  rw [← SimpleGraph.card_neighborSet_eq_degree, hc]
  simp only [Fintype.card_subtype, Finset.natCast_card_filter, rootFreeCoinCount]

end
end ZeroFreeness
