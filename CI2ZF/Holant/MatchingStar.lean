import CI2ZF.Holant.Corollaries

/-!
# Degree dependence of b-matching widths (main.tex, `rem:matching-degree-dependence`)

For ordinary matchings (`b ≡ 1`) on the star `K_{1,Δ}` the diagonal
matching partition function is `1 + Δ z`.  Its zero `-1/Δ` lies in
`U_ε([0,R])` as soon as `ε > 1/Δ`, so every width `ε` for which the
conclusion of `bmatching_uniform_polytube` holds satisfies `ε ≤ 1/Δ`.
In particular no single width works for all maximum degrees.

The star is realized on `ULift (Option (Fin Δ))`, with centre `none` and
leaves `some i`, so that it lives in every universe used by
`bmatching_uniform_polytube`.
-/

namespace CI2ZF.Holant
open Finset CI2ZF.Holant
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

universe u

/-- The centre of the star. -/
def centre (Δ : ℕ) : ULift.{u} (Option (Fin Δ)) := ⟨none⟩

/-- The star `K_{1,Δ}`: the centre is adjacent to every leaf, and there are
no other edges. -/
def star (Δ : ℕ) : SimpleGraph (ULift.{u} (Option (Fin Δ))) where
  Adj x y := x ≠ y ∧ (x = centre Δ ∨ y = centre Δ)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem star_adj {Δ : ℕ} (x y : ULift.{u} (Option (Fin Δ))) :
    (star.{u} Δ).Adj x y ↔ x ≠ y ∧ (x = centre Δ ∨ y = centre Δ) := Iff.rfl

theorem centre_mem_of_mem_edgeFinset {Δ : ℕ} {e : Sym2 (ULift.{u} (Option (Fin Δ)))}
    (he : e ∈ (star.{u} Δ).edgeFinset) : centre Δ ∈ e := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, star_adj] at he
    rcases he.2 with h | h
    · rw [h]; exact Sym2.mem_mk_left _ _
    · rw [h]; exact Sym2.mem_mk_right _ _

theorem card_univ_star (Δ : ℕ) : Fintype.card (ULift.{u} (Option (Fin Δ))) = Δ + 1 := by
  simp

theorem neighborFinset_centre (Δ : ℕ) :
    (star.{u} Δ).neighborFinset (centre Δ) = univ.erase (centre Δ) := by
  ext y
  rw [SimpleGraph.mem_neighborFinset, star_adj, mem_erase]
  constructor
  · rintro ⟨h, -⟩
    exact ⟨fun hy => h hy.symm, mem_univ _⟩
  · rintro ⟨hy, -⟩
    exact ⟨fun h => hy h.symm, Or.inl rfl⟩

theorem degree_centre (Δ : ℕ) : (star.{u} Δ).degree (centre Δ) = Δ := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_centre,
    card_erase_of_mem (mem_univ _), card_univ, card_univ_star]
  simp

theorem neighborFinset_leaf {Δ : ℕ} {x : ULift.{u} (Option (Fin Δ))} (hx : x ≠ centre Δ) :
    (star.{u} Δ).neighborFinset x = {centre Δ} := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, star_adj, mem_singleton]
  constructor
  · rintro ⟨-, h | h⟩
    · exact absurd h hx
    · exact h
  · rintro rfl
    exact ⟨hx, Or.inr rfl⟩

theorem degree_leaf {Δ : ℕ} {x : ULift.{u} (Option (Fin Δ))} (hx : x ≠ centre Δ) :
    (star.{u} Δ).degree x = 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_leaf hx, card_singleton]

/-- The star has maximum degree at most `Δ` (for `Δ ≥ 1`). -/
theorem star_degree_le {Δ : ℕ} (hΔ : 1 ≤ Δ) (x : ULift.{u} (Option (Fin Δ))) :
    (star.{u} Δ).degree x ≤ Δ := by
  by_cases hx : x = centre Δ
  · rw [hx, degree_centre]
  · rw [degree_leaf hx]; exact hΔ

/-- Every vertex has degree at least one, so `b ≡ 1` is an admissible capacity. -/
theorem one_le_star_degree {Δ : ℕ} (hΔ : 1 ≤ Δ) (x : ULift.{u} (Option (Fin Δ))) :
    1 ≤ (star.{u} Δ).degree x := by
  by_cases hx : x = centre Δ
  · rw [hx, degree_centre]; exact hΔ
  · rw [degree_leaf hx]

/-- The star has exactly `Δ` edges: they are the edges at the centre. -/
theorem card_edgeFinset_star (Δ : ℕ) : (star.{u} Δ).edgeFinset.card = Δ := by
  have h : (star.{u} Δ).edgeFinset = (star.{u} Δ).incidenceFinset (centre Δ) := by
    ext e
    rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, SimpleGraph.mem_edgeFinset]
    change _ ↔ _ ∧ _
    constructor
    · intro he
      exact ⟨he, centre_mem_of_mem_edgeFinset (SimpleGraph.mem_edgeFinset.mpr he)⟩
    · exact fun h => h.1
  rw [h, SimpleGraph.card_incidenceFinset_eq_degree, degree_centre]

theorem selectedDegree_le_card {V E : Type*} [DecidableEq E] (inc : E → V → Prop)
    (S : Finset E) (v : V) : selectedDegree inc S v ≤ S.card :=
  card_filter_le _ _

theorem selectedDegree_centre {Δ : ℕ} {S : Finset (Sym2 (ULift.{u} (Option (Fin Δ))))}
    (hS : S ⊆ (star.{u} Δ).edgeFinset) :
    selectedDegree graphIncidence S (centre Δ) = S.card := by
  unfold selectedDegree
  rw [filter_true_of_mem]
  intro e he
  exact centre_mem_of_mem_edgeFinset (hS he)

/-- A set of star edges is a matching iff it has at most one edge. -/
theorem star_matching_iff {Δ : ℕ} {S : Finset (Sym2 (ULift.{u} (Option (Fin Δ))))}
    (hS : S ⊆ (star.{u} Δ).edgeFinset) :
    (∀ v, selectedDegree graphIncidence S v ≤ 1) ↔ S.card ≤ 1 := by
  constructor
  · intro h
    have := h (centre Δ)
    rwa [selectedDegree_centre hS] at this
  · intro h v
    exact (selectedDegree_le_card _ S v).trans h

theorem sum_choose_le_one (n : ℕ) (z : ℂ) :
    ∑ m ∈ range (n + 1), (n.choose m) • (if m ≤ 1 then z ^ m else 0) = 1 + n * z := by
  rcases n with _ | n
  · simp
  · rw [sum_range_succ', sum_range_succ']
    have hrest : ∑ m ∈ range n, ((n + 1).choose (m + 1 + 1)) •
        (if m + 1 + 1 ≤ 1 then z ^ (m + 1 + 1) else 0) = 0 := by
      apply sum_eq_zero
      intro m _
      simp
    rw [hrest]
    simp [add_comm]

/-- **The diagonal matching polynomial of `K_{1,Δ}` is `1 + Δ z`.** -/
theorem star_matchingPartition_diagonal (Δ : ℕ) (z : ℂ) :
    matchingPartition graphIncidence (star.{u} Δ).edgeFinset (fun _ => 1) (fun _ => z) =
      1 + Δ * z := by
  unfold matchingPartition
  have hcongr : ∀ S ∈ (star.{u} Δ).edgeFinset.powerset,
      (if ∀ v, selectedDegree graphIncidence S v ≤ 1 then ∏ _e ∈ S, z else 0) =
        (fun m : ℕ => if m ≤ 1 then z ^ m else 0) S.card := by
    intro S hS
    rw [mem_powerset] at hS
    simp only [star_matching_iff hS, prod_const]
  rw [sum_congr rfl hcongr,
    sum_powerset_apply_card (fun m : ℕ => if m ≤ 1 then z ^ m else 0), card_edgeFinset_star]
  exact sum_choose_le_one Δ z

/-- The point `-1/Δ` is a zero of the diagonal matching polynomial of the star. -/
theorem star_matchingPartition_zero {Δ : ℕ} (hΔ : 1 ≤ Δ) :
    matchingPartition graphIncidence (star.{u} Δ).edgeFinset (fun _ => 1)
      (fun _ => ((-1 / (Δ : ℝ) : ℝ) : ℂ)) = 0 := by
  rw [star_matchingPartition_diagonal]
  have hΔ0 : (Δ : ℂ) ≠ 0 := by exact_mod_cast (show Δ ≠ 0 by omega)
  push_cast
  field_simp
  ring

/-- For `ε > 1/Δ` and `R ≥ 0`, the constant vector `-1/Δ` lies in the
edge polytube `U_ε([0,R])^E` of the star. -/
theorem neg_inv_mem_edgePolytube {Δ : ℕ} (hΔ : 1 ≤ Δ) {ε R : ℝ} (hR : 0 ≤ R)
    (hε : 1 / (Δ : ℝ) < ε) :
    (fun _ => ((-1 / (Δ : ℝ) : ℝ) : ℂ)) ∈
      edgePolytube (star.{u} Δ).edgeFinset ε 0 R := by
  rw [mem_edgePolytube_iff]
  intro e _
  refine ⟨0, ⟨le_rfl, hR⟩, ?_⟩
  have hΔpos : (0 : ℝ) < Δ := by exact_mod_cast (show 0 < Δ by omega)
  simp only [Complex.ofReal_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_neg (by rw [neg_div]; exact neg_neg_of_pos (by positivity)), neg_div, neg_neg]
  exact hε

/-- **The conclusion of `bmatching_uniform_polytube` fails for `ε > 1/Δ`.**
For every `R ≥ 0`, the star `K_{1,Δ}`, the capacity `b ≡ 1` and the
constant activity `-1/Δ ∈ U_ε([0,R])` give a zero. -/
theorem bmatching_polytube_fails {Δ : ℕ} (hΔ : 1 ≤ Δ) {ε R : ℝ} (hR : 0 ≤ R)
    (hε : 1 / (Δ : ℝ) < ε) :
    ¬ ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ v, G.degree v ≤ Δ) → ∀ b : V → ℕ, (∀ v, b v ≤ G.degree v) →
        ∀ z ∈ edgePolytube G.edgeFinset ε 0 R,
          matchingPartition graphIncidence G.edgeFinset b z ≠ 0 := by
  intro h
  exact h (ULift.{u} (Option (Fin Δ))) (star.{u} Δ) (star_degree_le hΔ) (fun _ => 1)
    (one_le_star_degree hΔ) _ (neg_inv_mem_edgePolytube hΔ hR hε)
    (star_matchingPartition_zero hΔ)

/-- **Width bound of `rem:matching-degree-dependence`.**  Every width for
which the b-matching zero-freeness conclusion holds on `U_ε([0,R])`
satisfies `ε ≤ 1/Δ`. -/
theorem bmatching_width_le_inv {Δ : ℕ} (hΔ : 1 ≤ Δ) {ε R : ℝ} (hR : 0 ≤ R)
    (h : ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ v, G.degree v ≤ Δ) → ∀ b : V → ℕ, (∀ v, b v ≤ G.degree v) →
        ∀ z ∈ edgePolytube G.edgeFinset ε 0 R,
          matchingPartition graphIncidence G.edgeFinset b z ≠ 0) :
    ε ≤ 1 / Δ := by
  by_contra hlt
  exact bmatching_polytube_fails hΔ hR (lt_of_not_ge hlt) h

/-- The width produced by `bmatching_uniform_polytube` obeys the bound:
for every `R > 0` there is a valid width, and every valid width lies in
`(0, 1/Δ]`. -/
theorem bmatching_uniform_polytube_width (Δ : ℕ) (hΔ : 1 ≤ Δ) {R : ℝ} (hR : 0 < R) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / (Δ : ℝ) ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        (∀ v, G.degree v ≤ Δ) → ∀ b : V → ℕ, (∀ v, b v ≤ G.degree v) →
          ∀ z ∈ edgePolytube G.edgeFinset ε 0 R,
            matchingPartition graphIncidence G.edgeFinset b z ≠ 0 := by
  obtain ⟨ε, hε, h⟩ := bmatching_uniform_polytube.{u} Δ hR
  exact ⟨ε, hε, bmatching_width_le_inv hΔ hR.le h, h⟩

/-- **Dependence on the maximum degree is unavoidable.**  For no `R ≥ 0`
is there a single positive width valid for all maximum degrees. -/
theorem no_degree_free_width {R : ℝ} (hR : 0 ≤ R) :
    ¬ ∃ ε > 0, ∀ Δ : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ v, G.degree v ≤ Δ) → ∀ b : V → ℕ, (∀ v, b v ≤ G.degree v) →
        ∀ z ∈ edgePolytube G.edgeFinset ε 0 R,
          matchingPartition graphIncidence G.edgeFinset b z ≠ 0 := by
  rintro ⟨ε, hε, h⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  have hn1 : 1 ≤ n + 1 := Nat.le_add_left 1 n
  have hle := bmatching_width_le_inv hn1 hR (h (n + 1))
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have : ε * ((n + 1 : ℕ) : ℝ) ≤ 1 := by
    rw [le_div_iff₀ hpos] at hle
    exact hle
  have h2 : 1 < ε * ((n + 1 : ℕ) : ℝ) := by
    rw [div_lt_iff₀ hε] at hn
    push_cast
    nlinarith
  linarith

end
end CI2ZF.Holant
