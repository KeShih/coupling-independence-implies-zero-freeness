import CI2ZF.Potts.Model.PottsModel

/-!
# Conditional marginals of order `x^k` (main.tex, lines 345-349)

`main.tex` remarks that the marginal lower bound of CFFGZZ Observation 10
need not stay bounded away from zero as `x ↓ 0`: a colour `c` appearing on
`k ≥ 1` pinned neighbours of a free vertex `v` has conditional marginal of
order `x^k` at `v`.

`marginal tau G x r c` below is the actual Gibbs probability, under the
pinned Potts law at activity `x`, that the free vertex `r` has colour `c`
(`marginal_eq_gibbs`).  With `k = tau.boundaryCount G r c` the number of
pinned neighbours of `r` with colour `c` and `q > deg_G(r)`:

* `marginal_le_pow`: for every graph, pinning and `x ∈ (0,1]`,
  `marginal ≤ x^k` (free neighbours allowed);
* `marginal_tendsto_zero`, `marginal_not_bounded_below`: if `k ≥ 1`, the
  marginal tends to `0` as `x ↓ 0`, so no positive lower bound is uniform in `x`;
* `marginal_order_pow`: under the paper's standing hypothesis
  `q ≥ Δ + 1` (maximum degree at most `Δ`), for every `x ∈ (0,1]`,
  `x^k / q^n ≤ marginal ≤ x^k`, with `n` the number of free vertices; so the
  marginal is of order exactly `x^k` as `x ↓ 0`;
* `marginal_eq_of_no_free_neighbour`, `marginal_bounds_of_no_free_neighbour`:
  if every neighbour of `r` is pinned, the marginal equals
  `x^{k_c} / ∑_a x^{k_a}` and lies in `[x^k / q, x^k]`.

The lower bound uses `q ≥ Δ + 1` to extend the root colour `c` to a
configuration with no conflicts other than the `k` forced ones.  (Without
it a free neighbour could be forced to colour `c` by its own pinned
neighbours, and the marginal could be of smaller order.)
-/

namespace CI2ZF.Potts
open Finset PottsCI CI2ZF.Potts Filter Topology
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {V C : Type*} [Fintype V] [Fintype C]

/-- The conditional marginal of colour `c` at the free vertex `r`, at
activity `x`, under the pinning `tau`. -/
def marginal (tau : PartialColouring V C) (G : SimpleGraph V) (x : ℝ)
    (r : tau.FreeVertex) (c : C) : ℝ :=
  (∑ σ : tau.FreeVertex → C, if σ r = c then (tau.toPinningData G).weight x σ else 0) /
    (tau.toPinningData G).partition x

/-- The marginal is the Gibbs probability of the event `σ r = c`. -/
theorem marginal_eq_gibbs [Nonempty C] (tau : PartialColouring V C) (G : SimpleGraph V)
    {x : ℝ} (hx : 0 < x) (r : tau.FreeVertex) (c : C) :
    marginal tau G x r c =
      ∑ σ, if σ r = c then ((tau.toPinningData G).gibbs x hx.le
        ((tau.toPinningData G).partition_pos_of_parameter_pos hx)).w σ else 0 := by
  unfold marginal
  rw [Finset.sum_div]
  apply sum_congr rfl
  intro σ _
  split_ifs
  · rfl
  · simp

variable (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex)

/-- The weight splits into the root factor and the root-child exponent. -/
theorem weight_eq_root (x : ℝ) (σ : tau.FreeVertex → C) :
    (tau.toPinningData G).weight x σ =
      x ^ tau.boundaryCount G r (σ r) * x ^ rootChildExponent tau G r σ := by
  rw [tau.childWeight_eq_pow G x σ, ← pow_add, root_exponent_split tau G r σ, pow_add]

/-- Colours of the neighbours of `r` (pinned and free) under `σ`. -/
def nbrColours (σ : tau.FreeVertex → C) : Finset C :=
  (G.neighborFinset r.1).image (tau.extend σ)

theorem exists_free_colour (hdeg : G.degree r.1 < Fintype.card C) (σ : tau.FreeVertex → C) :
    ∃ a, a ∉ nbrColours tau G r σ := by
  have hcard : (nbrColours tau G r σ).card < (univ : Finset C).card := by
    rw [card_univ]
    exact card_image_le.trans_lt (by rwa [SimpleGraph.card_neighborFinset_eq_degree])
  obtain ⟨a, _, ha⟩ := exists_mem_notMem_of_card_lt_card hcard
  exact ⟨a, ha⟩

variable {tau G r}

theorem boundaryCount_eq_zero_of_not_mem {σ : tau.FreeVertex → C} {a : C}
    (ha : a ∉ nbrColours tau G r σ) : tau.boundaryCount G r a = 0 := by
  unfold PartialColouring.boundaryCount
  rw [card_eq_zero, filter_eq_empty_iff]
  intro p hp hpa
  apply ha
  unfold nbrColours
  rw [mem_image]
  refine ⟨p.1, ?_, ?_⟩
  · rw [SimpleGraph.mem_neighborFinset]
    exact (mem_filter.mp hp).2
  · rw [tau.extend_of_mem σ p.2]
    exact hpa

theorem free_adj {u w : tau.FreeVertex} (h : (tau.freeGraph G).Adj u w) : G.Adj u.1 w.1 := h

theorem freeConflictCount_update_le {σ : tau.FreeVertex → C} {a : C}
    (ha : a ∉ nbrColours tau G r σ) :
    tau.freeConflictCount G (Function.update σ r a) ≤ tau.freeConflictCount G σ := by
  unfold PartialColouring.freeConflictCount
  apply card_le_card
  intro e he
  rw [mem_filter] at he ⊢
  obtain ⟨he1, he2⟩ := he
  refine ⟨he1, ?_⟩
  induction e using Sym2.ind with
  | _ u w =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he1
    have hadj := free_adj he1
    rw [PartialColouring.sameColour_mk] at he2 ⊢
    have hne : u ≠ w := he1.ne
    by_cases hu : u = r
    · subst hu
      rw [Function.update_self, Function.update_of_ne hne.symm] at he2
      exfalso
      apply ha
      refine mem_image.mpr ⟨w.1, (SimpleGraph.mem_neighborFinset _ _ _).mpr hadj, ?_⟩
      rw [tau.extend_of_not_mem σ w.2]
      exact he2.symm
    · by_cases hw : w = r
      · subst hw
        rw [Function.update_self, Function.update_of_ne hne] at he2
        exfalso
        apply ha
        refine mem_image.mpr ⟨u.1, (SimpleGraph.mem_neighborFinset _ _ _).mpr hadj.symm, ?_⟩
        rw [tau.extend_of_not_mem σ u.2]
        exact he2
      · rwa [Function.update_of_ne hu, Function.update_of_ne hw] at he2

theorem sum_erase_update (σ : tau.FreeVertex → C) (a : C) :
    ∑ u ∈ univ.erase r, tau.boundaryCount G u (Function.update σ r a u) =
      ∑ u ∈ univ.erase r, tau.boundaryCount G u (σ u) := by
  apply sum_congr rfl
  intro u hu
  rw [Function.update_of_ne (ne_of_mem_erase hu)]

theorem rootChildExponent_update_le {σ : tau.FreeVertex → C} {a : C}
    (ha : a ∉ nbrColours tau G r σ) :
    rootChildExponent tau G r (Function.update σ r a) ≤ rootChildExponent tau G r σ := by
  unfold rootChildExponent
  rw [sum_erase_update]
  have := freeConflictCount_update_le ha
  omega

/-- **Upper bound `x^k`.**  For every finite graph, every pinning, every
free vertex `r` with `deg_G(r) < q` and every `x ∈ (0,1]`, the conditional
marginal of a colour `c` at `r` is at most `x^k`, where `k` is the number
of pinned neighbours of `r` with colour `c`. -/
theorem marginal_le_pow [Nonempty C] {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (c : C)
    (hdeg : G.degree r.1 < Fintype.card C) :
    marginal tau G x r c ≤ x ^ tau.boundaryCount G r c := by
  choose a ha using exists_free_colour tau G r hdeg
  set I := tau.toPinningData G with hI
  have hZ : 0 < I.partition x := I.partition_pos_of_parameter_pos hx0
  unfold marginal
  rw [← hI, div_le_iff₀ hZ]
  let f : (tau.FreeVertex → C) → (tau.FreeVertex → C) := fun σ => Function.update σ r (a σ)
  let S := univ.filter (fun σ : tau.FreeVertex → C => σ r = c)
  have hsum : (∑ σ, if σ r = c then I.weight x σ else 0) = ∑ σ ∈ S, I.weight x σ := by
    rw [sum_filter]
  have hstep : ∀ σ ∈ S, I.weight x σ ≤ x ^ tau.boundaryCount G r c * I.weight x (f σ) := by
    intro σ hσ
    have hσr : σ r = c := (mem_filter.mp hσ).2
    rw [hI, weight_eq_root tau G r x σ, weight_eq_root tau G r x (f σ), hσr]
    have hfr : f σ r = a σ := Function.update_self _ _ _
    rw [hfr, boundaryCount_eq_zero_of_not_mem (ha σ), pow_zero, one_mul]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hx0.le _)
    exact pow_le_pow_of_le_one hx0.le hx1 (rootChildExponent_update_le (ha σ))
  have hinj : Set.InjOn f S := by
    intro σ hσ σ' hσ' h
    have hσr : σ r = c := (mem_filter.mp hσ).2
    have hσr' : σ' r = c := (mem_filter.mp hσ').2
    funext u
    by_cases hu : u = r
    · rw [hu, hσr, hσr']
    · have := congrFun h u
      simpa only [f, Function.update_of_ne hu] using this
  rw [hsum]
  calc ∑ σ ∈ S, I.weight x σ ≤ ∑ σ ∈ S, x ^ tau.boundaryCount G r c * I.weight x (f σ) :=
        sum_le_sum hstep
    _ = x ^ tau.boundaryCount G r c * ∑ τ ∈ S.image f, I.weight x τ := by
        rw [← mul_sum, sum_image hinj]
    _ ≤ x ^ tau.boundaryCount G r c * I.partition x := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hx0.le _)
        exact sum_le_sum_of_subset_of_nonneg (subset_univ _)
          (fun τ _ _ => I.weight_nonneg hx0.le τ)

theorem marginal_nonneg {x : ℝ} (hx0 : 0 ≤ x) (c : C) : 0 ≤ marginal tau G x r c := by
  unfold marginal
  apply div_nonneg
  · apply sum_nonneg
    intro σ _
    split_ifs
    · exact (tau.toPinningData G).weight_nonneg hx0 σ
    · exact le_rfl
  · exact (tau.toPinningData G).partition_nonneg hx0

/-- **The marginal tends to zero as `x ↓ 0`** when `c` appears on at
least one pinned neighbour of `r` (and `deg_G(r) < q`). -/
theorem marginal_tendsto_zero [Nonempty C] (c : C) (hk : 1 ≤ tau.boundaryCount G r c)
    (hdeg : G.degree r.1 < Fintype.card C) :
    Tendsto (fun x => marginal tau G x r c) (𝓝[>] 0) (𝓝 0) := by
  have hpow : Tendsto (fun x : ℝ => x ^ tau.boundaryCount G r c) (𝓝[>] 0) (𝓝 0) := by
    have h := ((continuous_pow (tau.boundaryCount G r c)).tendsto (0 : ℝ))
    rw [zero_pow (by omega)] at h
    exact h.mono_left nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hpow
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact marginal_nonneg (le_of_lt hx) c
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact marginal_le_pow hx.1 hx.2.le c hdeg

/-- **No lower bound uniform in `x`.** -/
theorem marginal_not_bounded_below [Nonempty C] (c : C) (hk : 1 ≤ tau.boundaryCount G r c)
    (hdeg : G.degree r.1 < Fintype.card C) :
    ∀ m > 0, ∃ x ∈ Set.Ioc (0 : ℝ) 1, marginal tau G x r c < m := by
  intro m hm
  refine ⟨min 1 (m / 2), ⟨lt_min one_pos (by positivity), min_le_left _ _⟩, ?_⟩
  have hx0 : 0 < min 1 (m / 2) := lt_min one_pos (by positivity)
  have hx1 : min 1 (m / 2) ≤ 1 := min_le_left _ _
  calc marginal tau G (min 1 (m / 2)) r c
      ≤ min 1 (m / 2) ^ tau.boundaryCount G r c := marginal_le_pow hx0 hx1 c hdeg
    _ ≤ min 1 (m / 2) := pow_le_of_le_one hx0.le hx1 (by omega)
    _ ≤ m / 2 := min_le_right _ _
    _ < m := by linarith

/-! ## All neighbours pinned: the exact marginal -/

theorem freeConflictCount_update_of_isolated (hiso : ∀ u : tau.FreeVertex, ¬ G.Adj r.1 u.1)
    (σ : tau.FreeVertex → C) (a : C) :
    tau.freeConflictCount G (Function.update σ r a) = tau.freeConflictCount G σ := by
  unfold PartialColouring.freeConflictCount
  congr 1
  apply filter_congr
  intro e he
  induction e using Sym2.ind with
  | _ u w =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    have hadj := free_adj he
    have hu : u ≠ r := by
      rintro rfl
      exact hiso w hadj
    have hw : w ≠ r := by
      rintro rfl
      exact hiso u hadj.symm
    rw [PartialColouring.sameColour_mk, PartialColouring.sameColour_mk,
      Function.update_of_ne hu, Function.update_of_ne hw]

theorem rootChildExponent_update_of_isolated (hiso : ∀ u : tau.FreeVertex, ¬ G.Adj r.1 u.1)
    (σ : tau.FreeVertex → C) (a : C) :
    rootChildExponent tau G r (Function.update σ r a) = rootChildExponent tau G r σ := by
  unfold rootChildExponent
  rw [sum_erase_update, freeConflictCount_update_of_isolated hiso]

/-- **Exact marginal when every neighbour of `r` is pinned:**
`P(σ r = c) = x^{k_c} / ∑_a x^{k_a}`. -/
theorem marginal_eq_of_no_free_neighbour [Nonempty C] {x : ℝ} (hx0 : 0 < x) (c : C)
    (hiso : ∀ u : tau.FreeVertex, ¬ G.Adj r.1 u.1) :
    marginal tau G x r c =
      x ^ tau.boundaryCount G r c / ∑ a, x ^ tau.boundaryCount G r a := by
  set I := tau.toPinningData G with hI
  let g : (tau.FreeVertex → C) → ℝ := fun σ => x ^ rootChildExponent tau G r σ
  let T : C → ℝ := fun a => ∑ σ ∈ univ.filter (fun σ : tau.FreeVertex → C => σ r = a), g σ
  have hT (a : C) : T a = T c := by
    apply sum_nbij' (fun σ => Function.update σ r c) (fun σ => Function.update σ r a)
    · intro σ _
      simp
    · intro σ _
      simp
    · intro σ hσ
      have hσr : σ r = a := (mem_filter.mp (mem_coe.mp hσ)).2
      rw [Function.update_idem, ← hσr, Function.update_eq_self]
    · intro σ hσ
      have hσr : σ r = c := (mem_filter.mp (mem_coe.mp hσ)).2
      rw [Function.update_idem, ← hσr, Function.update_eq_self]
    · intro σ _
      simp only [g]
      rw [rootChildExponent_update_of_isolated hiso]
  have hfib (a : C) : ∑ σ ∈ univ.filter (fun σ : tau.FreeVertex → C => σ r = a), I.weight x σ =
      x ^ tau.boundaryCount G r a * T c := by
    rw [← hT a, mul_sum]
    apply sum_congr rfl
    intro σ hσ
    have hσr : σ r = a := (mem_filter.mp hσ).2
    rw [hI, weight_eq_root tau G r x σ, hσr]
  have hZ : I.partition x = (∑ a, x ^ tau.boundaryCount G r a) * T c := by
    unfold PinningData.partition
    rw [← sum_fiberwise univ (fun σ : tau.FreeVertex → C => σ r) (I.weight x), sum_mul]
    exact sum_congr rfl fun a _ => hfib a
  have hTpos : 0 < T c := by
    apply sum_pos
    · intro σ _
      exact pow_pos hx0 _
    · exact ⟨fun _ => c, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
  unfold marginal
  rw [← hI, hZ, ← sum_filter, hfib c, mul_div_mul_right _ _ hTpos.ne']

/-- **Two-sided bound of order `x^k`** when every neighbour of `r` is
pinned: `x^k / q ≤ P(σ r = c) ≤ x^k` for `x ∈ (0,1]`, `q = |C| > deg_G(r)`. -/
theorem marginal_bounds_of_no_free_neighbour [Nonempty C] {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (c : C) (hdeg : G.degree r.1 < Fintype.card C)
    (hiso : ∀ u : tau.FreeVertex, ¬ G.Adj r.1 u.1) :
    x ^ tau.boundaryCount G r c / Fintype.card C ≤ marginal tau G x r c ∧
      marginal tau G x r c ≤ x ^ tau.boundaryCount G r c := by
  refine ⟨?_, marginal_le_pow hx0 hx1 c hdeg⟩
  rw [marginal_eq_of_no_free_neighbour hx0 c hiso]
  obtain ⟨a, ha⟩ := exists_free_colour tau G r hdeg (fun _ => c)
  have hD1 : 1 ≤ ∑ b, x ^ tau.boundaryCount G r b := by
    calc (1 : ℝ) = x ^ tau.boundaryCount G r a := by
          rw [boundaryCount_eq_zero_of_not_mem ha, pow_zero]
      _ ≤ ∑ b, x ^ tau.boundaryCount G r b :=
          single_le_sum (f := fun b => x ^ tau.boundaryCount G r b)
            (fun b _ => pow_nonneg hx0.le _) (mem_univ a)
  have hDq : ∑ b, x ^ tau.boundaryCount G r b ≤ Fintype.card C := by
    calc ∑ b, x ^ tau.boundaryCount G r b ≤ ∑ _b : C, (1 : ℝ) :=
          sum_le_sum fun b _ => pow_le_one₀ hx0.le hx1
      _ = Fintype.card C := by simp
  exact div_le_div_of_nonneg_left (pow_nonneg hx0.le _) (by linarith) hDq

/-! ## The general two-sided bound under `q ≥ Δ + 1` -/

/-- Some configuration with `σ r = c` has exactly the `k` forced conflicts. -/
theorem exists_config_weight_eq_pow [Nonempty C] {Δ : ℕ} (hdeg : ∀ v, G.degree v ≤ Δ)
    (hq : Δ + 1 ≤ Fintype.card C) (x : ℝ) (c : C) :
    ∃ σ : tau.FreeVertex → C, σ r = c ∧
      (tau.toPinningData G).weight x σ = x ^ tau.boundaryCount G r c := by
  obtain ⟨η, hη⟩ := exists_hardAdmissible_of_succ_le ((pinVertex tau r c).toPinningData G)
    ((pinVertex tau r c).degreeBound_of_original G hdeg) hq
  have h1 := ((pinVertex tau r c).toPinningData G).weight_zero_eq η
  rw [if_pos hη, (pinVertex tau r c).childWeight_eq_pow G 0 η] at h1
  have hb : (pinVertex tau r c).boundaryConflictCount G η = 0 := by
    by_contra hne
    rw [zero_pow hne, zero_mul] at h1
    exact zero_ne_one h1
  have hf : (pinVertex tau r c).freeConflictCount G η = 0 := by
    by_contra hne
    rw [zero_pow hne, mul_zero] at h1
    exact zero_ne_one h1
  have hexp := child_exponent_pinVertex tau G r c η
  rw [hb, hf] at hexp
  refine ⟨childToParent tau r c η, childToParent_root tau r c η, ?_⟩
  rw [weight_eq_root tau G r x, childToParent_root, ← hexp, pow_zero, mul_one]

/-- **Conditional marginal of order `x^k`.**  For a graph of maximum degree
at most `Δ`, `q = |C| ≥ Δ + 1` colours, any pinning and any free vertex
`r`, the marginal of `c` at `r` satisfies, for every `x ∈ (0,1]`,
`x^k / q^n ≤ P_x(σ r = c) ≤ x^k`, where `k` is the number of pinned
neighbours of `r` coloured `c` and `n` is the number of free vertices.
The constants do not depend on `x`, so the marginal is of order exactly
`x^k` as `x ↓ 0`. -/
theorem marginal_order_pow [Nonempty C] {Δ : ℕ} (hdeg : ∀ v, G.degree v ≤ Δ)
    (hq : Δ + 1 ≤ Fintype.card C) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (c : C) :
    x ^ tau.boundaryCount G r c / (Fintype.card C : ℝ) ^ Fintype.card tau.FreeVertex ≤
        marginal tau G x r c ∧
      marginal tau G x r c ≤ x ^ tau.boundaryCount G r c := by
  refine ⟨?_, marginal_le_pow hx0 hx1 c (by have := hdeg r.1; omega)⟩
  set I := tau.toPinningData G with hI
  have hZ : 0 < I.partition x := I.partition_pos_of_parameter_pos hx0
  obtain ⟨σ, hσr, hσw⟩ := exists_config_weight_eq_pow (tau := tau) (r := r) hdeg hq x c
  have hnum : x ^ tau.boundaryCount G r c ≤
      ∑ σ : tau.FreeVertex → C, if σ r = c then I.weight x σ else 0 :=
    calc x ^ tau.boundaryCount G r c = (if σ r = c then I.weight x σ else 0) := by
          rw [if_pos hσr, hσw]
      _ ≤ _ := single_le_sum (f := fun σ' : tau.FreeVertex → C =>
          if σ' r = c then I.weight x σ' else 0)
          (fun σ' _ => ite_nonneg (I.weight_nonneg hx0.le σ') le_rfl) (mem_univ σ)
  have hZle : I.partition x ≤ (Fintype.card C : ℝ) ^ Fintype.card tau.FreeVertex := by
    unfold PinningData.partition
    calc ∑ σ, I.weight x σ ≤ ∑ _σ : tau.FreeVertex → C, (1 : ℝ) := by
          apply sum_le_sum
          intro σ _
          rw [hI, tau.childWeight_eq_pow G x σ]
          exact mul_le_one₀ (pow_le_one₀ hx0.le hx1) (pow_nonneg hx0.le _)
            (pow_le_one₀ hx0.le hx1)
      _ = (Fintype.card C : ℝ) ^ Fintype.card tau.FreeVertex := by
          simp
  unfold marginal
  rw [← hI]
  calc x ^ tau.boundaryCount G r c / (Fintype.card C : ℝ) ^ Fintype.card tau.FreeVertex
      ≤ x ^ tau.boundaryCount G r c / I.partition x :=
        div_le_div_of_nonneg_left (pow_nonneg hx0.le _) hZ hZle
    _ ≤ _ := div_le_div_of_nonneg_right hnum hZ.le

end
end CI2ZF.Potts
