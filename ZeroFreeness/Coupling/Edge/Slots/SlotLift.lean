/-
Lemmas 8.3 (`lem:slot-fact`) and 8.4 (`lem:edge-slot-lift`) of the companion
paper, `companion/appendices/edge-potts.tex`, in their countable form.

* `slot_representation` (and `slot_representation_pnat`, slots `r ≥ 1`):
  Lemma 8.3.  Proved without the entire-function (Hadamard) argument of the
  paper: the library's real-rooted finite slot approximants have geometrically
  separated weights `κ_{n,i+1} < x κ_{n,i}`, so `κ_{n,i} ≤ x^i` uniformly;
  a pointwise convergent subsequence (Tychonoff) and dominated convergence
  give the countable law, and positivity of every weight follows from the
  identity itself.
* `SlotModel`: the countable endpoint-slot lift over lifted states
  `(c,r,s) ∈ C × ℕ × ℕ`, with occupied-label sets, admissibility, weights,
  partition sums over the countable space `F → C × ℕ × ℕ`, the normalized law,
  the bounds (load), (fibre), (slack), pinning, and reachability.
* `lem_edge_slot_lift`: Lemma 8.4, all three assertions, for every slot law
  satisfying Lemma 8.3 and every ordering of the endpoints of the free edges;
  `lem_edge_slot_lift_exists` combines it with Lemma 8.3.
-/
import ZeroFreeness.Coupling.Edge.Slots.SimpleGraphBounds
import ZeroFreeness.Coupling.Edge.Slots.Approximation
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Sequences

namespace ZeroFreeness.Appendix.Edge

open ZeroFreeness.Appendix.Edge Polynomial Filter Topology
open scoped BigOperators

noncomputable section

universe u

/-! ## Two general summation facts -/

/-- Tannery's theorem (dominated convergence for countable sums).  This is a
verbatim copy of mathlib's `tendsto_tsum_of_dominated_convergence`, whose
module is not part of the prebuilt mathlib used by this project. -/
lemma tendsto_tsum_dominated {α β G : Type*} {𝓕 : Filter α}
    [NormedAddCommGroup G] [CompleteSpace G]
    {f : α → β → G} {g : β → G} {bound : β → ℝ} (h_sum : Summable bound)
    (hab : ∀ k : β, Tendsto (f · k) 𝓕 (𝓝 (g k)))
    (h_bound : ∀ᶠ n in 𝓕, ∀ k, ‖f n k‖ ≤ bound k) :
    Tendsto (∑' k, f · k) 𝓕 (𝓝 (∑' k, g k)) := by
  rcases isEmpty_or_nonempty β
  · simpa only [tsum_empty] using tendsto_const_nhds
  rcases 𝓕.eq_or_neBot with rfl | _
  · simp only [tendsto_bot]
  have h_g_le (k : β) : ‖g k‖ ≤ bound k :=
    le_of_tendsto (tendsto_norm.comp (hab k)) <| h_bound.mono (fun n h => h k)
  have h_sumg : Summable (‖g ·‖) :=
    h_sum.of_norm_bounded (fun k ↦ (norm_norm (g k)).symm ▸ h_g_le k)
  have h_suma : ∀ᶠ n in 𝓕, Summable (‖f n ·‖) := by
    filter_upwards [h_bound] with n h
    exact h_sum.of_norm_bounded <| by simpa only [norm_norm] using h
  rw [Metric.tendsto_nhds]
  intro ε hε
  let ⟨S, hS⟩ := h_sum
  obtain ⟨T, hT⟩ : ∃ (T : Finset β), dist (∑ b ∈ T, bound b) S < ε / 3 := by
    rw [HasSum, Metric.tendsto_nhds] at hS
    exact Eventually.exists <| hS _ (by positivity)
  have h1 : ∑' (k : (Tᶜ : Set β)), bound k < ε / 3 := by
    calc _ ≤ ‖∑' (k : (Tᶜ : Set β)), bound k‖ := Real.le_norm_self _
         _ = ‖S - ∑ b ∈ T, bound b‖           := congrArg _ ?_
         _ < ε / 3                            := by rwa [dist_eq_norm, norm_sub_rev] at hT
    simpa only [h_sum.sum_add_tsum_compl, eq_sub_iff_add_eq'] using hS.tsum_eq
  have h2 : Tendsto (∑ k ∈ T, f · k) 𝓕 (𝓝 (T.sum g)) := tendsto_finsetSum _ (fun i _ ↦ hab i)
  rw [Metric.tendsto_nhds] at h2
  filter_upwards [h2 (ε / 3) (by positivity), h_suma, h_bound] with n hn h_suma h_bound
  rw [dist_eq_norm, ← h_suma.of_norm.tsum_sub h_sumg.of_norm,
    ← (h_suma.of_norm.sub h_sumg.of_norm).sum_add_tsum_compl (s := T),
    (by ring : ε = ε / 3 + (ε / 3 + ε / 3))]
  refine (norm_add_le _ _).trans_lt (add_lt_add ?_ ?_)
  · simpa only [dist_eq_norm, Finset.sum_sub_distrib] using hn
  · rw [(h_suma.subtype _).of_norm.tsum_sub (h_sumg.subtype _).of_norm]
    refine (norm_sub_le _ _).trans_lt (add_lt_add ?_ ?_)
    · refine ((norm_tsum_le_tsum_norm (h_suma.subtype _)).trans ?_).trans_lt h1
      exact (h_suma.subtype _).tsum_le_tsum (h_bound ·) (h_sum.subtype _)
    · refine ((norm_tsum_le_tsum_norm <| h_sumg.subtype _).trans ?_).trans_lt h1
      exact (h_sumg.subtype _).tsum_le_tsum (h_g_le ·) (h_sum.subtype _)

/-- Finite products of nonnegative countable sums, indexed by `Fin n`. -/
lemma hasSum_pi_prod_fin (n : ℕ) : ∀ {S : Fin n → Type u} (f : ∀ i, S i → ℝ) (a : Fin n → ℝ),
    (∀ i s, 0 ≤ f i s) → (∀ i, HasSum (f i) (a i)) →
    HasSum (fun ω : ∀ i, S i => ∏ i, f i (ω i)) (∏ i, a i) := by
  induction n with
  | zero =>
    intro S f a _ _
    simp
  | succ n ih =>
    intro S f a hf ha
    let g : (∀ i : Fin n, S i.succ) → ℝ := fun ω => ∏ i : Fin n, f i.succ (ω i)
    have ih' : HasSum g (∏ i : Fin n, a i.succ) :=
      ih (S := fun i => S i.succ) (fun i => f i.succ) (fun i => a i.succ)
      (fun i => hf i.succ) (fun i => ha i.succ)
    have h0 : HasSum (f 0) (a 0) := ha 0
    have h1 : 0 ≤ f 0 := fun s => hf 0 s
    have h2 : 0 ≤ g := fun ω => Finset.prod_nonneg fun i _ => hf i.succ (ω i)
    have hs := Summable.mul_of_nonneg h0.summable ih'.summable h1 h2
    have hmul := HasSum.mul h0 ih' hs
    have hprod : (∏ i, a i) = a 0 * ∏ i : Fin n, a i.succ := Fin.prod_univ_succ a
    have hfun : ((fun ω : ∀ i, S i => ∏ i, f i (ω i)) ∘ (Fin.consEquiv S)) =
        fun p : S 0 × (∀ i : Fin n, S i.succ) => f 0 p.1 * g p.2 := by
      funext p
      simp only [Function.comp_apply, Fin.prod_univ_succ, g]
      rfl
    rw [hprod, ← (Fin.consEquiv S).hasSum_iff, hfun]
    exact hmul

/-- Finite products of nonnegative countable sums: the sum over the finite
(dependent) product of the countable index sets is the product of the sums. -/
lemma hasSum_pi_prod {T : Type*} [Fintype T] {S : T → Type u} (f : ∀ t, S t → ℝ) (a : T → ℝ)
    (hf : ∀ t s, 0 ≤ f t s) (ha : ∀ t, HasSum (f t) (a t)) :
    HasSum (fun ω : ∀ t, S t => ∏ t, f t (ω t)) (∏ t, a t) := by
  let e := Fintype.equivFin T
  have h := hasSum_pi_prod_fin (Fintype.card T) (S := fun i => S (e.symm i))
    (fun i => f (e.symm i)) (fun i => a (e.symm i)) (fun i => hf _) (fun i => ha _)
  have ha' : (∏ i, a (e.symm i)) = ∏ t, a t := Equiv.prod_comp e.symm a
  rw [ha'] at h
  rw [← (Equiv.piCongrLeft' S e).symm.hasSum_iff]
  convert h using 1
  funext ω
  simp only [Function.comp_apply]
  rw [← Equiv.prod_comp e.symm]
  apply Finset.prod_congr rfl
  intro i _
  rw [Equiv.piCongrLeft'_symm_apply_apply]

/-! ## Lemma 8.3: finite approximants with geometric separation -/

/-- The finite real-rooted slot approximants of the library, keeping the
strict root separation `κ j < x κ i` for `i < j`. -/
lemma separated_normalized_factorization {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    {n : ℕ} (hn : n ≠ 0) :
    ∃ κ : Fin n → ℝ, (∀ r, 0 < κ r) ∧ (∑ r, κ r) = 1 ∧
      (∀ i j : Fin n, i < j → κ j < x * κ i) ∧
      slotGeneratingPolynomial κ = normalizedSlotApproxPolynomial x n := by
  obtain ⟨r, hr, hsep, hfactor⟩ := slotApproxPolynomial_separated_factorization hx hx1 n
  let κ : Fin n → ℝ := fun i => ((n : ℝ) * r i)⁻¹
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hκ (i : Fin n) : 0 < κ i := inv_pos.mpr (mul_pos hnpos (hr i))
  have hpoly : slotGeneratingPolynomial κ = normalizedSlotApproxPolynomial x n := by
    apply Polynomial.funext
    intro t
    have hreflect := congrArg (fun p : Polynomial ℝ => p.eval (-((n : ℝ)⁻¹ * t))) hfactor
    simp only [reflectedSlotApproxPolynomial_eval, neg_neg,
      normalizedFactorPolynomial_eval] at hreflect
    simp only [normalizedSlotApproxPolynomial, eval_comp, eval_mul, eval_C, eval_X]
    rw [hreflect]
    simp only [slotGeneratingPolynomial, eval_prod, eval_add, eval_one, eval_mul, eval_C,
      eval_X, normalizedRootProduct]
    apply Finset.prod_congr rfl
    intro i _
    dsimp [κ]
    field_simp
    ring
  refine ⟨κ, hκ, ?_, ?_, hpoly⟩
  · have h := congrArg (fun p : Polynomial ℝ => p.coeff 1) hpoly
    simpa only [slotGeneratingPolynomial_linear, normalizedSlotApproxPolynomial_linear x hn]
      using h
  · intro i j hij
    have h := hsep i j hij
    have hri := hr i
    have hrj := hr j
    show ((n : ℝ) * r j)⁻¹ < x * ((n : ℝ) * r i)⁻¹
    rw [inv_eq_one_div, inv_eq_one_div, mul_one_div,
      div_lt_div_iff₀ (mul_pos hnpos hrj) (mul_pos hnpos hri)]
    nlinarith [mul_lt_mul_of_pos_left h hnpos]

/-- The `n+1`-slot approximant. -/
def approxKappa {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (n : ℕ) : Fin (n + 1) → ℝ :=
  Classical.choose (separated_normalized_factorization hx hx1 n.succ_ne_zero)

lemma approxKappa_spec {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (n : ℕ) :
    (∀ r, 0 < approxKappa hx hx1 n r) ∧ (∑ r, approxKappa hx hx1 n r) = 1 ∧
      (∀ i j : Fin (n + 1), i < j → approxKappa hx hx1 n j < x * approxKappa hx hx1 n i) ∧
      slotGeneratingPolynomial (approxKappa hx hx1 n) =
        normalizedSlotApproxPolynomial x (n + 1) :=
  Classical.choose_spec (separated_normalized_factorization hx hx1 n.succ_ne_zero)

/-- The approximant extended by zero to all slot labels `ℕ`. -/
def padKappa {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (n : ℕ) (i : ℕ) : ℝ :=
  if h : i < n + 1 then approxKappa hx hx1 n ⟨i, h⟩ else 0

lemma padKappa_nonneg {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (n i : ℕ) :
    0 ≤ padKappa hx hx1 n i := by
  unfold padKappa
  split_ifs with h
  · exact ((approxKappa_spec hx hx1 n).1 _).le
  · exact le_rfl

lemma padKappa_succ_le {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (n i : ℕ) :
    padKappa hx hx1 n (i + 1) ≤ x * padKappa hx hx1 n i := by
  by_cases h : i + 1 < n + 1
  · have hi : i < n + 1 := by omega
    have hlt := (approxKappa_spec hx hx1 n).2.2.1 ⟨i, hi⟩ ⟨i + 1, h⟩
      (by change i < i + 1; omega)
    simp only [padKappa, dif_pos h, dif_pos hi]
    exact hlt.le
  · simp only [padKappa, dif_neg h]
    exact mul_nonneg hx.le (padKappa_nonneg hx hx1 n i)

lemma padKappa_zero_le_one {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (n : ℕ) :
    padKappa hx hx1 n 0 ≤ 1 := by
  have hs := (approxKappa_spec hx hx1 n).2.1
  simp only [padKappa, dif_pos (Nat.succ_pos n)]
  rw [← hs]
  exact Finset.single_le_sum (fun r _ => ((approxKappa_spec hx hx1 n).1 r).le)
    (Finset.mem_univ _)

lemma padKappa_le_pow {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (n i : ℕ) :
    padKappa hx hx1 n i ≤ x ^ i := by
  induction i with
  | zero => simpa using padKappa_zero_le_one hx hx1 n
  | succ i ih =>
    calc padKappa hx hx1 n (i + 1) ≤ x * padKappa hx hx1 n i := padKappa_succ_le hx hx1 n i
      _ ≤ x * x ^ i := mul_le_mul_of_nonneg_left ih hx.le
      _ = x ^ (i + 1) := by ring

lemma padKappa_hasSum {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (n : ℕ) :
    HasSum (padKappa hx hx1 n) 1 := by
  have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (f := padKappa hx hx1 n) (s := Finset.range (n + 1))
    (fun i hi => by
      simp only [Finset.mem_range] at hi
      simp only [padKappa, dif_neg hi])
  convert h using 1
  rw [← (approxKappa_spec hx hx1 n).2.1, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [padKappa, dif_pos i.isLt]

/-- The ordered distinct-slot sum for the padded approximant is its finite
distinct-slot mass. -/
lemma padKappa_distinct {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (n k : ℕ) :
    HasSum (fun f : {f : Fin k → ℕ // Function.Injective f} => ∏ j, padKappa hx hx1 n (f.1 j))
      (((n + 1).descFactorial k : ℝ) / ((n : ℝ) + 1) ^ k * x ^ k.choose 2) := by
  classical
  let κ := approxKappa hx hx1 n
  let ι : {g : Fin k → Fin (n + 1) // Function.Injective g} →
      {f : Fin k → ℕ // Function.Injective f} :=
    fun g => ⟨fun j => (g.1 j : ℕ), Fin.val_injective.comp g.2⟩
  have hι : Function.Injective ι := by
    intro g h hgh
    apply Subtype.ext
    funext j
    exact Fin.ext (congrFun (congrArg Subtype.val hgh) j)
  have hzero : ∀ f ∉ Set.range ι, (∏ j, padKappa hx hx1 n (f.1 j)) = 0 := by
    intro f hf
    have hj : ∃ j, ¬ f.1 j < n + 1 := by
      by_contra hn
      push Not at hn
      exact hf ⟨⟨fun j => ⟨f.1 j, hn j⟩, fun a b hab => f.2 (congrArg Fin.val hab)⟩, rfl⟩
    obtain ⟨j, hj⟩ := hj
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp only [padKappa, dif_neg hj])
  rw [← hι.hasSum_iff hzero]
  have hcomp : ((fun f : {f : Fin k → ℕ // Function.Injective f} =>
      ∏ j, padKappa hx hx1 n (f.1 j)) ∘ ι) = fun g => ∏ j, κ (g.1 j) := by
    funext g
    simp only [Function.comp_apply, ι, padKappa, dif_pos (g.1 _).isLt]
    rfl
  rw [hcomp]
  have hval : distinctSlotMass κ k =
      ∑ g : {g : Fin k → Fin (n + 1) // Function.Injective g}, ∏ j, κ (g.1 j) := by
    unfold distinctSlotMass
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun g => by simp) _
  have hm : distinctSlotMass κ k =
      ((n + 1).descFactorial k : ℝ) / ((n : ℝ) + 1) ^ k * x ^ k.choose 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      distinctSlotMass_of_approx_factorization κ x (approxKappa_spec hx hx1 n).2.2.2 k
  rw [← hm, hval]
  have hfin := hasSum_fintype (fun g : {g : Fin k → Fin (n + 1) // Function.Injective g} =>
    ∏ j, κ (g.1 j))
  exact hfin

/-- The geometric domination of the distinct-slot terms is summable. -/
lemma summable_geometric_tuple {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (k : ℕ) :
    Summable (fun f : {f : Fin k → ℕ // Function.Injective f} => ∏ j, x ^ (f.1 j)) := by
  have h := hasSum_pi_prod (T := Fin k) (S := fun _ => ℕ) (fun _ r => x ^ r)
    (fun _ => (1 - x)⁻¹) (fun _ r => pow_nonneg hx.le r)
    (fun _ => hasSum_geometric_of_lt_one hx.le hx1)
  exact h.summable.comp_injective Subtype.val_injective

/-- **Lemma 8.3 (slot representation)**, with slots indexed by `ℕ`.  For
`0 < x < 1` there is a probability distribution `κ` on the slot labels,
with every `κ r > 0`, such that for every `k ≥ 0` the sum of
`∏ j, κ (r j)` over ordered `k`-tuples of pairwise distinct slots equals
`x ^ (k choose 2)`. -/
theorem slot_representation {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    ∃ κ : ℕ → ℝ, (∀ r, 0 < κ r) ∧ HasSum κ 1 ∧
      ∀ k : ℕ, HasSum (fun f : {f : Fin k → ℕ // Function.Injective f} => ∏ j, κ (f.1 j))
        (x ^ k.choose 2) := by
  -- Compactness: a subsequence of the padded approximants converges pointwise.
  have hcpt : IsCompact (Set.univ.pi fun _ : ℕ => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ n, padKappa hx hx1 n ∈ Set.univ.pi fun _ : ℕ => Set.Icc (0 : ℝ) 1 := by
    intro n
    simp only [Set.mem_univ_pi, Set.mem_Icc]
    intro i
    exact ⟨padKappa_nonneg hx hx1 n i,
      (padKappa_le_pow hx hx1 n i).trans (pow_le_one₀ hx.le hx1.le)⟩
  obtain ⟨κ, _, φ, hφ, hlim⟩ := hcpt.tendsto_subseq hmem
  have hpt : ∀ i, Tendsto (fun m => padKappa hx hx1 (φ m) i) atTop (𝓝 (κ i)) :=
    fun i => (tendsto_pi_nhds.mp hlim) i
  have hnonneg : ∀ i, 0 ≤ κ i := fun i =>
    ge_of_tendsto (hpt i) (Eventually.of_forall fun m => padKappa_nonneg hx hx1 (φ m) i)
  have hstep : ∀ i, κ (i + 1) ≤ x * κ i := fun i =>
    le_of_tendsto_of_tendsto (hpt (i + 1)) ((hpt i).const_mul x)
      (Eventually.of_forall fun m => padKappa_succ_le hx hx1 (φ m) i)
  have hpow : ∀ i, κ i ≤ x ^ i := fun i =>
    le_of_tendsto (hpt i) (Eventually.of_forall fun m => padKappa_le_pow hx hx1 (φ m) i)
  -- Total mass.
  have hsumκ : Summable κ :=
    Summable.of_nonneg_of_le hnonneg hpow (summable_geometric_of_lt_one hx.le hx1)
  have htotal : Tendsto (fun m => ∑' i, padKappa hx hx1 (φ m) i) atTop (𝓝 (∑' i, κ i)) :=
    tendsto_tsum_dominated (summable_geometric_of_lt_one hx.le hx1) hpt
      (Eventually.of_forall fun m i => by
        rw [Real.norm_of_nonneg (padKappa_nonneg hx hx1 (φ m) i)]
        exact padKappa_le_pow hx hx1 (φ m) i)
  have hone : ∑' i, κ i = 1 := by
    have hc : (fun m => ∑' i, padKappa hx hx1 (φ m) i) = fun _ => (1 : ℝ) := by
      funext m
      exact (padKappa_hasSum hx hx1 (φ m)).tsum_eq
    rw [hc] at htotal
    exact tendsto_nhds_unique htotal tendsto_const_nhds
  -- Distinct-slot moments.
  have hmoment : ∀ k : ℕ, HasSum
      (fun f : {f : Fin k → ℕ // Function.Injective f} => ∏ j, κ (f.1 j)) (x ^ k.choose 2) := by
    intro k
    have hbound := summable_geometric_tuple hx hx1 k
    have hsum : Summable (fun f : {f : Fin k → ℕ // Function.Injective f} => ∏ j, κ (f.1 j)) :=
      Summable.of_nonneg_of_le (fun f => Finset.prod_nonneg fun j _ => hnonneg _)
        (fun f => Finset.prod_le_prod (fun j _ => hnonneg _) (fun j _ => hpow _)) hbound
    have hlimit := tendsto_tsum_dominated
      (f := fun m (f : {f : Fin k → ℕ // Function.Injective f}) =>
        ∏ j, padKappa hx hx1 (φ m) (f.1 j))
      (g := fun f => ∏ j, κ (f.1 j)) hbound
      (fun f => tendsto_finsetProd _ fun j _ => hpt (f.1 j))
      (Eventually.of_forall fun m f => by
        rw [Real.norm_of_nonneg (Finset.prod_nonneg fun j _ => padKappa_nonneg hx hx1 _ _)]
        exact Finset.prod_le_prod (fun j _ => padKappa_nonneg hx hx1 _ _)
          (fun j _ => padKappa_le_pow hx hx1 _ _))
    have hval : (fun m => ∑' f : {f : Fin k → ℕ // Function.Injective f},
        ∏ j, padKappa hx hx1 (φ m) (f.1 j)) = fun m =>
          ((φ m + 1).descFactorial k : ℝ) / ((φ m : ℝ) + 1) ^ k * x ^ k.choose 2 := by
      funext m
      exact (padKappa_distinct hx hx1 (φ m) k).tsum_eq
    have hratio : Tendsto (fun m =>
        ((φ m + 1).descFactorial k : ℝ) / ((φ m : ℝ) + 1) ^ k * x ^ k.choose 2)
        atTop (𝓝 (x ^ k.choose 2)) := by
      have h := ((tendsto_descFactorial_ratio k).comp hφ.tendsto_atTop).mul_const
        (x ^ k.choose 2)
      simpa only [Function.comp_def, one_mul] using h
    change Tendsto (fun m => ∑' f : {f : Fin k → ℕ // Function.Injective f},
        ∏ j, padKappa hx hx1 (φ m) (f.1 j)) atTop _ at hlimit
    rw [hval] at hlimit
    have heq := tendsto_nhds_unique hlimit hratio
    rw [← heq]
    exact hsum.hasSum
  -- Every slot weight is positive.
  have hpos : ∀ r, 0 < κ r := by
    intro N
    by_contra hN
    have hzero : κ N = 0 := le_antisymm (not_lt.mp hN) (hnonneg N)
    have htail : ∀ d, κ (N + d) = 0 := by
      intro d
      induction d with
      | zero => simpa using hzero
      | succ d ih =>
        apply le_antisymm _ (hnonneg _)
        have := hstep (N + d)
        rw [ih, mul_zero] at this
        simpa [Nat.add_assoc] using this
    have hterm : ∀ f : {f : Fin (N + 1) → ℕ // Function.Injective f},
        (∏ j, κ (f.1 j)) = 0 := by
      intro f
      have hj : ∃ j, N ≤ f.1 j := by
        by_contra hn
        push Not at hn
        have hinj : Function.Injective (fun j : Fin (N + 1) => (⟨f.1 j, hn j⟩ : Fin N)) :=
          fun a b hab => f.2 (congrArg Fin.val hab)
        have := Fintype.card_le_of_injective _ hinj
        simp at this
      obtain ⟨j, hj⟩ := hj
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
      rw [hd]
      exact htail d
    have h0 : HasSum (fun f : {f : Fin (N + 1) → ℕ // Function.Injective f} =>
        ∏ j, κ (f.1 j)) 0 := by
      have : (fun f : {f : Fin (N + 1) → ℕ // Function.Injective f} => ∏ j, κ (f.1 j)) =
          fun _ => 0 := funext hterm
      rw [this]
      exact hasSum_zero
    have := (hmoment (N + 1)).unique h0
    exact (pow_pos hx _).ne' this
  exact ⟨κ, hpos, hone ▸ hsumκ.hasSum, hmoment⟩

/-- **Lemma 8.3**, with the slot labels literally `r ≥ 1` (type `ℕ+`). -/
theorem slot_representation_pnat {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    ∃ κ : ℕ+ → ℝ, (∀ r, 0 < κ r) ∧ HasSum κ 1 ∧
      ∀ k : ℕ, HasSum (fun f : {f : Fin k → ℕ+ // Function.Injective f} => ∏ j, κ (f.1 j))
        (x ^ k.choose 2) := by
  obtain ⟨κ, hpos, hsum, hmom⟩ := slot_representation hx hx1
  let e : ℕ+ ≃ ℕ := Equiv.pnatEquivNat
  refine ⟨fun r => κ (e r), fun r => hpos _, ?_, ?_⟩
  · exact (e.hasSum_iff (f := κ)).mpr hsum
  · intro k
    have h := hmom k
    let E : {f : Fin k → ℕ+ // Function.Injective f} ≃
        {f : Fin k → ℕ // Function.Injective f} :=
      Equiv.subtypeEquiv (Equiv.arrowCongr (Equiv.refl _) e) (fun f =>
        (e.injective.of_comp_iff f).symm)
    rw [← E.hasSum_iff] at h
    convert h using 1
    funext f
    rfl


/-! ## Lemma 8.4: the countable exact slot lift -/

section Lift

open PottsCI
attribute [local instance low] Classical.propDecidable
set_option linter.unusedSectionVars false

/-- A slot law with the three properties of Lemma 8.3. -/
def IsSlotLaw (x : ℝ) (κ : ℕ → ℝ) : Prop :=
  (∀ r, 0 < κ r) ∧ HasSum κ 1 ∧
    ∀ k : ℕ, HasSum (fun f : {f : Fin k → ℕ // Function.Injective f} => ∏ j, κ (f.1 j))
      (x ^ k.choose 2)

lemma exists_isSlotLaw {x : ℝ} (hx : 0 < x) (hx1 : x < 1) : ∃ κ, IsSlotLaw x κ :=
  slot_representation hx hx1

/-- The library's bundled probability slot weights. -/
def IsSlotLaw.toSlotWeights {x : ℝ} {κ : ℕ → ℝ} (h : IsSlotLaw x κ) : SlotWeights :=
  ⟨κ, fun r => (h.1 r).le, h.2.1⟩

/-- A countable endpoint-slot model: an ordered endpoint geometry on the
free edges, slot weights `κ`, the parameter `x ∈ [0,1]`, and the fixed
colour exponents of the activities. -/
structure SlotModel (V E C : Type*) where
  geom : EndpointGeometry V E
  κ : SlotWeights
  x : ℝ
  x_nonneg : 0 ≤ x
  x_le_one : x ≤ 1
  exponent : E → C → ℕ

namespace SlotModel

variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
variable [DecidableEq V] [DecidableEq E] [DecidableEq C] (M : SlotModel V E C)

/-- Occupied-label families `B = (B_v)`. -/
abbrev Boundary (V C : Type*) := V → Finset (C × ℕ)

/-- The activity `w_e(c,r,s) = x ^ (exponent e c) * κ r * κ s`. -/
def act (e : E) (ξ : C × ℕ × ℕ) : ℝ := slotActivity M.κ M.x (M.exponent e) ξ

lemma act_apply (e : E) (c : C) (r s : ℕ) :
    M.act e (c, r, s) = M.x ^ M.exponent e c * M.κ.weight r * M.κ.weight s := rfl

lemma act_nonneg (e : E) (ξ : C × ℕ × ℕ) : 0 ≤ M.act e ξ :=
  slotActivity_nonneg M.κ M.x_nonneg _ _

lemma act_hasSum (e : E) : HasSum (M.act e) (∑ c, M.x ^ M.exponent e c) :=
  slotActivity_hasSum M.κ M.x_nonneg _

lemma act_summable (e : E) : Summable (M.act e) := (M.act_hasSum e).summable

/-- The endpoint label `ℓ_{e,y}`: `(c,r)` at `e⁻ = endpoint e 0` and `(c,s)`
at `e⁺ = endpoint e 1`. -/
def label (e : E) (y : V) (ξ : C × ℕ × ℕ) : C × ℕ :=
  if y = M.geom.endpoint e 0 then (ξ.1, ξ.2.1) else (ξ.1, ξ.2.2)

lemma label_zero (e : E) (ξ : C × ℕ × ℕ) :
    M.label e (M.geom.endpoint e 0) ξ = (ξ.1, ξ.2.1) := if_pos rfl

lemma label_one (e : E) (ξ : C × ℕ × ℕ) :
    M.label e (M.geom.endpoint e 1) ξ = (ξ.1, ξ.2.2) := by
  unfold label
  rw [if_neg]
  intro h
  exact absurd (M.geom.injective e h) Fin.zero_lt_one.ne'

/-- `ξ` is compatible with the occupied labels at both endpoints of `e`. -/
def Compat (B : Boundary V C) (e : E) (ξ : C × ℕ × ℕ) : Prop :=
  ∀ y ∈ M.geom.endpoints e, M.label e y ξ ∉ B y

/-- Admissibility of a lifted assignment on the current free-edge set `F`:
at every vertex the occupied labels and the labels exposed by the incident
free edges are pairwise distinct. -/
def Admissible (F : Finset E) (B : Boundary V C) (ω : F → C × ℕ × ℕ) : Prop :=
  (∀ e : F, M.Compat B e.1 (ω e)) ∧
    ∀ e f : F, e ≠ f → ∀ y, y ∈ M.geom.endpoints e.1 → y ∈ M.geom.endpoints f.1 →
      M.label e.1 y (ω e) ≠ M.label f.1 y (ω f)

/-- The weight `W_{F,B}`, supported on admissible assignments. -/
def weight (F : Finset E) (B : Boundary V C) (ω : F → C × ℕ × ℕ) : ℝ :=
  if M.Admissible F B ω then ∏ e : F, M.act e.1 (ω e) else 0

/-- The partition sum over the countable lifted state space. -/
def partition (F : Finset E) (B : Boundary V C) : ℝ := ∑' ω : F → C × ℕ × ℕ, M.weight F B ω

/-- The normalized lifted law `ν_{F,B}`. -/
def law (F : Finset E) (B : Boundary V C) (ω : F → C × ℕ × ℕ) : ℝ :=
  M.weight F B ω / M.partition F B

/-- `deg_F(v)`. -/
def freeDegree (F : Finset E) (v : V) : ℕ := (F.filter fun e => v ∈ M.geom.endpoints e).card

def Meets (e f : E) : Prop := ∃ y, y ∈ M.geom.endpoints e ∧ y ∈ M.geom.endpoints f

/-- `d_F(e)`. -/
def adjDegree (F : Finset E) (e : E) : ℕ := ((F.erase e).filter fun f => M.Meets e f).card

/-- The activity of the endpoint fibre `{ξ : ℓ_{e,y}(ξ) = ζ}`. -/
def fibreMass (e : E) (y : V) (ζ : C × ℕ) : ℝ :=
  compatibleMass (M.act e) (fun ξ => M.label e y ξ = ζ)

/-- `M_e(B)`. -/
def compatMass (B : Boundary V C) (e : E) : ℝ := compatibleMass (M.act e) (M.Compat B e)

/-- The three bounds (load), (fibre), (slack). -/
def Bounds (Δ : ℕ) (F : Finset E) (B : Boundary V C) : Prop :=
  (∀ v, M.freeDegree F v + (B v).card ≤ Δ) ∧
    (∀ e ∈ F, ∀ y ∈ M.geom.endpoints e, ∀ ζ, M.fibreMass e y ζ ≤ 1) ∧
    ∀ e ∈ F, (Δ : ℝ) + 2 ≤ M.compatMass B e - M.adjDegree F e

/-- Pinning the state `ξ` on `e` adds its two endpoint labels. -/
def pinBoundary (B : Boundary V C) (e : E) (ξ : C × ℕ × ℕ) : Boundary V C :=
  fun y => if y ∈ M.geom.endpoints e then insert (M.label e y ξ) (B y) else B y

/-- Data obtained from `(F₀, ∅)` by successively pinning admissible
positive-activity states. -/
inductive Reachable : Finset E → Boundary V C → Prop
  | init : Reachable Finset.univ (fun _ => ∅)
  | pin {F : Finset E} {B : Boundary V C} {e : E} {ξ : C × ℕ × ℕ} :
      Reachable F B → e ∈ F → M.Compat B e ξ → 0 < M.act e ξ →
      Reachable (F.erase e) (M.pinBoundary B e ξ)

/-! ### The fibre bound -/

lemma compatibleMass_congr {S : Type*} (w : S → ℝ) {P Q : S → Prop} (h : ∀ s, P s ↔ Q s) :
    compatibleMass w P = compatibleMass w Q := by
  have : P = Q := funext fun s => propext (h s)
  rw [this]

lemma compatibleWeight_nonneg' {S : Type*} (w : S → ℝ) (hw : ∀ s, 0 ≤ w s) (P : S → Prop)
    (s : S) : 0 ≤ compatibleWeight w P s := by
  unfold compatibleWeight
  split_ifs
  · exact hw s
  · exact le_rfl

/-- Every endpoint fibre has activity at most one (for all data). -/
lemma fibreMass_le_one (e : E) (y : V) (ζ : C × ℕ) : M.fibreMass e y ζ ≤ 1 := by
  unfold fibreMass compatibleMass
  by_cases hy : y = M.geom.endpoint e 0
  · have hinj : Function.Injective (fun s : ℕ => ((ζ.1, ζ.2, s) : C × ℕ × ℕ)) := by
      intro a b h
      simpa using h
    have hsupp : Function.support (compatibleWeight (M.act e) (fun ξ => M.label e y ξ = ζ)) ⊆
        Set.range (fun s : ℕ => ((ζ.1, ζ.2, s) : C × ℕ × ℕ)) := by
      intro ξ hξ
      have hl : M.label e y ξ = ζ := by
        by_contra hn
        exact hξ (by unfold compatibleWeight; exact if_neg hn)
      simp only [label, if_pos hy] at hl
      exact ⟨ξ.2.2, by rw [← hl]⟩
    rw [← hinj.tsum_eq hsupp]
    have hterm : ∀ s : ℕ, compatibleWeight (M.act e) (fun ξ => M.label e y ξ = ζ) (ζ.1, ζ.2, s) =
        slotActivity M.κ M.x (M.exponent e) (ζ.1, ζ.2, s) := by
      intro s
      unfold compatibleWeight
      rw [if_pos (by simp only [label, if_pos hy])]
      rfl
    simp only [hterm]
    exact slotActivity_left_fibre_le_one M.κ M.x_nonneg M.x_le_one _ ζ.1 ζ.2
  · have hinj : Function.Injective (fun r : ℕ => ((ζ.1, r, ζ.2) : C × ℕ × ℕ)) := by
      intro a b h
      simpa using h
    have hsupp : Function.support (compatibleWeight (M.act e) (fun ξ => M.label e y ξ = ζ)) ⊆
        Set.range (fun r : ℕ => ((ζ.1, r, ζ.2) : C × ℕ × ℕ)) := by
      intro ξ hξ
      have hl : M.label e y ξ = ζ := by
        by_contra hn
        exact hξ (by unfold compatibleWeight; exact if_neg hn)
      simp only [label, if_neg hy] at hl
      exact ⟨ξ.2.1, by rw [← hl]⟩
    rw [← hinj.tsum_eq hsupp]
    have hterm : ∀ r : ℕ, compatibleWeight (M.act e) (fun ξ => M.label e y ξ = ζ) (ζ.1, r, ζ.2) =
        slotActivity M.κ M.x (M.exponent e) (ζ.1, r, ζ.2) := by
      intro r
      unfold compatibleWeight
      rw [if_pos (by simp only [label, if_neg hy])]
      rfl
    simp only [hterm]
    exact slotActivity_right_fibre_le_one M.κ M.x_nonneg M.x_le_one _ ζ.1 ζ.2

/-! ### One pinning step preserves the bounds -/

lemma shared_unique {e f : E} (hef : e ≠ f) {y z : V} (hye : y ∈ M.geom.endpoints e)
    (hyf : y ∈ M.geom.endpoints f) (hze : z ∈ M.geom.endpoints e)
    (hzf : z ∈ M.geom.endpoints f) : y = z := by
  by_contra hne
  exact hef (M.geom.linear e f y z hye hyf hze hzf hne)

lemma freeDegree_erase {F : Finset E} {e : E} (he : e ∈ F) (v : V) :
    M.freeDegree (F.erase e) v + (if v ∈ M.geom.endpoints e then 1 else 0) =
      M.freeDegree F v := by
  unfold freeDegree
  rw [Finset.filter_erase]
  split_ifs with hv
  · have hm : e ∈ F.filter fun e => v ∈ M.geom.endpoints e := Finset.mem_filter.mpr ⟨he, hv⟩
    rw [Finset.card_erase_of_mem hm]
    have := Finset.card_pos.mpr ⟨e, hm⟩
    omega
  · rw [Finset.erase_eq_of_notMem (by simp [hv])]
    rfl

lemma adjDegree_erase {F : Finset E} {e f : E} (he : e ∈ F) (hfe : f ≠ e) :
    M.adjDegree (F.erase e) f + (if M.Meets f e then 1 else 0) = M.adjDegree F f := by
  unfold adjDegree
  rw [Finset.erase_right_comm, Finset.filter_erase]
  split_ifs with hm
  · have hmem : e ∈ (F.erase f).filter fun g => M.Meets f g :=
      Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨Ne.symm hfe, he⟩, hm⟩
    rw [Finset.card_erase_of_mem hmem]
    have := Finset.card_pos.mpr ⟨e, hmem⟩
    omega
  · rw [Finset.erase_eq_of_notMem (by simp [hm])]
    rfl

lemma compat_pin_of_not_meets (B : Boundary V C) {e f : E} (ξ : C × ℕ × ℕ)
    (hm : ¬ M.Meets f e) (η : C × ℕ × ℕ) :
    M.Compat (M.pinBoundary B e ξ) f η ↔ M.Compat B f η := by
  unfold Compat pinBoundary
  constructor
  · intro h y hy
    have hye : y ∉ M.geom.endpoints e := fun hye => hm ⟨y, hy, hye⟩
    simpa only [if_neg hye] using h y hy
  · intro h y hy
    have hye : y ∉ M.geom.endpoints e := fun hye => hm ⟨y, hy, hye⟩
    simpa only [if_neg hye] using h y hy

lemma compat_pin_of_shared (B : Boundary V C) {e f : E} (hfe : f ≠ e) (ξ : C × ℕ × ℕ)
    {y₀ : V} (hy₀f : y₀ ∈ M.geom.endpoints f) (hy₀e : y₀ ∈ M.geom.endpoints e)
    (η : C × ℕ × ℕ) :
    M.Compat (M.pinBoundary B e ξ) f η ↔
      M.Compat B f η ∧ M.label f y₀ η ≠ M.label e y₀ ξ := by
  unfold Compat pinBoundary
  constructor
  · intro h
    refine ⟨fun y hy => ?_, ?_⟩
    · have := h y hy
      split_ifs at this with hye
      · exact fun hb => this (Finset.mem_insert_of_mem hb)
      · exact this
    · have := h y₀ hy₀f
      rw [if_pos hy₀e] at this
      exact fun heq => this (heq ▸ Finset.mem_insert_self _ _)
  · rintro ⟨h, hne⟩ y hy
    split_ifs with hye
    · have hyy : y = y₀ := M.shared_unique hfe hy hye hy₀f hy₀e
      subst hyy
      rw [Finset.mem_insert, not_or]
      exact ⟨hne, h y hy⟩
    · exact h y hy

/-- One pinning step of a compatible state preserves (load), (fibre) and
(slack). -/
theorem Bounds.pin {Δ : ℕ} {F : Finset E} {B : Boundary V C} (hB : M.Bounds Δ F B)
    {e : E} {ξ : C × ℕ × ℕ} (he : e ∈ F) (hc : M.Compat B e ξ) :
    M.Bounds Δ (F.erase e) (M.pinBoundary B e ξ) := by
  obtain ⟨hload, hfib, hslack⟩ := hB
  refine ⟨?_, ?_, ?_⟩
  · intro v
    have hd := M.freeDegree_erase he v
    have hl := hload v
    unfold pinBoundary
    split_ifs at hd ⊢ with hv
    · rw [Finset.card_insert_of_notMem (hc v hv)]
      omega
    · omega
  · intro f hf y hy ζ
    exact hfib f (Finset.mem_of_mem_erase hf) y hy ζ
  · intro f hf
    have hfe : f ≠ e := Finset.ne_of_mem_erase hf
    have hfF : f ∈ F := Finset.mem_of_mem_erase hf
    have hd := M.adjDegree_erase he hfe
    have hold := hslack f hfF
    by_cases hm : M.Meets f e
    · obtain ⟨y₀, hy₀f, hy₀e⟩ := hm
      have hmass : M.compatMass (M.pinBoundary B e ξ) f =
          compatibleMass (M.act f) (fun η => M.Compat B f η ∧
            M.label f y₀ η ≠ M.label e y₀ ξ) :=
        compatibleMass_congr _ (M.compat_pin_of_shared B hfe ξ hy₀f hy₀e)
      rw [if_pos ⟨y₀, hy₀f, hy₀e⟩] at hd
      have hcast : (M.adjDegree (F.erase e) f : ℝ) = (M.adjDegree F f : ℝ) - 1 := by
        rw [← hd]
        push_cast
        ring
      rw [hmass, hcast]
      exact compatibleMass_slack_inherited (M.act f) (M.act_nonneg f) (M.act_summable f)
        (M.Compat B f) (M.label f y₀) (M.label e y₀ ξ)
        (hfib f hfF y₀ hy₀f _) hold
    · have hmass : M.compatMass (M.pinBoundary B e ξ) f = M.compatMass B f :=
        compatibleMass_congr _ (M.compat_pin_of_not_meets B ξ hm)
      rw [if_neg hm, Nat.add_zero] at hd
      rw [hmass, hd]
      exact hold

/-- Every reachable instance satisfies the bounds, once the initial one does. -/
theorem Reachable.bounds {Δ : ℕ} (hinit : M.Bounds Δ Finset.univ (fun _ => ∅))
    {F : Finset E} {B : Boundary V C} (h : M.Reachable F B) : M.Bounds Δ F B := by
  induction h with
  | init => exact hinit
  | pin _ he hc _ ih => exact ih.pin M he hc

/-! ### Finite, positive partition sums -/

lemma weight_nonneg (F : Finset E) (B : Boundary V C) (ω : F → C × ℕ × ℕ) :
    0 ≤ M.weight F B ω := by
  unfold weight
  split_ifs
  · exact Finset.prod_nonneg fun e _ => M.act_nonneg _ _
  · exact le_rfl

lemma weight_le_prod (F : Finset E) (B : Boundary V C) (ω : F → C × ℕ × ℕ) :
    M.weight F B ω ≤ ∏ e : F, M.act e.1 (ω e) := by
  unfold weight
  split_ifs
  · exact le_rfl
  · exact Finset.prod_nonneg fun e _ => M.act_nonneg _ _

lemma prod_hasSum (F : Finset E) :
    HasSum (fun ω : F → C × ℕ × ℕ => ∏ e : F, M.act e.1 (ω e))
      (∏ e : F, ∑ c, M.x ^ M.exponent e.1 c) :=
  hasSum_pi_prod (T := F) (S := fun _ => C × ℕ × ℕ) (fun e => M.act e.1) _
    (fun _ _ => M.act_nonneg _ _) (fun _ => M.act_hasSum _)

lemma weight_summable (F : Finset E) (B : Boundary V C) : Summable (M.weight F B) :=
  Summable.of_nonneg_of_le (M.weight_nonneg F B) (M.weight_le_prod F B) (M.prod_hasSum F).summable

lemma partition_le (F : Finset E) (B : Boundary V C) :
    M.partition F B ≤ (Fintype.card C : ℝ) ^ F.card := by
  calc M.partition F B ≤ ∏ e : F, ∑ c, M.x ^ M.exponent e.1 c :=
        Summable.tsum_le_tsum (M.weight_le_prod F B) (M.weight_summable F B)
          (M.prod_hasSum F).summable |>.trans_eq (M.prod_hasSum F).tsum_eq
    _ ≤ ∏ _e : F, (Fintype.card C : ℝ) := by
        apply Finset.prod_le_prod
        · intro e _
          exact Finset.sum_nonneg fun c _ => pow_nonneg M.x_nonneg _
        · intro e _
          calc (∑ c, M.x ^ M.exponent e.1 c) ≤ ∑ _c : C, (1 : ℝ) :=
                Finset.sum_le_sum fun c _ => pow_le_one₀ M.x_nonneg M.x_le_one
            _ = Fintype.card C := by simp
    _ = (Fintype.card C : ℝ) ^ F.card := by simp

/-- States compatible with `B` at `e` and avoiding the labels of the already
assigned neighbours in `s`. -/
def Good (B : Boundary V C) (e : E) (σ : E → C × ℕ × ℕ) (s : Finset E)
    (ξ : C × ℕ × ℕ) : Prop :=
  M.Compat B e ξ ∧ ∀ f ∈ s, f ≠ e → ∀ y, y ∈ M.geom.endpoints e →
    y ∈ M.geom.endpoints f → M.label e y ξ ≠ M.label f y (σ f)

def Bad (e : E) (σ : E → C × ℕ × ℕ) (f : E) (ξ : C × ℕ × ℕ) : Prop :=
  ∃ y, y ∈ M.geom.endpoints e ∧ y ∈ M.geom.endpoints f ∧ M.label e y ξ = M.label f y (σ f)

lemma bad_mass_le_one (e : E) (σ : E → C × ℕ × ℕ) {f : E} (hfe : f ≠ e)
    (hm : M.Meets e f) : compatibleMass (M.act e) (M.Bad e σ f) ≤ 1 := by
  obtain ⟨y₀, hy₀e, hy₀f⟩ := hm
  have heq : compatibleMass (M.act e) (M.Bad e σ f) = M.fibreMass e y₀ (M.label f y₀ (σ f)) := by
    unfold fibreMass
    apply compatibleMass_congr
    intro ξ
    constructor
    · rintro ⟨y, hye, hyf, hl⟩
      have := M.shared_unique (Ne.symm hfe) hye hyf hy₀e hy₀f
      subst this
      exact hl
    · intro hl
      exact ⟨y₀, hy₀e, hy₀f, hl⟩
  rw [heq]
  exact M.fibreMass_le_one _ _ _

/-- Greedy availability: each adjacent assigned edge removes at most one unit
of compatible activity. -/
lemma avail (B : Boundary V C) (e : E) (σ : E → C × ℕ × ℕ) (s : Finset E) :
    M.compatMass B e - ((s.erase e).filter fun f => M.Meets e f).card ≤
      compatibleMass (M.act e) (M.Good B e σ s) := by
  set N := (s.erase e).filter fun f => M.Meets e f
  have hw := M.act_nonneg e
  have hs := M.act_summable e
  have hpoint : ∀ ξ, compatibleWeight (M.act e) (M.Compat B e) ξ ≤
      compatibleWeight (M.act e) (M.Good B e σ s) ξ +
        ∑ f ∈ N, compatibleWeight (M.act e) (M.Bad e σ f) ξ := by
    intro ξ
    have hnn : 0 ≤ ∑ f ∈ N, compatibleWeight (M.act e) (M.Bad e σ f) ξ :=
      Finset.sum_nonneg fun f _ => compatibleWeight_nonneg' _ hw _ _
    by_cases hg : M.Good B e σ s ξ
    · have h1 : compatibleWeight (M.act e) (M.Compat B e) ξ = M.act e ξ := if_pos hg.1
      have h2 : compatibleWeight (M.act e) (M.Good B e σ s) ξ = M.act e ξ := if_pos hg
      rw [h1, h2]
      linarith
    · by_cases hc : M.Compat B e ξ
      · have hbad : ∃ f ∈ s, f ≠ e ∧ ∃ y, y ∈ M.geom.endpoints e ∧
            y ∈ M.geom.endpoints f ∧ M.label e y ξ = M.label f y (σ f) := by
          by_contra hn
          apply hg
          refine ⟨hc, fun f hf hfe y hye hyf hl => hn ⟨f, hf, hfe, y, hye, hyf, hl⟩⟩
        obtain ⟨f, hf, hfe, y, hye, hyf, hl⟩ := hbad
        have hfN : f ∈ N := Finset.mem_filter.mpr
          ⟨Finset.mem_erase.mpr ⟨hfe, hf⟩, ⟨y, hye, hyf⟩⟩
        have h1 : compatibleWeight (M.act e) (M.Compat B e) ξ = M.act e ξ := if_pos hc
        have h2 : compatibleWeight (M.act e) (M.Good B e σ s) ξ = 0 := if_neg hg
        have h3 : compatibleWeight (M.act e) (M.Bad e σ f) ξ = M.act e ξ :=
          if_pos ⟨y, hye, hyf, hl⟩
        have hsingle := Finset.single_le_sum (s := N)
          (f := fun f => compatibleWeight (M.act e) (M.Bad e σ f) ξ)
          (fun f _ => compatibleWeight_nonneg' _ hw _ _) hfN
        rw [h1, h2, zero_add]
        rw [h3] at hsingle
        exact hsingle
      · have h1 : compatibleWeight (M.act e) (M.Compat B e) ξ = 0 := if_neg hc
        rw [h1]
        exact add_nonneg (compatibleWeight_nonneg' _ hw _ _) hnn
  have hsumBad : ∀ f ∈ N, Summable (compatibleWeight (M.act e) (M.Bad e σ f)) :=
    fun f _ => compatible_summable _ hw hs _
  have hsum := Summable.tsum_le_tsum hpoint (compatible_summable _ hw hs _)
    ((compatible_summable _ hw hs _).add (summable_sum hsumBad))
  rw [(compatible_summable _ hw hs _).tsum_add (summable_sum hsumBad),
    Summable.tsum_finsetSum hsumBad] at hsum
  have hbadle : ∑ f ∈ N, ∑' ξ, compatibleWeight (M.act e) (M.Bad e σ f) ξ ≤ (N.card : ℝ) := by
    calc ∑ f ∈ N, ∑' ξ, compatibleWeight (M.act e) (M.Bad e σ f) ξ ≤ ∑ _f ∈ N, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro f hf
          have hf' := Finset.mem_filter.mp hf
          exact M.bad_mass_le_one e σ (Finset.ne_of_mem_erase hf'.1) hf'.2
      _ = N.card := by simp
  change M.compatMass B e ≤ compatibleMass (M.act e) (M.Good B e σ s) + _ at hsum
  linarith

lemma exists_partial [Nonempty (C × ℕ × ℕ)] {Δ : ℕ} {F : Finset E} {B : Boundary V C}
    (hB : M.Bounds Δ F B) :
    ∀ s : Finset E, s ⊆ F → ∃ σ : E → C × ℕ × ℕ,
      (∀ e ∈ s, M.Compat B e (σ e) ∧ 0 < M.act e (σ e)) ∧
      ∀ e ∈ s, ∀ f ∈ s, e ≠ f → ∀ y, y ∈ M.geom.endpoints e → y ∈ M.geom.endpoints f →
        M.label e y (σ e) ≠ M.label f y (σ f) := by
  intro s
  induction s using Finset.induction_on with
  | empty => exact fun _ => ⟨fun _ => Classical.choice inferInstance, by simp⟩
  | @insert e s hes ih =>
    intro hsub
    obtain ⟨σ, hσ, hp⟩ := ih ((Finset.subset_insert e s).trans hsub)
    have heF : e ∈ F := hsub (Finset.mem_insert_self e s)
    have hav := M.avail B e σ s
    have hcard : (((s.erase e).filter fun f => M.Meets e f).card : ℝ) ≤ M.adjDegree F e := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _
        (Finset.erase_subset_erase e ((Finset.subset_insert e s).trans hsub)))
    have hsl := hB.2.2 e heF
    have hpos : 0 < compatibleMass (M.act e) (M.Good B e σ s) := by
      have : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
      linarith
    obtain ⟨ξ, hg, hξ⟩ := exists_positive_compatible (M.act e) _ hpos
    refine ⟨Function.update σ e ξ, ?_, ?_⟩
    · intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hfs
      · simpa only [Function.update_self] using And.intro hg.1 hξ
      · have hfe : f ≠ e := fun h => hes (h ▸ hfs)
        simpa only [Function.update_of_ne hfe] using hσ f hfs
    · intro f hf g hg' hfg y hyf hyg
      by_cases hfe : f = e
      · subst hfe
        have hge : g ≠ f := Ne.symm hfg
        have hgs : g ∈ s := (Finset.mem_insert.mp hg').resolve_left hge
        simpa only [Function.update_self, Function.update_of_ne hge] using
          hg.2 g hgs hge y hyf hyg
      · by_cases hge : g = e
        · subst hge
          have hfs : f ∈ s := (Finset.mem_insert.mp hf).resolve_left hfe
          simpa only [Function.update_self, Function.update_of_ne hfe] using
            (hg.2 f hfs hfe y hyg hyf).symm
        · simpa only [Function.update_of_ne hfe, Function.update_of_ne hge] using
            hp f ((Finset.mem_insert.mp hf).resolve_left hfe) g
              ((Finset.mem_insert.mp hg').resolve_left hge) hfg y hyf hyg

/-- Under the three bounds the partition sum is finite (summable, at most
`q ^ |F|`) and positive. -/
theorem partition_pos {Δ : ℕ} {F : Finset E} {B : Boundary V C} (hB : M.Bounds Δ F B) :
    0 < M.partition F B := by
  by_cases hF : F.Nonempty
  · obtain ⟨e₀, he₀⟩ := hF
    have hp : 0 < M.compatMass B e₀ := by
      have := hB.2.2 e₀ he₀
      have h0 : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
      have h1 : (0 : ℝ) ≤ M.adjDegree F e₀ := Nat.cast_nonneg _
      linarith
    obtain ⟨ξ₀, _, _⟩ := exists_positive_compatible (M.act e₀) _ hp
    have : Nonempty (C × ℕ × ℕ) := ⟨ξ₀⟩
    obtain ⟨σ, hσ, hpair⟩ := M.exists_partial hB F subset_rfl
    let ω : F → C × ℕ × ℕ := fun e => σ e.1
    have hadm : M.Admissible F B ω :=
      ⟨fun e => (hσ e.1 e.2).1, fun e f hef y hye hyf =>
        hpair e.1 e.2 f.1 f.2 (fun h => hef (Subtype.ext h)) y hye hyf⟩
    have hwpos : 0 < M.weight F B ω := by
      unfold weight
      rw [if_pos hadm]
      exact Finset.prod_pos fun e _ => (hσ e.1 e.2).2
    exact Summable.tsum_pos (M.weight_summable F B) (M.weight_nonneg F B) ω hwpos
  · have hF0 : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    subst hF0
    let ω : (∅ : Finset E) → C × ℕ × ℕ := fun e => absurd e.2 (Finset.notMem_empty _)
    have hadm : M.Admissible ∅ B ω :=
      ⟨fun e => absurd e.2 (Finset.notMem_empty _), fun e => absurd e.2 (Finset.notMem_empty _)⟩
    have hwpos : 0 < M.weight ∅ B ω := by
      unfold weight
      rw [if_pos hadm]
      exact Finset.prod_pos fun e _ => absurd e.2 (Finset.notMem_empty _)
    exact Summable.tsum_pos (M.weight_summable ∅ B) (M.weight_nonneg ∅ B) ω hwpos

theorem Bounds.partition_finite_pos {Δ : ℕ} {F : Finset E} {B : Boundary V C}
    (hB : M.Bounds Δ F B) :
    HasSum (M.weight F B) (M.partition F B) ∧ 0 < M.partition F B ∧
      M.partition F B ≤ (Fintype.card C : ℝ) ^ F.card :=
  ⟨(M.weight_summable F B).hasSum, M.partition_pos hB, M.partition_le F B⟩

/-- The normalized lifted law is a probability distribution. -/
theorem Bounds.law_hasSum {Δ : ℕ} {F : Finset E} {B : Boundary V C}
    (hB : M.Bounds Δ F B) : HasSum (M.law F B) 1 := by
  have h := (M.weight_summable F B).hasSum.div_const (M.partition F B)
  change HasSum _ (M.partition F B / M.partition F B) at h
  rw [div_self (M.partition_pos hB).ne'] at h
  exact h

end SlotModel

end Lift

/-! ### Exact projection of the initial countable lift -/

section Projection

open PottsCI
attribute [local instance low] Classical.propDecidable
set_option linter.unusedSectionVars false

/-- Ordered distinct-slot sums over an arbitrary finite index type. -/
lemma injective_hasSum {κ : ℕ → ℝ} {m : ℕ → ℝ}
    (hm : ∀ k, HasSum (fun f : {f : Fin k → ℕ // Function.Injective f} => ∏ j, κ (f.1 j)) (m k))
    (T : Type*) [Fintype T] :
    HasSum (fun β : T → ℕ => if Function.Injective β then ∏ t, κ (β t) else 0)
      (m (Fintype.card T)) := by
  set k := Fintype.card T
  have h1 : HasSum (fun f : Fin k → ℕ => if Function.Injective f then ∏ j, κ (f j) else 0)
      (m k) := by
    have hzero : ∀ f ∉ Set.range (Subtype.val : {f : Fin k → ℕ // Function.Injective f} →
        (Fin k → ℕ)), (if Function.Injective f then ∏ j, κ (f j) else 0) = 0 := by
      intro f hf
      rw [if_neg]
      intro hinj
      exact hf ⟨⟨f, hinj⟩, rfl⟩
    rw [← (Subtype.val_injective).hasSum_iff hzero]
    convert hm k using 1
    funext f
    simp only [Function.comp_apply, if_pos f.2]
  let e : T ≃ Fin k := Fintype.equivFin T
  let A : (T → ℕ) ≃ (Fin k → ℕ) := Equiv.arrowCongr e (Equiv.refl ℕ)
  rw [← A.symm.hasSum_iff]
  convert h1 using 1
  funext f
  have hA : ∀ t, (A.symm f) t = f (e t) := fun t => rfl
  have hinj : Function.Injective (A.symm f) ↔ Function.Injective f := by
    have : (A.symm f) = f ∘ e := funext hA
    rw [this]
    exact Function.Injective.of_comp_iff' f e.bijective
  simp only [Function.comp_apply]
  by_cases hf : Function.Injective f
  · rw [if_pos (hinj.mpr hf), if_pos hf]
    simp only [hA]
    exact Equiv.prod_comp e (fun j => κ (f j))
  · rw [if_neg (fun h => hf (hinj.mp h)), if_neg hf]

/-- Regroup incidence-indexed slots by their key. -/
def groupEquiv {I J : Type*} (key : I → J) :
    (I → ℕ) ≃ ((j : J) → {i : I // key i = j} → ℕ) where
  toFun α _ t := α t.1
  invFun β i := β (key i) ⟨i, rfl⟩
  left_inv _ := rfl
  right_inv β := by
    funext j t
    rcases t with ⟨i, hi⟩
    subst j
    rfl

/-- Slots at incidences with a common key are pairwise distinct. -/
def GroupedDistinct {I J : Type*} (key : I → J) (α : I → ℕ) : Prop :=
  ∀ p q, key p = key q → α p = α q → p = q

/-- The slot weight of a grouped-distinct assignment (zero otherwise). -/
def groupedTerm {I J : Type*} [Fintype I] (κ : ℕ → ℝ) (key : I → J) (α : I → ℕ) : ℝ :=
  if GroupedDistinct key α then ∏ i, κ (α i) else 0

/-- Countable grouped slot factorization: slots at incidences with a
common key are required to be distinct, and the groups factor. -/
lemma grouped_hasSum {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    {κ : ℕ → ℝ} (hκ : ∀ r, 0 ≤ κ r) {m : ℕ → ℝ}
    (hm : ∀ k, HasSum (fun f : {f : Fin k → ℕ // Function.Injective f} => ∏ j, κ (f.1 j)) (m k))
    (key : I → J) :
    HasSum (groupedTerm κ key) (∏ j, m (Fintype.card {i // key i = j})) := by
  let G : ((j : J) → {i : I // key i = j} → ℕ) → ℝ := fun β =>
    ∏ j, (if Function.Injective (β j) then ∏ t, κ (β j t) else 0)
  have hG : HasSum G (∏ j, m (Fintype.card {i // key i = j})) :=
    hasSum_pi_prod (S := fun j => {i : I // key i = j} → ℕ)
      (fun j β => if Function.Injective β then ∏ t, κ (β t) else 0)
      (fun j => m (Fintype.card {i // key i = j}))
      (fun j β => by
        split_ifs
        · exact Finset.prod_nonneg fun t _ => hκ _
        · exact le_rfl)
      (fun j => injective_hasSum hm _)
  have heq : groupedTerm κ key = G ∘ groupEquiv key := by
    funext α
    simp only [groupedTerm, Function.comp_apply, G, groupEquiv, Equiv.coe_fn_mk]
    rw [Fintype.prod_ite_zero]
    have hiff : GroupedDistinct key α ↔
        ∀ j, Function.Injective (fun t : {i // key i = j} => α t.1) := by
      unfold GroupedDistinct
      constructor
      · intro h j a b hab
        exact Subtype.ext (h a.1 b.1 (a.2.trans b.2.symm) hab)
      · intro h p q hk hα
        have := h (key p) (a₁ := ⟨p, rfl⟩) (a₂ := ⟨q, hk.symm⟩) hα
        exact congrArg Subtype.val this
    by_cases hc : GroupedDistinct key α
    · rw [if_pos hc, if_pos (hiff.mp hc)]
      exact (Fintype.prod_fiberwise key (fun i => κ (α i))).symm
    · rw [if_neg hc, if_neg (fun h => hc (hiff.mpr h))]
  rw [heq, (groupEquiv key).hasSum_iff]
  exact hG

end Projection

section ProjectionModel

open PottsCI
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) gapSlotDecEq (A : Type*) : DecidableEq A := Classical.decEq A
set_option linter.unusedSectionVars false

namespace SlotModel

variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C] (M : SlotModel V E C)

/-- A colour assignment together with the two endpoint slots of every edge. -/
def assemble (φ : E → C) (α : E × Fin 2 → ℕ) : ↥(Finset.univ : Finset E) → C × ℕ × ℕ :=
  fun e => (φ e.1, α (e.1, 0), α (e.1, 1))

def assembleEquiv : ((E → C) × (E × Fin 2 → ℕ)) ≃ (↥(Finset.univ : Finset E) → C × ℕ × ℕ) where
  toFun p := assemble p.1 p.2
  invFun ω := (fun e => (ω ⟨e, Finset.mem_univ e⟩).1,
    fun p => ![(ω ⟨p.1, Finset.mem_univ _⟩).2.1, (ω ⟨p.1, Finset.mem_univ _⟩).2.2] p.2)
  left_inv p := by
    rcases p with ⟨φ, α⟩
    refine Prod.ext rfl ?_
    funext q
    rcases q with ⟨e, h⟩
    fin_cases h <;> rfl
  right_inv ω := by
    funext e
    rcases e with ⟨e, he⟩
    simp only [assemble]
    rfl

lemma label_assemble (φ : E → C) (α : E × Fin 2 → ℕ) (e : E) (h : Fin 2) :
    M.label e (M.geom.endpoint e h) (assemble φ α ⟨e, Finset.mem_univ e⟩) = (φ e, α (e, h)) := by
  fin_cases h
  · exact M.label_zero e _
  · exact M.label_one e _

/-- Admissibility with empty occupied labels is grouped slot distinctness. -/
lemma admissible_assemble_iff (φ : E → C) (α : E × Fin 2 → ℕ) :
    M.Admissible Finset.univ (fun _ => ∅) (assemble φ α) ↔
      GroupedDistinct (M.geom.incidenceColourKey φ) α := by
  unfold GroupedDistinct
  constructor
  · intro h p q hkey hslot
    have hv : M.geom.endpoint p.1 p.2 = M.geom.endpoint q.1 q.2 := congrArg Prod.fst hkey
    have hc : φ p.1 = φ q.1 := congrArg Prod.snd hkey
    by_cases he : p.1 = q.1
    · apply Prod.ext he
      apply M.geom.injective p.1
      rw [hv, he]
    · exfalso
      have hpair := h.2 ⟨p.1, Finset.mem_univ _⟩ ⟨q.1, Finset.mem_univ _⟩
        (fun h' => he (congrArg Subtype.val h')) (M.geom.endpoint p.1 p.2)
        (M.geom.endpoint_mem p.1 p.2) (hv ▸ M.geom.endpoint_mem q.1 q.2)
      rw [M.label_assemble φ α p.1 p.2, hv, M.label_assemble φ α q.1 q.2] at hpair
      exact hpair (Prod.ext hc hslot)
  · intro h
    refine ⟨fun e y _ => Finset.notMem_empty _, ?_⟩
    intro e f hef y hye hyf hlabel
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hye
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hyf
    have he' : e = ⟨e.1, Finset.mem_univ _⟩ := rfl
    have hf' : f = ⟨f.1, Finset.mem_univ _⟩ := rfl
    have hl1 : M.label e.1 y (assemble φ α e) = (φ e.1, α (e.1, i)) := by
      rw [← hi, he']
      exact M.label_assemble φ α e.1 i
    have hl2 : M.label f.1 y (assemble φ α f) = (φ f.1, α (f.1, j)) := by
      rw [← hj, hf']
      exact M.label_assemble φ α f.1 j
    rw [hl1, hl2] at hlabel
    have hkey : M.geom.incidenceColourKey φ (e.1, i) = M.geom.incidenceColourKey φ (f.1, j) :=
      Prod.ext (hi.trans hj.symm) (congrArg Prod.fst hlabel)
    have := h (e.1, i) (f.1, j) hkey (congrArg Prod.snd hlabel)
    exact hef (Subtype.ext (congrArg Prod.fst this))

lemma weight_assemble (φ : E → C) (α : E × Fin 2 → ℕ) :
    M.weight Finset.univ (fun _ => ∅) (assemble φ α) =
      (∏ e, M.x ^ M.exponent e (φ e)) *
        groupedTerm M.κ.weight (M.geom.incidenceColourKey φ) α := by
  unfold weight groupedTerm
  rw [propext (M.admissible_assemble_iff φ α)]
  split_ifs
  · have h1 : (∏ e : (Finset.univ : Finset E), M.act e.1 (assemble φ α e)) =
        ∏ e : E, (M.x ^ M.exponent e (φ e) * (M.κ.weight (α (e, 0)) * M.κ.weight (α (e, 1)))) := by
      have h := Finset.prod_coe_sort (Finset.univ : Finset E)
        (fun e => M.x ^ M.exponent e (φ e) * (M.κ.weight (α (e, 0)) * M.κ.weight (α (e, 1))))
      rw [← h]
      apply Finset.prod_congr rfl
      intro e _
      simp only [assemble, act_apply, mul_assoc]
    rw [h1, Finset.prod_mul_distrib, Fintype.prod_prod_type]
    simp only [Fin.prod_univ_two]
  · rw [mul_zero]

/-- The slot fibre of a colour assignment has the Potts colour weight. -/
lemma fibre_hasSum
    (hmom : ∀ k, HasSum (fun f : {f : Fin k → ℕ // Function.Injective f} =>
      ∏ j, M.κ.weight (f.1 j)) (M.x ^ k.choose 2)) (φ : E → C) :
    HasSum (fun α : E × Fin 2 → ℕ => M.weight Finset.univ (fun _ => ∅) (assemble φ α))
      (M.geom.targetColourWeight M.x M.exponent φ) := by
  have hg := grouped_hasSum M.κ.nonneg hmom (M.geom.incidenceColourKey φ)
  have hmul := hg.mul_left (∏ e, M.x ^ M.exponent e (φ e))
  have hcard : ∀ vc, Fintype.card {i // M.geom.incidenceColourKey φ i = vc} =
      M.geom.colourIncidenceCount φ vc := fun vc => rfl
  have hfun : (fun α : E × Fin 2 → ℕ => M.weight Finset.univ (fun _ => ∅) (assemble φ α)) =
      fun α => (∏ e, M.x ^ M.exponent e (φ e)) *
        groupedTerm M.κ.weight (M.geom.incidenceColourKey φ) α :=
    funext fun α => M.weight_assemble φ α
  have htarget : M.geom.targetColourWeight M.x M.exponent φ =
      (∏ e, M.x ^ M.exponent e (φ e)) *
        ∏ vc, M.x ^ (Fintype.card {i // M.geom.incidenceColourKey φ i = vc}).choose 2 := by
    unfold EndpointGeometry.targetColourWeight
    simp only [hcard]
  rw [hfun, htarget]
  exact hmul

def colourPart (φ : E → C) (p : (E → C) × (E × Fin 2 → ℕ)) : ℝ :=
  if p.1 = φ then M.weight Finset.univ (fun _ => ∅) (assembleEquiv p) else 0

lemma colourPart_hasSum
    (hmom : ∀ k, HasSum (fun f : {f : Fin k → ℕ // Function.Injective f} =>
      ∏ j, M.κ.weight (f.1 j)) (M.x ^ k.choose 2)) (φ : E → C) :
    HasSum (M.colourPart φ) (M.geom.targetColourWeight M.x M.exponent φ) := by
  let ι : (E × Fin 2 → ℕ) → (E → C) × (E × Fin 2 → ℕ) := fun α => (φ, α)
  have hι : Function.Injective ι := fun a b h => congrArg Prod.snd h
  have hzero : ∀ p ∉ Set.range ι, M.colourPart φ p = 0 := by
    intro p hp
    unfold colourPart
    rw [if_neg]
    intro h
    exact hp ⟨p.2, Prod.ext h.symm rfl⟩
  rw [← hι.hasSum_iff hzero]
  have hfun : M.colourPart φ ∘ ι =
      fun α : E × Fin 2 → ℕ => M.weight Finset.univ (fun _ => ∅) (assemble φ α) := by
    funext α
    simp only [Function.comp_apply, colourPart, ι]
    rfl
  rw [hfun]
  exact M.fibre_hasSum hmom φ

/-- The initial partition sum is the Potts colour partition function. -/
lemma initial_partition_hasSum
    (hmom : ∀ k, HasSum (fun f : {f : Fin k → ℕ // Function.Injective f} =>
      ∏ j, M.κ.weight (f.1 j)) (M.x ^ k.choose 2)) :
    HasSum (M.weight Finset.univ (fun _ => ∅))
      (M.geom.targetColourPartition M.x M.exponent) := by
  rw [← assembleEquiv.hasSum_iff]
  have h := hasSum_sum (s := Finset.univ) (fun φ _ => M.colourPart_hasSum hmom φ)
  have hfun : (M.weight Finset.univ (fun _ => ∅)) ∘ assembleEquiv =
      fun p => ∑ φ ∈ Finset.univ, M.colourPart φ p := by
    funext p
    simp only [Function.comp_apply, colourPart]
    rw [Finset.sum_ite_eq Finset.univ p.1, if_pos (Finset.mem_univ _)]
  rw [hfun]
  exact h

/-- The colour projection `(c,r,s) ↦ c` of an initial lifted assignment. -/
def colourOf (ω : ↥(Finset.univ : Finset E) → C × ℕ × ℕ) : E → C :=
  fun e => (ω ⟨e, Finset.mem_univ e⟩).1

/-- The lifted law restricted to the colour fibre of `φ`; its total mass is the
pushforward of the initial lifted law under the colour projection. -/
def colourFibreLaw (φ : E → C) (ω : ↥(Finset.univ : Finset E) → C × ℕ × ℕ) : ℝ :=
  if colourOf ω = φ then M.law Finset.univ (fun _ => ∅) ω else 0

/-- **Exact projection** for the initial data `(F₀, ∅)`: the colour marginal
of the normalized lifted law is the normalized endpoint-collision law. -/
theorem initial_projection [Nonempty C] (hx : 0 < M.x)
    (hmom : ∀ k, HasSum (fun f : {f : Fin k → ℕ // Function.Injective f} =>
      ∏ j, M.κ.weight (f.1 j)) (M.x ^ k.choose 2)) (φ : E → C) :
    HasSum (M.colourFibreLaw φ) ((M.geom.targetColourLaw M.x hx M.exponent).w φ) := by
  have hZ : M.partition Finset.univ (fun _ => ∅) = M.geom.targetColourPartition M.x M.exponent :=
    (M.initial_partition_hasSum hmom).tsum_eq
  rw [← assembleEquiv.hasSum_iff]
  have h := (M.colourPart_hasSum hmom φ).div_const (M.geom.targetColourPartition M.x M.exponent)
  have hw : (M.geom.targetColourLaw M.x hx M.exponent).w φ =
      M.geom.targetColourWeight M.x M.exponent φ / M.geom.targetColourPartition M.x M.exponent :=
    rfl
  rw [hw]
  refine (congrArg (fun F => HasSum F _) ?_).mpr h
  funext p
  simp only [Function.comp_apply, colourPart, colourFibreLaw, law, hZ]
  have hiff : colourOf (assembleEquiv p) = φ ↔ p.1 = φ := Iff.rfl
  by_cases hp : p.1 = φ
  · rw [if_pos (hiff.mpr hp), if_pos hp]
  · rw [if_neg (fun h => hp (hiff.mp h)), if_neg hp, zero_div]

end SlotModel

end ProjectionModel

/-! ### The edge-Potts slot lift of a finite simple graph -/

section EdgePotts

open PottsCI EndpointGeometry
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) gapSlotDecEq' (A : Type*) : DecidableEq A := Classical.decEq A
set_option linter.unusedSectionVars false

namespace SlotModel

variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C] (M : SlotModel V E C)

lemma compatMass_empty (e : E) : M.compatMass (fun _ => ∅) e = ∑' ξ, M.act e ξ := by
  unfold compatMass compatibleMass compatibleWeight
  congr 1
  funext ξ
  rw [if_pos (show M.Compat (fun _ => ∅) e ξ from fun y _ => Finset.notMem_empty _)]

/-- The initial lifted law is a probability law. -/
theorem initial_law_hasSum [Nonempty C] (hx : 0 < M.x)
    (hmom : ∀ k, HasSum (fun f : {f : Fin k → ℕ // Function.Injective f} =>
      ∏ j, M.κ.weight (f.1 j)) (M.x ^ k.choose 2)) :
    HasSum (M.law Finset.univ (fun _ => ∅)) 1 := by
  have h := (M.initial_partition_hasSum hmom).div_const
    (M.geom.targetColourPartition M.x M.exponent)
  rw [div_self (M.geom.targetColourPartition_pos hx M.exponent).ne'] at h
  have hZ : M.partition Finset.univ (fun _ => ∅) = M.geom.targetColourPartition M.x M.exponent :=
    (M.initial_partition_hasSum hmom).tsum_eq
  have hfun : M.law Finset.univ (fun _ => ∅) = fun ω =>
      M.weight Finset.univ (fun _ => ∅) ω / M.geom.targetColourPartition M.x M.exponent := by
    funext ω
    simp only [law, hZ]
  rw [hfun]
  exact h

end SlotModel

variable {V C : Type*} [Fintype V] [Fintype C]

/-- `b_y^τ(c)`: the number of pinned edges at the vertex `y` with colour `c`. -/
def pinnedAt (G : SimpleGraph V) (τ : PartialColouring G.edgeSet C) (y : V) (c : C) : ℕ :=
  (Finset.univ.filter fun f : τ.domain => y ∈ (f.1 : Sym2 V) ∧ τ.colour f = c).card

/-- `g` orders the two endpoints `(e⁻, e⁺) = (g.endpoint e 0, g.endpoint e 1)`
of every free edge `e`. -/
def IsOrientation (G : SimpleGraph V) (τ : PartialColouring G.edgeSet C)
    (g : EndpointGeometry V τ.FreeVertex) : Prop :=
  ∀ e y, y ∈ g.endpoints e ↔ y ∈ (e.1 : Sym2 V)

/-- The library's canonical endpoint ordering is an orientation. -/
lemma isOrientation_freeEdgeGeometry (G : SimpleGraph V) (τ : PartialColouring G.edgeSet C) :
    IsOrientation G τ (freeEdgeGeometry G τ) :=
  fun e y => freeEdgeGeometry_endpoint_mem G τ e y

/-- The edge-Potts slot model: activities
`w_e(c,r,s) = x ^ (b_u(c) + b_v(c)) κ_r κ_s` with `(u,v) = (e⁻,e⁺)`. -/
def edgeSlotModel (G : SimpleGraph V) (τ : PartialColouring G.edgeSet C)
    (g : EndpointGeometry V τ.FreeVertex) (κ : SlotWeights) (x : ℝ) (hx : 0 ≤ x)
    (hx1 : x ≤ 1) : SlotModel V τ.FreeVertex C where
  geom := g
  κ := κ
  x := x
  x_nonneg := hx
  x_le_one := hx1
  exponent e c := pinnedAt G τ (g.endpoint e 0) c + pinnedAt G τ (g.endpoint e 1) c

section Statements

variable (G : SimpleGraph V) (τ : PartialColouring G.edgeSet C)
  (g : EndpointGeometry V τ.FreeVertex) (κ : SlotWeights) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1)

/-- The activity (eq. edge-slot-activity), literally. -/
lemma edgeSlotModel_act (e : τ.FreeVertex) (c : C) (r s : ℕ) :
    (edgeSlotModel G τ g κ x hx hx1).act e (c, r, s) =
      x ^ (pinnedAt G τ (g.endpoint e 0) c + pinnedAt G τ (g.endpoint e 1) c) *
        κ.weight r * κ.weight s := rfl

/-- The exposed labels: `(c,r)` at `e⁻` and `(c,s)` at `e⁺`. -/
lemma edgeSlotModel_label (e : τ.FreeVertex) (c : C) (r s : ℕ) :
    (edgeSlotModel G τ g κ x hx hx1).label e (g.endpoint e 0) (c, r, s) = (c, r) ∧
      (edgeSlotModel G τ g κ x hx hx1).label e (g.endpoint e 1) (c, r, s) = (c, s) :=
  ⟨SlotModel.label_zero _ e _, SlotModel.label_one _ e _⟩

end Statements

lemma endpoints_pair {E : Type*} (g : EndpointGeometry V E) (e : E) (y : V) :
    y ∈ g.endpoints e ↔ y = g.endpoint e 0 ∨ y = g.endpoint e 1 := by
  unfold EndpointGeometry.endpoints endpointSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨h, _, rfl⟩
    fin_cases h
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, Finset.mem_univ _, rfl⟩
    · exact ⟨1, Finset.mem_univ _, rfl⟩

lemma endpoint_ne {E : Type*} (g : EndpointGeometry V E) (e : E) :
    g.endpoint e 0 ≠ g.endpoint e 1 := fun h =>
  absurd (g.injective e h) Fin.zero_lt_one.ne

/-- By simplicity, the line-graph boundary count of a free edge is the sum of
the pinned counts at its two endpoints. -/
lemma boundaryCount_eq_pinnedAt (G : SimpleGraph V) (τ : PartialColouring G.edgeSet C)
    (g : EndpointGeometry V τ.FreeVertex) (hg : IsOrientation G τ g)
    (e : τ.FreeVertex) (c : C) :
    τ.boundaryCount G.lineGraph e c =
      pinnedAt G τ (g.endpoint e 0) c + pinnedAt G τ (g.endpoint e 1) c := by
  set u := g.endpoint e 0
  set v := g.endpoint e 1
  have huv : u ≠ v := endpoint_ne g e
  have hmemE : ∀ w, w ∈ (e.1 : Sym2 V) ↔ w = u ∨ w = v := fun w =>
    (hg e w).symm.trans (endpoints_pair g e w)
  have heq : (e.1 : Sym2 V) = s(u, v) :=
    (Sym2.mem_and_mem_iff huv).mp ⟨(hmemE u).mpr (Or.inl rfl), (hmemE v).mpr (Or.inr rfl)⟩
  have hfree : e.1 ∉ τ.domain := e.2
  let A : V → Finset τ.domain := fun y =>
    Finset.univ.filter fun f : τ.domain => y ∈ (f.1 : Sym2 V) ∧ τ.colour f = c
  have hunion : ((τ.pinnedNeighbours G.lineGraph e).filter fun f => τ.colour f = c) =
      A u ∪ A v := by
    ext f
    simp only [PartialColouring.pinnedNeighbours, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, A, SimpleGraph.lineGraph_adj_iff_exists]
    have hne : e.1 ≠ f.1 := fun h => hfree (h ▸ f.2)
    constructor
    · rintro ⟨⟨_, w, hwe, hwf⟩, hc⟩
      rcases (hmemE w).mp hwe with rfl | rfl
      · exact Or.inl ⟨hwf, hc⟩
      · exact Or.inr ⟨hwf, hc⟩
    · rintro (⟨hu, hc⟩ | ⟨hv, hc⟩)
      · exact ⟨⟨hne, u, (hmemE u).mpr (Or.inl rfl), hu⟩, hc⟩
      · exact ⟨⟨hne, v, (hmemE v).mpr (Or.inr rfl), hv⟩, hc⟩
  have hdisj : Disjoint (A u) (A v) := by
    rw [Finset.disjoint_left]
    intro f hfu hfv
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hfu hfv
    have hf : (f.1 : Sym2 V) = s(u, v) := (Sym2.mem_and_mem_iff huv).mp ⟨hfu.1, hfv.1⟩
    have : e.1 = f.1 := Subtype.ext (heq.trans hf.symm)
    exact hfree (this ▸ f.2)
  unfold PartialColouring.boundaryCount
  rw [hunion, Finset.card_union_of_disjoint hdisj]
  rfl

lemma edgeGraph_eq_freeGraph (G : SimpleGraph V) (τ : PartialColouring G.edgeSet C)
    (g : EndpointGeometry V τ.FreeVertex) (hg : IsOrientation G τ g) :
    g.edgeGraph = τ.freeGraph G.lineGraph := by
  ext e f
  change (e ≠ f ∧ ∃ v, v ∈ g.endpoints e ∧ v ∈ g.endpoints f) ↔ G.lineGraph.Adj e.val f.val
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  have hg' : ∀ (e : τ.FreeVertex) (y : V), y ∈ g.endpoints e ↔ y ∈ (e.1 : Sym2 V) := hg
  simp only [hg']
  exact and_congr_left fun _ => ⟨fun h h' => h (Subtype.ext h'),
    fun h h' => h (congrArg Subtype.val h')⟩

lemma edgeSlotModel_exponent (G : SimpleGraph V) (τ : PartialColouring G.edgeSet C)
    (g : EndpointGeometry V τ.FreeVertex) (hg : IsOrientation G τ g) (κ : SlotWeights) (x : ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (edgeSlotModel G τ g κ x hx hx1).exponent = τ.boundaryCount G.lineGraph := by
  funext e c
  exact (boundaryCount_eq_pinnedAt G τ g hg e c).symm

lemma edgeSlotModel_pinningData (G : SimpleGraph V) (τ : PartialColouring G.edgeSet C)
    (g : EndpointGeometry V τ.FreeVertex) (hg : IsOrientation G τ g) (κ : SlotWeights) (x : ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    g.pinningData (edgeSlotModel G τ g κ x hx hx1).exponent = τ.toPinningData G.lineGraph := by
  rw [edgeSlotModel_exponent G τ g hg]
  unfold EndpointGeometry.pinningData PartialColouring.toPinningData
  congr 1
  exact edgeGraph_eq_freeGraph G τ g hg

/-- The limiting colour law of the lift is the pinned edge-Potts law. -/
lemma edgeSlotModel_targetLaw [Nonempty C] (G : SimpleGraph V)
    (τ : PartialColouring G.edgeSet C) (g : EndpointGeometry V τ.FreeVertex)
    (hg : IsOrientation G τ g) (κ : SlotWeights) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    g.targetColourLaw x hx (edgeSlotModel G τ g κ x hx.le hx1).exponent =
      (τ.toPinningData G.lineGraph).gibbs x hx.le
        ((τ.toPinningData G.lineGraph).partition_pos_of_parameter_pos hx) := by
  have hw : ∀ φ, g.targetColourWeight x (edgeSlotModel G τ g κ x hx.le hx1).exponent φ =
      (τ.toPinningData G.lineGraph).weight x φ := by
    intro φ
    rw [targetColourWeight_eq_pinningWeight, edgeSlotModel_pinningData G τ g hg]
  have hZ : g.targetColourPartition x (edgeSlotModel G τ g κ x hx.le hx1).exponent =
      (τ.toPinningData G.lineGraph).partition x :=
    Finset.sum_congr rfl fun φ _ => hw φ
  apply FinDist.ext
  funext φ
  change g.targetColourWeight x (edgeSlotModel G τ g κ x hx.le hx1).exponent φ /
    g.targetColourPartition x (edgeSlotModel G τ g κ x hx.le hx1).exponent = _
  rw [hw, hZ]
  rfl

lemma freeDegree_univ_le (G : SimpleGraph V) (τ : PartialColouring G.edgeSet C)
    (g : EndpointGeometry V τ.FreeVertex) (hg : IsOrientation G τ g) (κ : SlotWeights) (x : ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (v : V) :
    (edgeSlotModel G τ g κ x hx hx1).freeDegree Finset.univ v ≤ G.degree v := by
  unfold SlotModel.freeDegree
  rw [← SimpleGraph.card_incidenceFinset_eq_degree]
  apply Finset.card_le_card_of_injOn (fun e : τ.FreeVertex => (e.1.1 : Sym2 V))
  · intro e he
    have he' : v ∈ g.endpoints e := (Finset.mem_filter.mp he).2
    change e.1.1 ∈ G.incidenceFinset v
    rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
    exact (hg e v).mp he'
  · intro e _ f _ hef
    exact Subtype.ext (Subtype.ext hef)

lemma adjDegree_univ (G : SimpleGraph V) (τ : PartialColouring G.edgeSet C)
    (g : EndpointGeometry V τ.FreeVertex) (hg : IsOrientation G τ g) (κ : SlotWeights) (x : ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (e : τ.FreeVertex) :
    (edgeSlotModel G τ g κ x hx hx1).adjDegree Finset.univ e =
      (τ.freeGraph G.lineGraph).degree e := by
  rw [← edgeGraph_eq_freeGraph G τ g hg, ← SimpleGraph.card_neighborFinset_eq_degree]
  unfold SlotModel.adjDegree
  congr 1
  ext f
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
    SimpleGraph.mem_neighborFinset]
  change (f ≠ e ∧ ∃ y, y ∈ g.endpoints e ∧ y ∈ g.endpoints f) ↔
    (e ≠ f ∧ ∃ v, v ∈ g.endpoints e ∧ v ∈ g.endpoints f)
  exact and_congr_left fun _ => ne_comm

/-- The initial slot instance `(F₀, ∅)` satisfies (load), (fibre), (slack). -/
theorem edgeSlotModel_initial_bounds (G : SimpleGraph V) (τ : PartialColouring G.edgeSet C)
    (g : EndpointGeometry V τ.FreeVertex) (hg : IsOrientation G τ g) (κ : SlotWeights) (x : ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) {Δ : ℕ} (hdeg : ∀ v, G.degree v ≤ Δ)
    (hq : 3 * Δ ≤ Fintype.card C) :
    (edgeSlotModel G τ g κ x hx hx1).Bounds Δ Finset.univ (fun _ => ∅) := by
  set M := edgeSlotModel G τ g κ x hx hx1
  refine ⟨?_, ?_, ?_⟩
  · intro v
    rw [Finset.card_empty, Nat.add_zero]
    exact (freeDegree_univ_le G τ g hg κ x hx hx1 v).trans (hdeg v)
  · intro e _ y _ ζ
    exact M.fibreMass_le_one e y ζ
  · intro e _
    have hinc : M.adjDegree Finset.univ e + (∑ c, M.exponent e c) + 2 ≤ 2 * Δ := by
      have h1 := τ.constraintDegree_eq_degree G.lineGraph e
      have h2 := lineGraph_degree_bound G hdeg e.1
      have hexp : (∑ c, M.exponent e c) = ∑ c, τ.boundaryCount G.lineGraph e c := by
        rw [edgeSlotModel_exponent G τ g hg]
      rw [adjDegree_univ G τ g hg κ x hx hx1 e, hexp]
      unfold PinningData.constraintDegree at h1
      simp only [PartialColouring.toPinningData_graph,
        PartialColouring.toPinningData_boundaryCount] at h1
      exact le_trans (le_of_eq (congrArg (· + 2) h1)) h2
    rw [M.compatMass_empty e]
    exact slotActivity_initial_slack κ hx (M.exponent e) hq hinc

/-! ### Lemma 8.4 -/

/-- **Lemma 8.4, exact lift.**  For the initial data `(F₀, ∅)`, the colour
projection `(c,r,s) ↦ c` sends the lifted law exactly to the normalized
pinned edge-Potts law `(μ^edge_{G,x})^τ = μ^τ_{L(G)}(x)`: the lifted mass of
the colour fibre of every `φ` is its pinned edge-Potts probability. -/
theorem edge_slot_lift_projection [Nonempty C] (G : SimpleGraph V)
    (τ : PartialColouring G.edgeSet C) (g : EndpointGeometry V τ.FreeVertex)
    (hg : IsOrientation G τ g) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) {κ : ℕ → ℝ}
    (hκ : IsSlotLaw x κ) (φ : τ.FreeVertex → C) :
    HasSum ((edgeSlotModel G τ g hκ.toSlotWeights x hx.le hx1.le).colourFibreLaw φ)
      (((τ.toPinningData G.lineGraph).gibbs x hx.le
        ((τ.toPinningData G.lineGraph).partition_pos_of_parameter_pos hx)).w φ) := by
  rw [← edgeSlotModel_targetLaw G τ g hg hκ.toSlotWeights hx hx1.le]
  exact (edgeSlotModel G τ g hκ.toSlotWeights x hx.le hx1.le).initial_projection hx hκ.2.2 φ

/-- The pushforward of the initial lifted law under the colour projection,
as a function of the colour assignment, is the pinned edge-Potts law. -/
theorem edge_slot_lift_pushforward [Nonempty C] (G : SimpleGraph V)
    (τ : PartialColouring G.edgeSet C) (g : EndpointGeometry V τ.FreeVertex)
    (hg : IsOrientation G τ g) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) {κ : ℕ → ℝ}
    (hκ : IsSlotLaw x κ) :
    (fun φ : τ.FreeVertex → C =>
      ∑' ω, (edgeSlotModel G τ g hκ.toSlotWeights x hx.le hx1.le).colourFibreLaw φ ω) =
      ((τ.toPinningData G.lineGraph).gibbs x hx.le
        ((τ.toPinningData G.lineGraph).partition_pos_of_parameter_pos hx)).w :=
  funext fun φ => (edge_slot_lift_projection G τ g hg hx hx1 hκ φ).tsum_eq

/-- **Lemma 8.4, inherited bounds.**  The initial slot instance and every
boundary obtained from it by successively pinning admissible
positive-activity states satisfy (load), (fibre) and (slack). -/
theorem edge_slot_lift_bounds (G : SimpleGraph V) (τ : PartialColouring G.edgeSet C)
    (g : EndpointGeometry V τ.FreeVertex) (hg : IsOrientation G τ g) {Δ : ℕ}
    (hdeg : ∀ v, G.degree v ≤ Δ) (hq : 3 * Δ ≤ Fintype.card C) {x : ℝ} (hx : 0 < x)
    (hx1 : x < 1) {κ : ℕ → ℝ} (hκ : IsSlotLaw x κ) {F : Finset τ.FreeVertex}
    {B : SlotModel.Boundary V C}
    (h : (edgeSlotModel G τ g hκ.toSlotWeights x hx.le hx1.le).Reachable F B) :
    (edgeSlotModel G τ g hκ.toSlotWeights x hx.le hx1.le).Bounds Δ F B :=
  SlotModel.Reachable.bounds _
    (edgeSlotModel_initial_bounds G τ g hg _ x hx.le hx1.le hdeg hq) h

/-- **Lemma 8.4** (`lem:edge-slot-lift`), all three assertions.  For every
slot law `κ` with the properties of Lemma 8.3 (one exists by
`slot_representation`), and every ordering `g` of the endpoints of the free
edges:
1. the colour projection of the initial lifted law is the pinned edge-Potts
   law, and the initial lifted law is a probability law;
2. every instance reachable from `(F₀, ∅)` by pinning admissible
   positive-activity states satisfies (load), (fibre), (slack);
3. every instance `(F, B)` (finite occupied-label sets, same labels and
   activities) satisfying the three bounds has a finite, positive partition
   sum (at most `q ^ |F|`), so its normalized law `ν_{F,B}` is a probability
   law. -/
theorem lem_edge_slot_lift [Nonempty C] (G : SimpleGraph V)
    (τ : PartialColouring G.edgeSet C) (g : EndpointGeometry V τ.FreeVertex)
    (hg : IsOrientation G τ g) {Δ : ℕ} (hdeg : ∀ v, G.degree v ≤ Δ)
    (hq : 3 * Δ ≤ Fintype.card C) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) {κ : ℕ → ℝ}
    (hκ : IsSlotLaw x κ) :
    ((∀ φ : τ.FreeVertex → C,
        HasSum ((edgeSlotModel G τ g hκ.toSlotWeights x hx.le hx1.le).colourFibreLaw φ)
          (((τ.toPinningData G.lineGraph).gibbs x hx.le
            ((τ.toPinningData G.lineGraph).partition_pos_of_parameter_pos hx)).w φ)) ∧
      HasSum ((edgeSlotModel G τ g hκ.toSlotWeights x hx.le hx1.le).law Finset.univ
        (fun _ => ∅)) 1) ∧
    (∀ (F : Finset τ.FreeVertex) (B : SlotModel.Boundary V C),
      (edgeSlotModel G τ g hκ.toSlotWeights x hx.le hx1.le).Reachable F B →
        (edgeSlotModel G τ g hκ.toSlotWeights x hx.le hx1.le).Bounds Δ F B) ∧
    (∀ (F : Finset τ.FreeVertex) (B : SlotModel.Boundary V C),
      (edgeSlotModel G τ g hκ.toSlotWeights x hx.le hx1.le).Bounds Δ F B →
        HasSum ((edgeSlotModel G τ g hκ.toSlotWeights x hx.le hx1.le).weight F B)
            ((edgeSlotModel G τ g hκ.toSlotWeights x hx.le hx1.le).partition F B) ∧
          0 < (edgeSlotModel G τ g hκ.toSlotWeights x hx.le hx1.le).partition F B ∧
          (edgeSlotModel G τ g hκ.toSlotWeights x hx.le hx1.le).partition F B ≤
            (Fintype.card C : ℝ) ^ F.card ∧
          HasSum ((edgeSlotModel G τ g hκ.toSlotWeights x hx.le hx1.le).law F B) 1) :=
  ⟨⟨fun φ => edge_slot_lift_projection G τ g hg hx hx1 hκ φ,
      (edgeSlotModel G τ g hκ.toSlotWeights x hx.le hx1.le).initial_law_hasSum hx hκ.2.2⟩,
    fun _ _ h => edge_slot_lift_bounds G τ g hg hdeg hq hx hx1 hκ h,
    fun _ _ hB => ⟨(hB.partition_finite_pos _).1, (hB.partition_finite_pos _).2.1,
      (hB.partition_finite_pos _).2.2, hB.law_hasSum _⟩⟩

/-- Lemmas 8.3 and 8.4 together, for the library's canonical ordering of the
endpoints: there is a slot law `κ` (Lemma 8.3) for which all assertions of
Lemma 8.4 hold. -/
theorem lem_edge_slot_lift_exists [Nonempty C] (G : SimpleGraph V)
    (τ : PartialColouring G.edgeSet C) {Δ : ℕ} (hdeg : ∀ v, G.degree v ≤ Δ)
    (hq : 3 * Δ ≤ Fintype.card C) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    ∃ κ : ℕ → ℝ, ∃ hκ : IsSlotLaw x κ,
      (∀ φ : τ.FreeVertex → C,
        HasSum ((edgeSlotModel G τ (freeEdgeGeometry G τ) hκ.toSlotWeights x hx.le
            hx1.le).colourFibreLaw φ)
          (((τ.toPinningData G.lineGraph).gibbs x hx.le
            ((τ.toPinningData G.lineGraph).partition_pos_of_parameter_pos hx)).w φ)) ∧
      (∀ (F : Finset τ.FreeVertex) (B : SlotModel.Boundary V C),
        (edgeSlotModel G τ (freeEdgeGeometry G τ) hκ.toSlotWeights x hx.le hx1.le).Reachable
          F B →
        (edgeSlotModel G τ (freeEdgeGeometry G τ) hκ.toSlotWeights x hx.le hx1.le).Bounds
          Δ F B) := by
  obtain ⟨κ, hκ⟩ := exists_isSlotLaw hx hx1
  exact ⟨κ, hκ, fun φ => edge_slot_lift_projection G τ _ (isOrientation_freeEdgeGeometry G τ)
      hx hx1 hκ φ,
    fun _ _ h => edge_slot_lift_bounds G τ _ (isOrientation_freeEdgeGeometry G τ) hdeg hq hx
      hx1 hκ h⟩

end EdgePotts



end
end ZeroFreeness.Appendix.Edge
