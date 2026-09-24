import CI2ZF.Coupling.CLMM.Ambient
import CI2ZF.Coupling.CLMM.AmbientDegree
import CI2ZF.Coupling.Girth.Covariance.Doob.PinningVertex
import CI2ZF.Potts.Model.PinningRestrictionInstances
import CI2ZF.Potts.Model.PinningRestrictionComposition
import CI2ZF.Coupling.Edge.Finite.Conditioning

/-! CLMM2023 Lemma 5.13: fixed-ambient sphere influence decay implies the
Hamming coupling bound `2 Δ^R` for the two root-child Potts laws.

The base `J := I` is fixed; an instance is a further pinning
`(W, f : Option W ↪ A, p)` with root `f none`, and breadth `ℓ` counts free
vertices at `J.graph`-distance exactly `R` from the root.  By strong
induction on `card W` (`main_bound`) the transport cost is at most
`Fb ℓ = Δ^R (1 + 2ε L ℓ)`, `L 0 = 0`, `L ℓ = 1 + log ℓ`:
* `separated_case` (ℓ = 0): the laws share their marginal outside the ball
  (`potts_marginal_eq`), so `W ≤ #ball ≤ Δ^R` (`W_ham_le_of_common_marginal`);
* `recursion_case` (ℓ ≥ 1): condition on the sphere vertex of least TV
  (`W_le_split`, maximal coupling); conditioned laws are sub-instances
  (`Q1` same root, `Q2` rerooted at `w₀`), and `Fb_step`/`Fb_top` close it. -/

namespace CI2ZF.Appendix.CLMM.Lemma513
open scoped BigOperators
open PottsCI PottsCI.FinDist CI2ZF CI2ZF.Potts CI2ZF.Appendix.Edge.FiniteLaw
open CI2ZF.Appendix.Girth
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

universe u v

section Couplings

theorem W_add_const_le {S T : Type*} [Fintype S] [Fintype T] (d : S → T → ℝ)
    (hd : ∀ x y, 0 ≤ d x y) (t : ℝ) (ht : 0 ≤ t) (μ : FinDist S) (ν : FinDist T) :
    W (fun x y => d x y + t) μ ν ≤ W d μ ν + t := by
  have h : W (fun x y => d x y + t) μ ν - t ≤ W d μ ν := by
    apply le_W
    intro γ
    have h1 := W_le_cost (fun x y => add_nonneg (hd x y) ht) γ
    have h2 : γ.cost (fun x y => d x y + t) = γ.cost d + t := by
      unfold Coupling.cost
      have h3 : ∑ x, ∑ y, γ.w x y * t = t := by
        simp_rw [← Finset.sum_mul]
        rw [γ.total_mass, one_mul]
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [h3]
    linarith
  linarith

theorem W_le_of_support {S T : Type*} [Fintype S] [Fintype T] (d : S → T → ℝ)
    (hd : ∀ x y, 0 ≤ d x y) (μ : FinDist S) (ν : FinDist T) (B : ℝ)
    (h : ∀ x y, 0 < μ.w x → 0 < ν.w y → d x y ≤ B) : W d μ ν ≤ B := by
  refine (W_le_cost hd (Coupling.prod μ ν)).trans ?_
  unfold Coupling.cost Coupling.prod
  dsimp only
  calc ∑ x, ∑ y, μ.w x * ν.w y * d x y ≤ ∑ x, ∑ y, μ.w x * ν.w y * B := by
        apply Finset.sum_le_sum; intro x _; apply Finset.sum_le_sum; intro y _
        rcases eq_or_lt_of_le (μ.nonneg x) with hx | hx
        · rw [← hx]; simp
        rcases eq_or_lt_of_le (ν.nonneg y) with hy | hy
        · rw [← hy]; simp
        exact mul_le_mul_of_nonneg_left (h x y hx hy) (mul_nonneg hx.le hy.le)
    _ = B := by
        simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, ν.sum_one, one_mul, μ.sum_one,
          one_mul]

/-- Disintegration along an observation `k`, coupling the observed values with an
optimal (maximal) coupling. -/
theorem W_le_split {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X]
    (d : Ω → Ω → ℝ) (hd : ∀ x y, 0 ≤ d x y) (μ ν : FinDist Ω) (k : Ω → X) (A B : ℝ)
    (hB : 0 < B)
    (hsame : ∀ a, W d (conditional μ (fun ω => k ω = a)) (conditional ν (fun ω => k ω = a)) ≤ A)
    (hdiff : ∀ a a', a ≠ a' →
      W d (conditional μ (fun ω => k ω = a)) (conditional ν (fun ω => k ω = a')) ≤ A + B) :
    W d μ ν ≤ A + B * ((∑ a, |(marginal μ k).w a - (marginal ν k).w a|) / 2) := by
  set α := marginal μ k
  set β := marginal ν k
  let M := fun t => conditional μ (fun x => k x = t)
  let N := fun t => conditional ν (fun x => k x = t)
  let disc : X → X → ℝ := fun a a' => if a = a' then 0 else 1
  have hdisc0 : ∀ a a', 0 ≤ disc a a' := by
    intro a a'; dsimp only [disc]; split_ifs <;> norm_num
  have hdisc1 : ∀ a a', disc a a' ≤ 1 := by
    intro a a'; dsimp only [disc]; split_ifs <;> norm_num
  have key : ∀ γ : Coupling α β, W d μ ν ≤ A + B * γ.cost disc := by
    intro γ
    have hμ : α.bind M = μ := marginal_bind_conditional μ k
    have hν : β.bind N = ν := marginal_bind_conditional ν k
    calc W d μ ν = W d (α.bind M) (β.bind N) := by rw [hμ, hν]
      _ ≤ ∑ a, ∑ b, γ.w a b * W d (M a) (N b) := W_bind_le hd γ M N
      _ ≤ ∑ a, ∑ b, γ.w a b * (A + B * disc a b) := by
          apply Finset.sum_le_sum; intro a _; apply Finset.sum_le_sum; intro b _
          apply mul_le_mul_of_nonneg_left _ (γ.nonneg a b)
          by_cases hab : a = b
          · subst hab
            simp only [disc, if_pos rfl, mul_zero, add_zero]
            exact hsame a
          · simp only [disc, if_neg hab, mul_one]
            exact hdiff a b hab
      _ = A + B * γ.cost disc := by
          unfold Coupling.cost
          simp_rw [mul_add, Finset.sum_add_distrib]
          have h3 : ∑ x, ∑ y, γ.w x y * A = A := by
            simp_rw [← Finset.sum_mul]
            rw [γ.total_mass, one_mul]
          rw [h3, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl; intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b _
          ring
  have hW : (W d μ ν - A) / B ≤ W disc α β := by
    apply le_W
    intro γ
    rw [div_le_iff₀ hB]
    linarith [key γ]
  have hTV := W_le_half_l1 (d := disc) (B := 1) hdisc0 (fun a => by simp [disc]) hdisc1 α β
  rw [div_le_iff₀ hB] at hW
  nlinarith

end Couplings


section Separated
variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq C]

def outer (P : V → Prop) (σ : V → C) : {w // ¬ P w} → C := fun w => σ w.val

theorem W_ham_le_of_common_marginal (P : V → Prop) (μ ν : FinDist (V → C))
    (hm : marginal μ (outer P) = marginal ν (outer P)) :
    W ham μ ν ≤ Fintype.card {w // P w} := by
  set α := marginal μ (outer P) with hα
  let M := fun t => conditional μ (fun x => outer P x = t)
  let N := fun t => conditional ν (fun x => outer P x = t)
  have hμ : α.bind M = μ := marginal_bind_conditional μ _
  have hν : α.bind N = ν := by rw [hm]; exact marginal_bind_conditional ν _
  calc W ham μ ν = W ham (α.bind M) (α.bind N) := by rw [hμ, hν]
    _ ≤ ∑ ξ, α.w ξ * W ham (M ξ) (N ξ) := by
        have h := W_bind_diag (d' := (ham : (V → C) → (V → C) → ℝ)) ham_nonneg α M N
        exact h
    _ ≤ ∑ ξ, α.w ξ * (Fintype.card {w // P w} : ℝ) := by
        apply Finset.sum_le_sum; intro ξ _
        rcases eq_or_lt_of_le (α.nonneg ξ) with h0 | hpos
        · rw [← h0]; simp
        refine mul_le_mul_of_nonneg_left ?_ hpos.le
        refine W_le_of_support _ ham_nonneg _ _ _ ?_
        intro σ τ hσ hτ
        have hσ' := (conditional_pos_support μ (fun x => outer P x = ξ) hpos hσ).1
        have hτpos : 0 < eventMass ν (fun x => outer P x = ξ) := by
          have : (marginal ν (outer P)).w ξ = α.w ξ := by rw [hm]
          change 0 < (marginal ν (outer P)).w ξ
          rw [this]; exact hpos
        have hτ' := (conditional_pos_support ν _ hτpos hτ).1
        have hagree : ∀ w, ¬ P w → σ w = τ w := by
          intro w hw
          have h1 := congrFun hσ' ⟨w, hw⟩
          have h2 := congrFun hτ' ⟨w, hw⟩
          simp only [outer] at h1 h2
          rw [h1, h2]
        unfold ham hamCard
        rw [Fintype.card_subtype]
        exact_mod_cast Finset.card_le_card (by
          intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
          by_contra hP
          exact hw (hagree w hP))
    _ = Fintype.card {w // P w} := by rw [← Finset.sum_mul, α.sum_one, one_mul]

end Separated

section PottsSplit
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] [Nonempty C]

def inP (P : V → Prop) (e : Sym2 V) : Prop := ∃ w ∈ e, P w

def hPart (P : V → Prop) (G' : SimpleGraph V) (b : V → C → ℕ) (x : ℝ) (σ : V → C) : ℝ :=
  (∏ u : {u // P u}, x ^ b u.val (σ u.val)) *
    ∏ e ∈ G'.edgeFinset.filter (inP P), PinningData.edgeFactor x σ e

def gPart (P : V → Prop) (G' : SimpleGraph V) (b : V → C → ℕ) (x : ℝ) (σ : V → C) : ℝ :=
  (∏ u : {u // ¬ P u}, x ^ b u.val (σ u.val)) *
    ∏ e ∈ G'.edgeFinset.filter (fun e => ¬ inP P e), PinningData.edgeFactor x σ e

theorem weight_split (P : V → Prop) (G' : SimpleGraph V) (b : V → C → ℕ) (x : ℝ)
    (σ : V → C) :
    (⟨G', b⟩ : PinningData V C).weight x σ = hPart P G' b x σ * gPart P G' b x σ := by
  unfold PinningData.weight hPart gPart
  dsimp only
  rw [← Fintype.prod_subtype_mul_prod_subtype P (fun u => x ^ b u (σ u)),
    ← Finset.prod_filter_mul_prod_filter_not G'.edgeFinset (inP P)]
  ring

theorem hPart_congr (P : V → Prop) (G' : SimpleGraph V) (b : V → C → ℕ) (x : ℝ)
    (hsep : ∀ u w, G'.Adj u w → (P u ↔ P w)) (σ σ' : V → C)
    (h : ∀ w, P w → σ w = σ' w) : hPart P G' b x σ = hPart P G' b x σ' := by
  unfold hPart
  congr 1
  · apply Finset.prod_congr rfl
    intro u _
    rw [h u.val u.prop]
  · apply Finset.prod_congr rfl
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨he1, he2⟩ := he
    induction e using Sym2.ind with
    | _ u w =>
      have hadj : G'.Adj u w := by simpa using he1
      obtain ⟨z, hz, hPz⟩ := he2
      have hPu : P u ∧ P w := by
        rcases Sym2.mem_iff.mp hz with rfl | rfl
        · exact ⟨hPz, (hsep _ _ hadj).mp hPz⟩
        · exact ⟨(hsep _ _ hadj).mpr hPz, hPz⟩
      rw [PinningData.edgeFactor_mk, PinningData.edgeFactor_mk, h u hPu.1, h w hPu.2]

theorem gPart_congr (P : V → Prop) (G' : SimpleGraph V) (b : V → C → ℕ) (x : ℝ)
    (σ σ' : V → C) (h : ∀ w, ¬ P w → σ w = σ' w) :
    gPart P G' b x σ = gPart P G' b x σ' := by
  unfold gPart
  congr 1
  · apply Finset.prod_congr rfl
    intro u _
    rw [h u.val u.prop]
  · apply Finset.prod_congr rfl
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨_, he2⟩ := he
    induction e using Sym2.ind with
    | _ u w =>
      have hu : ¬ P u := fun hu => he2 ⟨u, Sym2.mem_mk_left u w, hu⟩
      have hw : ¬ P w := fun hw => he2 ⟨w, Sym2.mem_mk_right u w, hw⟩
      rw [PinningData.edgeFactor_mk, PinningData.edgeFactor_mk, h u hu, h w hw]

theorem gPart_eq (P : V → Prop) (G' : SimpleGraph V) (b₁ b₂ : V → C → ℕ) (x : ℝ)
    (hbc : ∀ w, ¬ P w → b₁ w = b₂ w) (σ : V → C) :
    gPart P G' b₁ x σ = gPart P G' b₂ x σ := by
  unfold gPart
  congr 1
  apply Finset.prod_congr rfl
  intro u _
  rw [hbc u.val u.prop]

theorem edgeFactor_pos {x : ℝ} (hx : 0 < x) (σ : V → C) (e : Sym2 V) :
    0 < PinningData.edgeFactor x σ e := by
  induction e using Sym2.ind with
  | _ u w =>
    rw [PinningData.edgeFactor_mk]
    split_ifs
    · exact hx
    · exact one_pos

theorem hPart_pos (P : V → Prop) (G' : SimpleGraph V) (b : V → C → ℕ) {x : ℝ} (hx : 0 < x)
    (σ : V → C) : 0 < hPart P G' b x σ :=
  mul_pos (Finset.prod_pos fun _ _ => pow_pos hx _)
    (Finset.prod_pos fun e _ => edgeFactor_pos hx σ e)

theorem gPart_pos (P : V → Prop) (G' : SimpleGraph V) (b : V → C → ℕ) {x : ℝ} (hx : 0 < x)
    (σ : V → C) : 0 < gPart P G' b x σ :=
  mul_pos (Finset.prod_pos fun _ _ => pow_pos hx _)
    (Finset.prod_pos fun e _ => edgeFactor_pos hx σ e)

abbrev splitEquiv (P : V → Prop) : (V → C) ≃ ({w // P w} → C) × ({w // ¬ P w} → C) :=
  Equiv.piEquivPiSubtypeProd P (fun _ => C)

theorem sum_split (P : V → Prop) (F : (V → C) → ℝ) :
    ∑ σ, F σ = ∑ α, ∑ β, F ((splitEquiv P).symm (α, β)) := by
  rw [← Fintype.sum_prod_type', ← (splitEquiv P).symm.sum_comp]

theorem outer_split (P : V → Prop) (α : {w // P w} → C) (β : {w // ¬ P w} → C) :
    outer P ((splitEquiv (C := C) P).symm (α, β)) = β := by
  funext w
  simp [outer, Equiv.piEquivPiSubtypeProd_symm_apply, w.prop]

theorem split_on_P (P : V → Prop) (α : {w // P w} → C) (β β' : {w // ¬ P w} → C) :
    ∀ w, P w → (splitEquiv (C := C) P).symm (α, β) w = (splitEquiv P).symm (α, β') w := by
  intro w hw
  simp [Equiv.piEquivPiSubtypeProd_symm_apply, hw]

theorem split_off_P (P : V → Prop) (α α' : {w // P w} → C) (β : {w // ¬ P w} → C) :
    ∀ w, ¬ P w → (splitEquiv (C := C) P).symm (α, β) w = (splitEquiv P).symm (α', β) w := by
  intro w hw
  simp [Equiv.piEquivPiSubtypeProd_symm_apply, hw]

theorem marginal_formula (P : V → Prop) (G' : SimpleGraph V) (b : V → C → ℕ) {x : ℝ}
    (hx : 0 < x) (hsep : ∀ u w, G'.Adj u w → (P u ↔ P w)) (ξ : {w // ¬ P w} → C) :
    (marginal (Appendix.Girth.DoobPinning.law (⟨G', b⟩ : PinningData V C) x hx) (outer P)).w ξ =
      gPart P G' b x ((splitEquiv P).symm (fun _ => Classical.arbitrary C, ξ)) /
        ∑ β, gPart P G' b x ((splitEquiv P).symm (fun _ => Classical.arbitrary C, β)) := by
  set α₀ : {w // P w} → C := fun _ => Classical.arbitrary C
  set β₀ : {w // ¬ P w} → C := fun _ => Classical.arbitrary C
  set h' : ({w // P w} → C) → ℝ := fun α => hPart P G' b x ((splitEquiv P).symm (α, β₀))
  set g' : ({w // ¬ P w} → C) → ℝ := fun β => gPart P G' b x ((splitEquiv P).symm (α₀, β))
  have hw : ∀ α β, (⟨G', b⟩ : PinningData V C).weight x ((splitEquiv P).symm (α, β)) =
      h' α * g' β := by
    intro α β
    rw [weight_split P G' b x]
    congr 1
    · exact hPart_congr P G' b x hsep _ _ (split_on_P P α β β₀)
    · exact gPart_congr P G' b x _ _ (split_off_P P α α₀ β)
  have hZ : (⟨G', b⟩ : PinningData V C).partition x = (∑ α, h' α) * ∑ β, g' β := by
    unfold PinningData.partition
    rw [sum_split P]
    simp_rw [hw, Finset.sum_mul_sum]
  have hH : 0 < ∑ α, h' α :=
    Finset.sum_pos (fun α _ => hPart_pos P G' b hx _) Finset.univ_nonempty
  have hG : 0 < ∑ β, g' β :=
    Finset.sum_pos (fun β _ => gPart_pos P G' b hx _) Finset.univ_nonempty
  unfold marginal eventMass
  dsimp only
  rw [sum_split P]
  trans ∑ α, h' α * g' ξ / ((∑ α, h' α) * ∑ β, g' β)
  · apply Finset.sum_congr rfl
    intro α _
    rw [Finset.sum_eq_single ξ]
    · rw [if_pos (outer_split P α ξ)]
      change (⟨G', b⟩ : PinningData V C).weight x _ / (⟨G', b⟩ : PinningData V C).partition x = _
      rw [hw, hZ]
    · intro β _ hβ
      rw [if_neg (by rw [outer_split]; exact hβ)]
    · simp
  · rw [← Finset.sum_div, ← Finset.sum_mul]
    field_simp
    rfl

theorem potts_marginal_eq (P : V → Prop) (G' : SimpleGraph V) (b₁ b₂ : V → C → ℕ) {x : ℝ}
    (hx : 0 < x) (hsep : ∀ u w, G'.Adj u w → (P u ↔ P w))
    (hbc : ∀ w, ¬ P w → b₁ w = b₂ w) :
    marginal (Appendix.Girth.DoobPinning.law (⟨G', b₁⟩ : PinningData V C) x hx) (outer P) =
      marginal (Appendix.Girth.DoobPinning.law (⟨G', b₂⟩ : PinningData V C) x hx) (outer P) := by
  apply FinDist.ext
  funext ξ
  rw [marginal_formula P G' b₁ hx hsep, marginal_formula P G' b₂ hx hsep]
  simp_rw [gPart_eq P G' b₁ b₂ x hbc]

end PottsSplit


section Graph
variable {A : Type*} [Fintype A] (G : SimpleGraph A)

theorem enat_eq_of_bounds {m : ℕ∞} {k : ℕ} (h1 : m ≤ k) (h2 : ((k + 1 : ℕ) : ℕ∞) ≤ m + 1) :
    m = k := by
  induction m using ENat.recTopCoe with
  | top => simp at h1
  | coe m =>
    norm_cast at h1 h2 ⊢
    omega

theorem walk_first_step {u w : A} (p : G.Walk u w) {k : ℕ} (hp : p.length = k + 1) :
    ∃ y, G.Adj u y ∧ G.edist y w ≤ k := by
  cases p with
  | nil => simp at hp
  | cons h q =>
    refine ⟨_, h, ?_⟩
    simp only [SimpleGraph.Walk.length_cons, add_left_inj] at hp
    rw [← hp]
    exact SimpleGraph.edist_le q

theorem sphere_card_le (Δ : ℕ) (hdeg : ∀ z, G.degree z ≤ Δ) (r : A) :
    ∀ k : ℕ, (Finset.univ.filter fun z => G.edist r z = k).card ≤ Δ ^ k := by
  intro k
  induction k with
  | zero =>
    have hs : (Finset.univ.filter fun z => G.edist r z = ((0 : ℕ) : ℕ∞)) ⊆ {r} := by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_zero,
        SimpleGraph.edist_eq_zero_iff] at hz
      simp [hz]
    simpa using Finset.card_le_card hs
  | succ k ih =>
    have hsub : (Finset.univ.filter fun z => G.edist r z = ((k + 1 : ℕ) : ℕ∞)) ⊆
        (Finset.univ.filter fun z => G.edist r z = (k : ℕ∞)).biUnion
          (fun y => G.neighborFinset y) := by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe hz
      obtain ⟨y, hzy, hy⟩ := walk_first_step G p.reverse (k := k)
        (by rw [SimpleGraph.Walk.length_reverse, hp])
      have hry : G.edist r y = k := by
        apply enat_eq_of_bounds
        · rw [SimpleGraph.edist_comm]; exact hy
        · have ht : G.edist r z ≤ G.edist r y + G.edist y z := SimpleGraph.edist_triangle
          rw [SimpleGraph.edist_eq_one_iff_adj.mpr hzy.symm, hz] at ht
          exact ht
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborFinset]
      exact ⟨y, hry, hzy.symm⟩
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ y ∈ (Finset.univ.filter fun z => G.edist r z = (k : ℕ∞)),
          (G.neighborFinset y).card := Finset.card_biUnion_le
      _ ≤ ∑ y ∈ (Finset.univ.filter fun z => G.edist r z = (k : ℕ∞)), Δ := by
          apply Finset.sum_le_sum
          intro y _
          rw [SimpleGraph.card_neighborFinset_eq_degree]
          exact hdeg y
      _ = (Finset.univ.filter fun z => G.edist r z = (k : ℕ∞)).card * Δ := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ Δ ^ k * Δ := Nat.mul_le_mul_right _ ih
      _ = Δ ^ (k + 1) := (pow_succ _ _).symm

theorem geom_le_pow {Δ : ℕ} (hΔ : 2 ≤ Δ) : ∀ R : ℕ, ∑ k ∈ Finset.range R, Δ ^ k ≤ Δ ^ R := by
  intro R
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith [Nat.one_le_pow R Δ (by omega)]

theorem ball_card_le (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀ z, G.degree z ≤ Δ) (r : A) (R : ℕ) :
    (Finset.univ.filter fun z => G.edist r z < R).card ≤ Δ ^ R := by
  have hsub : (Finset.univ.filter fun z => G.edist r z < R) ⊆
      (Finset.range R).biUnion (fun k => Finset.univ.filter fun z => G.edist r z = k) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_univ,
      true_and]
    induction h : G.edist r z using ENat.recTopCoe with
    | top => rw [h] at hz; simp at hz
    | coe m =>
      rw [h] at hz
      exact ⟨m, by exact_mod_cast hz, rfl⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range R, (Finset.univ.filter fun z => G.edist r z = k).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range R, Δ ^ k :=
        Finset.sum_le_sum fun k _ => sphere_card_le G Δ hdeg r k
    _ ≤ Δ ^ R := geom_le_pow hΔ R

end Graph

section Numeric

def Lf (n : ℕ) : ℝ := if n = 0 then 0 else 1 + Real.log n

def Fb (Δ R : ℕ) (ε : ℝ) (n : ℕ) : ℝ := (Δ : ℝ) ^ R * (1 + 2 * ε * Lf n)

theorem Lf_nonneg (n : ℕ) : 0 ≤ Lf n := by
  unfold Lf
  split_ifs with h
  · exact le_rfl
  · have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    have := Real.log_nonneg this
    linarith

theorem Lf_mono {m n : ℕ} (h : m ≤ n) : Lf m ≤ Lf n := by
  by_cases hm : m = 0
  · rw [hm]; unfold Lf; simp only [if_true]; exact Lf_nonneg n
  · have hn : n ≠ 0 := by omega
    unfold Lf
    rw [if_neg hm, if_neg hn]
    have hm1 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have := Real.log_le_log hm1 (by exact_mod_cast h : (m : ℝ) ≤ n)
    linarith

theorem Lf_step {n : ℕ} (hn : 1 ≤ n) : Lf (n - 1) + 1 / n ≤ Lf n := by
  rcases eq_or_lt_of_le hn with h | h
  · subst h; simp [Lf]
  · have hn0 : n ≠ 0 := by omega
    have hn1 : n - 1 ≠ 0 := by omega
    unfold Lf
    rw [if_neg hn0, if_neg hn1]
    have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn]; simp
    rw [hc]
    have hpos : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast h
      linarith
    have hnpos : (0 : ℝ) < n := by linarith
    have hkey := Real.one_sub_inv_le_log_of_pos (x := (n : ℝ) / ((n : ℝ) - 1))
      (div_pos hnpos hpos)
    rw [Real.log_div hnpos.ne' hpos.ne', inv_div] at hkey
    have h1 : 1 - ((n : ℝ) - 1) / n = 1 / n := by field_simp; ring
    rw [h1] at hkey
    linarith

theorem Fb_mono {Δ R : ℕ} {ε : ℝ} (hε : 0 ≤ ε) {m n : ℕ} (h : m ≤ n) :
    Fb Δ R ε m ≤ Fb Δ R ε n := by
  unfold Fb
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have := Lf_mono h
  nlinarith

theorem Fb_zero (Δ R : ℕ) (ε : ℝ) : Fb Δ R ε 0 = (Δ : ℝ) ^ R := by
  simp [Fb, Lf]

theorem Fb_step {Δ R : ℕ} {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} (hn : 1 ≤ n) :
    Fb Δ R ε (n - 1) + 2 * (Δ : ℝ) ^ R * (ε / n) ≤ Fb Δ R ε n := by
  unfold Fb
  have := Lf_step hn
  have hΔ : (0 : ℝ) ≤ (Δ : ℝ) ^ R := by positivity
  have h2 : 2 * (Δ : ℝ) ^ R * (ε / n) = (Δ : ℝ) ^ R * (2 * ε * (1 / n)) := by ring
  rw [h2, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ hΔ
  nlinarith

theorem Fb_top {Δ R : ℕ} {ε : ℝ} (hΔ : 3 ≤ Δ) (hR : 2 ≤ R) (hε0 : 0 < ε)
    (hε : ε ≤ 1 / (8 * R * Real.log Δ)) :
    Fb Δ R ε (Δ ^ R) + 1 ≤ 2 * (Δ : ℝ) ^ R := by
  have hΔ1 : (3 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hlog : 2 / 3 ≤ Real.log Δ := by
    have h := Real.one_sub_inv_le_log_of_pos (x := (Δ : ℝ)) (by linarith)
    have : (Δ : ℝ)⁻¹ ≤ 1 / 3 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hΔ1
    linarith
  have hR1 : (2 : ℝ) ≤ R := by exact_mod_cast hR
  set t := (R : ℝ) * Real.log Δ with ht
  have ht2 : 4 / 3 ≤ t := by nlinarith
  have hε' : 8 * t * ε ≤ 1 := by
    have h8 : 0 < 8 * (R : ℝ) * Real.log Δ := by positivity
    rw [le_div_iff₀ h8] at hε
    nlinarith
  have hL : Lf (Δ ^ R) = 1 + t := by
    have hne : Δ ^ R ≠ 0 := pow_ne_zero _ (by omega)
    unfold Lf
    rw [if_neg hne]
    push_cast
    rw [Real.log_pow]
  have hbig : (9 : ℝ) ≤ (Δ : ℝ) ^ R := by
    have : (3 : ℝ) ^ 2 ≤ (Δ : ℝ) ^ R :=
      (pow_le_pow_left₀ (by norm_num) hΔ1 2).trans
        (pow_le_pow_right₀ (by linarith) hR)
    nlinarith
  unfold Fb
  rw [hL]
  have hε1 : ε ≤ 3 / 32 := by nlinarith
  have hkey : 2 * ε * (1 + t) ≤ 7 / 16 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hkey (by linarith : (0 : ℝ) ≤ (Δ : ℝ) ^ R)]

end Numeric


section NormalForm
variable {A : Type u} [Fintype A] {C : Type v} [Fintype C]

theorem restrict_congr (J : PinningData A C) {W : Type u} (g₁ g₂ : W ↪ A)
    (q₁ q₂ : A → Option C) (hg : ∀ w, g₁ w = g₂ w) (hq : ∀ z, q₁ z = q₂ z) :
    restrictPinningData J g₁ q₁ = restrictPinningData J g₂ q₂ := by
  have h1 : g₁ = g₂ := Function.Embedding.ext hg
  have h2 : q₁ = q₂ := funext hq
  subst h1; subst h2; rfl

theorem composePinning_none_eq {W : Type u} (g : W ↪ A) (q : A → Option C)
    (hq : ∀ w, q (g w) = none) : composePinning g q (fun _ => none) = q := by
  funext z
  by_cases hz : z ∈ Set.range g
  · obtain ⟨w, rfl⟩ := hz
    rw [composePinning_apply, hq]
  · exact composePinning_of_not_mem_range g q _ z hz

theorem optionChild_normal (J : PinningData A C) {W : Type u} [Fintype W] (f : Option W ↪ A)
    (p : A → Option C) (hp : ∀ w, p (f w) = none) (a : C) :
    optionChildData (restrictPinningData J f p) a =
      restrictPinningData J (someEmbedding.trans f) (Function.update p (f none) (some a)) := by
  rw [optionChildData_eq_restrictPinningData, restrictPinningData_restrict J f p _ _ hp]
  apply restrict_congr
  · intro w; rfl
  · intro z
    by_cases hz : z ∈ Set.range f
    · obtain ⟨w, rfl⟩ := hz
      rw [composePinning_apply]
      cases w with
      | none => simp [rootOnlyPinning]
      | some o =>
        have hne : f (some o) ≠ f none := fun h => by simpa using f.injective h
        rw [Function.update_of_ne hne, hp]
        rfl
    · rw [composePinning_of_not_mem_range f p _ z hz]
      have hne : z ≠ f none := fun h => hz ⟨none, h.symm⟩
      rw [Function.update_of_ne hne]

theorem childData_normal (J : PinningData A C) {W : Type u} [Fintype W] [DecidableEq W]
    (g : W ↪ A) (q : A → Option C) (hq : ∀ w, q (g w) = none) (w₀ : W) (c : C) :
    DoobPinning.childData (restrictPinningData J g q) w₀ c =
      restrictPinningData J ((Function.Embedding.subtype _).trans g)
        (Function.update q (g w₀) (some c)) := by
  unfold DoobPinning.childData DoobPinning.rootData
  rw [relabelData_eq_restrictPinningData, restrictPinningData_restrict J g q _ _ hq,
    composePinning_none_eq g q hq]
  rw [optionChild_normal J _ q (fun w => hq _) c]
  apply restrict_congr
  · intro u
    simp [DoobPinning.rootIndex, someEmbedding]
  · intro z
    simp [DoobPinning.rootIndex]

end NormalForm

section Sub
variable {A : Type u} [Fintype A] {C : Type v} [Fintype C]
variable {W : Type u} [Fintype W] [DecidableEq W]

/-- The same root, with `w₀` removed from the free set. -/
def f₁ (f : Option W ↪ A) (w₀ : W) : Option (DoobPinning.Remaining w₀) ↪ A :=
  (Function.Embedding.optionMap (Function.Embedding.subtype _)).trans f

/-- The new root `w₀`, with the old root removed from the free set. -/
def e₂ (w₀ : W) : Option (DoobPinning.Remaining w₀) ↪ Option W :=
  (DoobPinning.rootIndex w₀).symm.toEmbedding.trans someEmbedding

def f₂ (f : Option W ↪ A) (w₀ : W) : Option (DoobPinning.Remaining w₀) ↪ A :=
  (e₂ w₀).trans f

@[simp] theorem f₁_none (f : Option W ↪ A) (w₀ : W) : f₁ f w₀ none = f none := rfl
@[simp] theorem f₁_some (f : Option W ↪ A) (w₀ : W) (u : DoobPinning.Remaining w₀) :
    f₁ f w₀ (some u) = f (some u.val) := rfl
@[simp] theorem f₂_none (f : Option W ↪ A) (w₀ : W) : f₂ f w₀ none = f (some w₀) := by
  simp [f₂, e₂, DoobPinning.rootIndex, someEmbedding]
@[simp] theorem f₂_some (f : Option W ↪ A) (w₀ : W) (u : DoobPinning.Remaining w₀) :
    f₂ f w₀ (some u) = f (some u.val) := by
  simp [f₂, e₂, DoobPinning.rootIndex, someEmbedding]

theorem range_f₁ (f : Option W ↪ A) (w₀ : W) (z : A) :
    z ∈ Set.range (f₁ f w₀) ↔ z ∈ Set.range f ∧ z ≠ f (some w₀) := by
  constructor
  · rintro ⟨y, rfl⟩
    cases y with
    | none => exact ⟨⟨none, rfl⟩, fun h => by simpa using f.injective h⟩
    | some u =>
      refine ⟨⟨some u.val, rfl⟩, fun h => u.prop ?_⟩
      simpa using f.injective h
  · rintro ⟨⟨y, rfl⟩, hne⟩
    cases y with
    | none => exact ⟨none, rfl⟩
    | some w =>
      have hw : w ≠ w₀ := fun h => hne (by rw [h])
      exact ⟨some ⟨w, hw⟩, rfl⟩

theorem range_f₂ (f : Option W ↪ A) (w₀ : W) (z : A) :
    z ∈ Set.range (f₂ f w₀) ↔ z ∈ Set.range f ∧ z ≠ f none := by
  constructor
  · rintro ⟨y, rfl⟩
    cases y with
    | none =>
      rw [f₂_none]
      exact ⟨⟨some w₀, rfl⟩, fun h => by simpa using f.injective h⟩
    | some u =>
      rw [f₂_some]
      exact ⟨⟨some u.val, rfl⟩, fun h => by simpa using f.injective h⟩
  · rintro ⟨⟨y, rfl⟩, hne⟩
    cases y with
    | none => exact absurd rfl hne
    | some w =>
      by_cases hw : w = w₀
      · subst hw; exact ⟨none, f₂_none f w⟩
      · exact ⟨some ⟨w, hw⟩, f₂_some f w₀ ⟨w, hw⟩⟩

theorem hp_update {W' : Type u} (f' : Option W' ↪ A) (f : Option W ↪ A) (p : A → Option C)
    (hp : ∀ z, p z = none ↔ z ∈ Set.range f) (z₀ : A)
    (hr : ∀ z, z ∈ Set.range f' ↔ z ∈ Set.range f ∧ z ≠ z₀) (c : C) :
    ∀ z, Function.update p z₀ (some c) z = none ↔ z ∈ Set.range f' := by
  intro z
  rw [hr]
  by_cases hz : z = z₀
  · subst hz; simp
  · rw [Function.update_of_ne hz, hp]
    exact ⟨fun h => ⟨h, hz⟩, fun h => h.1⟩

theorem hp_f₁ (f : Option W ↪ A) (p : A → Option C) (hp : ∀ z, p z = none ↔ z ∈ Set.range f)
    (w₀ : W) (c : C) :
    ∀ z, Function.update p (f (some w₀)) (some c) z = none ↔ z ∈ Set.range (f₁ f w₀) :=
  hp_update _ f p hp _ (range_f₁ f w₀) c

theorem hp_f₂ (f : Option W ↪ A) (p : A → Option C) (hp : ∀ z, p z = none ↔ z ∈ Set.range f)
    (w₀ : W) (a : C) :
    ∀ z, Function.update p (f none) (some a) z = none ↔ z ∈ Set.range (f₂ f w₀) :=
  hp_update _ f p hp _ (range_f₂ f w₀) a

theorem Q1 (J : PinningData A C) (f : Option W ↪ A) (p : A → Option C)
    (hp : ∀ z, p z = none ↔ z ∈ Set.range f) (w₀ : W) (a c : C) :
    DoobPinning.childData (optionChildData (restrictPinningData J f p) a) w₀ c =
      optionChildData (restrictPinningData J (f₁ f w₀)
        (Function.update p (f (some w₀)) (some c))) a := by
  have hp0 : ∀ w, p (f w) = none := fun w => (hp _).mpr ⟨w, rfl⟩
  rw [optionChild_normal J f p hp0 a]
  rw [childData_normal J _ _ (fun w => by
    have hne : (someEmbedding.trans f) w ≠ f none := fun h => by
      simpa [someEmbedding] using f.injective h
    rw [Function.update_of_ne hne]; exact hp0 _) w₀ c]
  rw [optionChild_normal J (f₁ f w₀) _ (fun w => ((hp_f₁ f p hp w₀ c) _).mpr ⟨w, rfl⟩) a]
  apply restrict_congr
  · intro u; rfl
  · intro z
    have hne : f none ≠ f (some w₀) := fun h => by simpa using f.injective h
    change Function.update (Function.update p (f none) (some a)) (f (some w₀)) (some c) z =
      Function.update (Function.update p (f (some w₀)) (some c)) (f none) (some a) z
    rw [Function.update_comm hne]

theorem Q2 (J : PinningData A C) (f : Option W ↪ A) (p : A → Option C)
    (hp : ∀ z, p z = none ↔ z ∈ Set.range f) (w₀ : W) (a c : C) :
    DoobPinning.childData (optionChildData (restrictPinningData J f p) a) w₀ c =
      optionChildData (restrictPinningData J (f₂ f w₀)
        (Function.update p (f none) (some a))) c := by
  have hp0 : ∀ w, p (f w) = none := fun w => (hp _).mpr ⟨w, rfl⟩
  rw [optionChild_normal J f p hp0 a]
  rw [childData_normal J _ _ (fun w => by
    have hne : (someEmbedding.trans f) w ≠ f none := fun h => by
      simpa [someEmbedding] using f.injective h
    rw [Function.update_of_ne hne]; exact hp0 _) w₀ c]
  rw [optionChild_normal J (f₂ f w₀) _ (fun w => ((hp_f₂ f p hp w₀ a) _).mpr ⟨w, rfl⟩) c]
  apply restrict_congr
  · intro u
    change f (some u.val) = f₂ f w₀ (some u)
    rw [f₂_some]
  · intro z
    rw [f₂_none]
    rfl

end Sub


section Extend
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] [Nonempty C]

theorem ham_eq_sum (σ τ : V → C) : ham σ τ = ∑ u, if σ u = τ u then (0 : ℝ) else 1 := by
  unfold ham hamCard
  rw [Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro u _
  split_ifs <;> simp_all

theorem ham_extend (w₀ : V) (c c' : C) (σ τ : DoobPinning.Remaining w₀ → C) :
    ham (DoobPinning.extendColouring w₀ c σ) (DoobPinning.extendColouring w₀ c' τ) =
      ham σ τ + (if c = c' then 0 else 1) := by
  rw [ham_eq_sum, ham_eq_sum, Fintype.sum_eq_add_sum_subtype_ne _ w₀]
  simp only [DoobPinning.extendColouring_root, DoobPinning.extendColouring_remaining]
  rw [add_comm]

theorem W_given_le (w₀ : V) (c c' : C) (μ ν : FinDist (DoobPinning.Remaining w₀ → C)) :
    W ham (mapLaw μ (DoobPinning.extendColouring w₀ c))
      (mapLaw ν (DoobPinning.extendColouring w₀ c')) ≤
      W ham μ ν + (if c = c' then 0 else 1) := by
  refine (W_mapLaw_le _ _ ham ham_nonneg).trans ?_
  have he : (fun σ τ => ham (DoobPinning.extendColouring w₀ c σ)
      (DoobPinning.extendColouring w₀ c' τ)) =
      fun σ τ => ham σ τ + (if c = c' then (0 : ℝ) else 1) := by
    funext σ τ; exact ham_extend w₀ c c' σ τ
  rw [he]
  exact W_add_const_le ham ham_nonneg _ (by split_ifs <;> norm_num) μ ν

end Extend

section Breadth
variable {A : Type u} [Fintype A]

def breadth (G : SimpleGraph A) (R : ℕ) {W : Type u} [Fintype W] (f : Option W ↪ A) : ℕ :=
  (Finset.univ.filter fun w : W => G.edist (f none) (f (some w)) = R).card

theorem card_filter_comp_le {W : Type*} [Fintype W] (g : W → A) (hg : Function.Injective g)
    (P : A → Prop) :
    (Finset.univ.filter fun w => P (g w)).card ≤ (Finset.univ.filter P).card := by
  apply Finset.card_le_card_of_injOn g
  · intro w hw
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢
    exact hw
  · exact hg.injOn

end Breadth


section Instances

theorem partition_pos' {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [Nonempty C]
    (dC : DecidableEq C) (I : PinningData V C) {x : ℝ} (hx : 0 < x) :
    0 < @PinningData.partition V C _ _ _ dC I x :=
  @PinningData.partition_pos_of_parameter_pos V C _ _ _ dC I _ x hx

theorem law_eq_gibbs {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]
    [Nonempty C] (iC dC : DecidableEq C) (I : PinningData V C) (x : ℝ) (hx : 0 < x) (h0 : 0 ≤ x)
    (hZ : 0 < @PinningData.partition V C _ _ _ dC I x) :
    @DoobPinning.law V C _ _ _ iC _ I x hx = @PinningData.gibbs V C _ _ _ dC I x h0 hZ := by
  have h : iC = dC := Subsingleton.elim _ _
  subst h
  rfl

end Instances

section Main
variable {C : Type v} [Fintype C] [DecidableEq C] [Nonempty C]
variable {A : Type u} [Fintype A]

theorem degree_le_of_degreeBound (J : PinningData A C) {Δ : ℕ} (h : J.DegreeBound Δ) (z : A) :
    J.graph.degree z ≤ Δ := by
  have := h z
  unfold PinningData.constraintDegree at this
  omega

theorem breadth_le (J : PinningData A C) {Δ : ℕ} (hd : J.DegreeBound Δ) (R : ℕ)
    {W : Type u} [Fintype W] (f : Option W ↪ A) : breadth J.graph R f ≤ Δ ^ R :=
  (card_filter_comp_le (fun w => f (some w)) (fun _ _ h => by simpa using f.injective h)
    (fun z => J.graph.edist (f none) z = R)).trans
    (sphere_card_le J.graph Δ (degree_le_of_degreeBound J hd) (f none) R)

theorem breadth_f₁_le (G : SimpleGraph A) (R : ℕ) {W : Type u} [Fintype W] [DecidableEq W]
    (f : Option W ↪ A) (w₀ : W) (hw₀ : G.edist (f none) (f (some w₀)) = R) :
    breadth G R (f₁ f w₀) ≤ breadth G R f - 1 := by
  unfold breadth
  have hmem : w₀ ∈ (Finset.univ.filter fun w : W => G.edist (f none) (f (some w)) = R) := by
    simp [hw₀]
  rw [← Finset.card_erase_of_mem hmem]
  apply Finset.card_le_card_of_injOn (fun u => u.val)
  · intro u hu
    rw [Finset.mem_coe, Finset.mem_filter] at hu
    rw [Finset.mem_coe, Finset.mem_erase, Finset.mem_filter]
    exact ⟨u.prop, Finset.mem_univ _, by simpa using hu.2⟩
  · intro u _ u' _ h
    exact Subtype.ext h

theorem lt_step (G : SimpleGraph A) {r y z : A} {R : ℕ} (hy : G.edist r y < R)
    (hadj : G.Adj y z) (hz : G.edist r z ≠ R) : G.edist r z < R := by
  have h1 : G.edist r z ≤ G.edist r y + 1 := by
    have := SimpleGraph.edist_triangle (G := G) (u := r) (v := y) (w := z)
    rwa [SimpleGraph.edist_eq_one_iff_adj.mpr hadj] at this
  have h2 : G.edist r y + 1 ≤ R := Order.add_one_le_of_lt hy
  exact lt_of_le_of_ne (h1.trans h2) hz

/-- CLMM Lemma 5.17, case `ℓ = 0`: the whole sphere is pinned. -/
theorem separated_case (J : PinningData A C) {Δ R : ℕ} (hΔ : 2 ≤ Δ) (hR : 2 ≤ R)
    (hdeg : ∀ z, J.graph.degree z ≤ Δ) {x : ℝ} (hx : 0 < x) {W : Type u} [Fintype W]
    (f : Option W ↪ A) (p : A → Option C) (hℓ : breadth J.graph R f = 0) (a b : C) :
    FinDist.W ham (DoobPinning.law (optionChildData (restrictPinningData J f p) a) x hx)
      (DoobPinning.law (optionChildData (restrictPinningData J f p) b) x hx) ≤ (Δ : ℝ) ^ R := by
  have hno : ∀ w, J.graph.edist (f none) (f (some w)) ≠ R := by
    intro w hw
    have hmem : w ∈ (Finset.univ.filter fun w : W => J.graph.edist (f none) (f (some w)) = R) := by
      simp [hw]
    unfold breadth at hℓ
    rw [Finset.card_eq_zero] at hℓ
    rw [hℓ] at hmem
    simp at hmem
  let P : W → Prop := fun w => J.graph.edist (f none) (f (some w)) < R
  let I := restrictPinningData J f p
  have hsep : ∀ u w, (optionMiddleData I).graph.Adj u w → (P u ↔ P w) := by
    intro u w huw
    have hadj : J.graph.Adj (f (some u)) (f (some w)) := huw
    exact ⟨fun hu => lt_step J.graph hu hadj (hno w), fun hw => lt_step J.graph hw hadj.symm (hno u)⟩
  have hbc : ∀ w, ¬ P w → (optionChildData I a).boundaryCount w =
      (optionChildData I b).boundaryCount w := by
    intro w hw
    have hna : ¬ I.graph.Adj none (some w) := by
      intro hmem
      have hadj : J.graph.Adj (f none) (f (some w)) := hmem
      apply hw
      show J.graph.edist (f none) (f (some w)) < R
      rw [SimpleGraph.edist_eq_one_iff_adj.mpr hadj]
      exact_mod_cast (by omega : 1 < R)
    funext c
    rw [optionChildData_count, optionChildData_count]
    simp [hna]
  have hm := potts_marginal_eq P (optionChildData I a).graph _ _ hx hsep hbc
  have hW := W_ham_le_of_common_marginal P _ _ hm
  refine le_trans hW ?_
  rw [Fintype.card_subtype]
  have hc := (card_filter_comp_le (fun w => f (some w)) (fun _ _ h => by simpa using f.injective h)
    (fun z => J.graph.edist (f none) z < R)).trans (ball_card_le J.graph Δ hΔ hdeg (f none) R)
  exact_mod_cast hc

/-- CLMM Lemma 5.17, case `ℓ ≥ 1`, combined with the Lemma 5.18 induction step. -/
theorem recursion_case {Δ g R : ℕ} {x ε : ℝ} (hΔ : 3 ≤ Δ) (hR : 2 ≤ R) (hx : 0 < x)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / (8 * R * Real.log Δ))
    (hS : CI2ZF.Appendix.CLMM.FixedAmbientSphereDecay.{u,v} C Δ g R x ε)
    (J : PinningData A C) (hJd : J.DegreeBound Δ) (hJg : (g : ℕ∞) ≤ J.graph.egirth)
    {W : Type u} [Fintype W] (f : Option W ↪ A) (p : A → Option C)
    (hp : ∀ z, p z = none ↔ z ∈ Set.range f) (hℓ : breadth J.graph R f ≠ 0)
    (IH : ∀ (W' : Type u) [Fintype W'], Fintype.card W' < Fintype.card W →
      ∀ (f' : Option W' ↪ A) (p' : A → Option C), (∀ z, p' z = none ↔ z ∈ Set.range f') →
      ∀ a b : C,
        FinDist.W ham (DoobPinning.law (optionChildData (restrictPinningData J f' p') a) x hx)
          (DoobPinning.law (optionChildData (restrictPinningData J f' p') b) x hx) ≤
          Fb Δ R ε (breadth J.graph R f'))
    (a b : C) :
    FinDist.W ham (DoobPinning.law (optionChildData (restrictPinningData J f p) a) x hx)
      (DoobPinning.law (optionChildData (restrictPinningData J f p) b) x hx) ≤
      Fb Δ R ε (breadth J.graph R f) := by
  let S := Finset.univ.filter fun w : W => J.graph.edist (f none) (f (some w)) = R
  have hSne : S.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hℓ)
  let TV : W → ℝ := fun w => (1 / 2 : ℝ) * ∑ c,
    |CI2ZF.Appendix.CLMM.singleSiteMass (DoobPinning.law (optionChildData (restrictPinningData J f p) a) x hx) w c -
      CI2ZF.Appendix.CLMM.singleSiteMass (DoobPinning.law (optionChildData (restrictPinningData J f p) b) x hx) w c|
  obtain ⟨w₀, hw₀S, hmin⟩ := S.exists_min_image TV hSne
  have hw₀ : J.graph.edist (f none) (f (some w₀)) = R := (Finset.mem_filter.mp hw₀S).2
  have hinf : CI2ZF.Appendix.CLMM.ambientSphereInfluence J.graph f R
      (DoobPinning.law (optionChildData (restrictPinningData J f p) a) x hx)
      (DoobPinning.law (optionChildData (restrictPinningData J f p) b) x hx) ≤ ε := by
    have h := hS J hJd hJg f p hp a b hx.le (partition_pos' _ _ hx) (partition_pos' _ _ hx)
    convert h using 2 <;> exact law_eq_gibbs (V := W) (C := C) _ _ _ _ _ _ _
  have hsum : CI2ZF.Appendix.CLMM.ambientSphereInfluence J.graph f R
      (DoobPinning.law (optionChildData (restrictPinningData J f p) a) x hx)
      (DoobPinning.law (optionChildData (restrictPinningData J f p) b) x hx) = ∑ w ∈ S, TV w := by
    unfold CI2ZF.Appendix.CLMM.ambientSphereInfluence
    rw [Finset.sum_filter]
  have hℓpos : (0 : ℝ) < breadth J.graph R f := by exact_mod_cast Nat.pos_of_ne_zero hℓ
  have hTV : TV w₀ ≤ ε / breadth J.graph R f := by
    have h1 : S.card • TV w₀ ≤ ∑ w ∈ S, TV w := Finset.card_nsmul_le_sum S TV (TV w₀) hmin
    rw [nsmul_eq_mul] at h1
    rw [le_div_iff₀ hℓpos, mul_comm]
    have : (S.card : ℝ) = breadth J.graph R f := rfl
    rw [this] at h1
    linarith
  have hcard : Fintype.card (DoobPinning.Remaining w₀) < Fintype.card W :=
    DoobPinning.remaining_card_lt w₀
  have hFtop := Fb_top hΔ hR hε0 hε
  have hB : 0 < Fb Δ R ε (Δ ^ R) + 1 := by
    have : 0 ≤ Fb Δ R ε (Δ ^ R) := by
      unfold Fb; have := Lf_nonneg (Δ ^ R); positivity
    linarith
  have hsplit := W_le_split ham ham_nonneg
    (DoobPinning.law (optionChildData (restrictPinningData J f p) a) x hx)
    (DoobPinning.law (optionChildData (restrictPinningData J f p) b) x hx) (fun σ => σ w₀)
    (Fb Δ R ε (breadth J.graph R f - 1)) (Fb Δ R ε (Δ ^ R) + 1) hB ?_ ?_
  · have hTV' : (∑ c, |(marginal (DoobPinning.law (optionChildData (restrictPinningData J f p) a)
        x hx) (fun σ => σ w₀)).w c - (marginal (DoobPinning.law
        (optionChildData (restrictPinningData J f p) b) x hx) (fun σ => σ w₀)).w c|) / 2 =
        TV w₀ := by
      simp only [TV, one_div]
      rw [div_eq_inv_mul]
      rfl
    rw [hTV'] at hsplit
    have hstep := Fb_step (Δ := Δ) (R := R) hε0.le (Nat.one_le_iff_ne_zero.mpr hℓ)
    have hε' : 0 ≤ ε / breadth J.graph R f := div_nonneg hε0.le hℓpos.le
    calc _ ≤ _ := hsplit
      _ ≤ Fb Δ R ε (breadth J.graph R f - 1) +
          (Fb Δ R ε (Δ ^ R) + 1) * (ε / breadth J.graph R f) := by gcongr
      _ ≤ Fb Δ R ε (breadth J.graph R f - 1) +
          2 * (Δ : ℝ) ^ R * (ε / breadth J.graph R f) := by gcongr
      _ ≤ _ := hstep
  · intro c
    show FinDist.W ham (Doob.given (DoobPinning.law (optionChildData (restrictPinningData J f p) a)
      x hx) (fun σ => σ w₀) c) (Doob.given (DoobPinning.law
      (optionChildData (restrictPinningData J f p) b) x hx) (fun σ => σ w₀) c) ≤ _
    rw [DoobPinning.given_eq_child _ w₀ c x hx, DoobPinning.given_eq_child _ w₀ c x hx]
    refine (W_given_le w₀ c c _ _).trans ?_
    rw [if_pos rfl, add_zero, Q1 J f p hp w₀ a c, Q1 J f p hp w₀ b c]
    convert (IH _ hcard (f₁ f w₀) _ (hp_f₁ f p hp w₀ c) a b).trans
      (Fb_mono hε0.le (breadth_f₁_le J.graph R f w₀ hw₀)) using 3
  · intro c c' hcc'
    show FinDist.W ham (Doob.given (DoobPinning.law (optionChildData (restrictPinningData J f p) a)
      x hx) (fun σ => σ w₀) c) (Doob.given (DoobPinning.law
      (optionChildData (restrictPinningData J f p) b) x hx) (fun σ => σ w₀) c') ≤ _
    rw [DoobPinning.given_eq_child _ w₀ c x hx, DoobPinning.given_eq_child _ w₀ c' x hx]
    refine (W_given_le w₀ c c' _ _).trans ?_
    rw [if_neg hcc']
    have h1 : FinDist.W ham
        (DoobPinning.law (DoobPinning.childData
          (optionChildData (restrictPinningData J f p) a) w₀ c) x hx)
        (DoobPinning.law (DoobPinning.childData
          (optionChildData (restrictPinningData J f p) a) w₀ c') x hx) ≤ Fb Δ R ε (Δ ^ R) := by
      rw [Q2 J f p hp w₀ a c, Q2 J f p hp w₀ a c']
      convert (IH _ hcard (f₂ f w₀) _ (hp_f₂ f p hp w₀ a) c c').trans
        (Fb_mono hε0.le (breadth_le J hJd R _)) using 3
      rfl
    have h2 : FinDist.W ham
        (DoobPinning.law (DoobPinning.childData
          (optionChildData (restrictPinningData J f p) a) w₀ c') x hx)
        (DoobPinning.law (DoobPinning.childData
          (optionChildData (restrictPinningData J f p) b) w₀ c') x hx) ≤
          Fb Δ R ε (breadth J.graph R f - 1) := by
      rw [Q1 J f p hp w₀ a c', Q1 J f p hp w₀ b c']
      convert (IH _ hcard (f₁ f w₀) _ (hp_f₁ f p hp w₀ c') a b).trans
        (Fb_mono hε0.le (breadth_f₁_le J.graph R f w₀ hw₀)) using 3
      rfl
    have h3 := W_triangle ham_nonneg ham_nonneg ham_nonneg ham_triangle
      (DoobPinning.law (DoobPinning.childData
        (optionChildData (restrictPinningData J f p) a) w₀ c) x hx)
      (DoobPinning.law (DoobPinning.childData
        (optionChildData (restrictPinningData J f p) a) w₀ c') x hx)
      (DoobPinning.law (DoobPinning.childData
        (optionChildData (restrictPinningData J f p) b) w₀ c') x hx)
    linarith

/-- CLMM Lemma 5.18: induction on the number of free vertices, for every
further pinning of the fixed base `J`, with distances measured in `J.graph`. -/
theorem main_bound {Δ g R : ℕ} {x ε : ℝ} (hΔ : 3 ≤ Δ) (hR : 2 ≤ R) (hx : 0 < x)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / (8 * R * Real.log Δ))
    (hS : CI2ZF.Appendix.CLMM.FixedAmbientSphereDecay.{u,v} C Δ g R x ε)
    (J : PinningData A C) (hJd : J.DegreeBound Δ) (hJg : (g : ℕ∞) ≤ J.graph.egirth) :
    ∀ (n : ℕ) (W : Type u) [Fintype W], Fintype.card W = n →
      ∀ (f : Option W ↪ A) (p : A → Option C), (∀ z, p z = none ↔ z ∈ Set.range f) →
      ∀ a b : C,
        FinDist.W ham (DoobPinning.law (optionChildData (restrictPinningData J f p) a) x hx)
          (DoobPinning.law (optionChildData (restrictPinningData J f p) b) x hx) ≤
          Fb Δ R ε (breadth J.graph R f) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W _ hn f p hp a b
    by_cases hℓ : breadth J.graph R f = 0
    · rw [hℓ, Fb_zero]
      exact separated_case J (by omega) hR (degree_le_of_degreeBound J hJd) hx f p hℓ a b
    · apply recursion_case hΔ hR hx hε0 hε hS J hJd hJg f p hp hℓ _ a b
      intro W' _ hlt f' p' hp' a' b'
      exact ih _ (hn ▸ hlt) W' rfl f' p' hp' a' b'

end Main

/-- CLMM2023, Lemma 5.13: fixed-ambient sphere influence decay implies the
Hamming coupling bound `2 Δ^R` for the two root-child Potts laws. -/
theorem sphere_to_coupling (C : Type v) [Fintype C] [DecidableEq C] [Nonempty C] :
    ∀ (Δ g R : ℕ) (x ε : ℝ), 3 ≤ Δ → 2 ≤ R →
    ∀ (hx : 0 < x), x ≤ 1 → 0 < ε → ε ≤ 1 / (8 * R * Real.log Δ) →
    FixedAmbientSphereDecay.{u,v} C Δ g R x ε →
    ∀ {O : Type u} [Fintype O] (I : PinningData (Option O) C),
      I.DegreeBound Δ → (g : ℕ∞) ≤ I.graph.egirth → ∀ (a b : C)
      (ha : 0 < (optionChildData I a).partition x)
      (hb : 0 < (optionChildData I b).partition x),
      W ham ((optionChildData I a).gibbs x hx.le ha)
        ((optionChildData I b).gibbs x hx.le hb) ≤ 2 * (Δ : ℝ) ^ R := by
  intro Δ g R x ε hΔ hR hx _hx1 hε0 hε hS O _ I hId hIg a b ha hb
  have hmain := main_bound hΔ hR hx hε0 hε hS I hId hIg _ O rfl
    (Function.Embedding.refl (Option O)) (fun _ => none)
    (fun z => ⟨fun _ => ⟨z, rfl⟩, fun _ => rfl⟩) a b
  rw [restrictPinningData_id] at hmain
  have h2 := Fb_mono (Δ := Δ) (R := R) hε0.le
    (breadth_le I hId R (Function.Embedding.refl (Option O)))
  have h3 := Fb_top hΔ hR hε0 hε
  have h4 : FinDist.W ham (DoobPinning.law (optionChildData I a) x hx)
      (DoobPinning.law (optionChildData I b) x hx) ≤ 2 * (Δ : ℝ) ^ R := by linarith
  convert h4 using 2 <;> exact (law_eq_gibbs _ _ _ _ _ _ _).symm

end
end CI2ZF.Appendix.CLMM.Lemma513
