import CI2ZF.Coupling.Edge.Slots.SlotLift
import CI2ZF.Coupling.Edge.Finite.CI

/-! # `lem:edge-one-label` for the countable slot lift

Companion, Appendix "edge Potts", Lemma 8.5, for the actual countable
lifted laws `ν_{F,B}` of `CI2ZF/Coupling/Edge/Slots/SlotLift.lean`
(countable states `C × ℕ × ℕ`, countable labels `C × ℕ`).

We define couplings of two countable probability laws, the expected Hamming
cost, and the Wasserstein distance `W_{1,F}` as the infimum of the costs.
The main theorem proves the paper's bound

  `W_{1,F}(ν_{F,B^α}, ν_{F,B^β}) ≤ (Δ-1)/2 · (1 - ((Δ-1)/Δ)^n)`

for every occupied-label comparison with at most `n` free edges which
satisfies the three bounds (load), (fibre), (slack); i.e. `T_n` is at most
the stated envelope, and `T_0 = 0`.

Proof route.  For each `N`, lump all slots `≥ N` of the countable slot law
into one slot `N`.  The lumped model is a finite weighted endpoint-label
system, which satisfies the three bounds *exactly* (the compatible activity
`M_e(B)` is unchanged when all occupied labels have slot `< N`), so the
library's finite one-label theorem applies to it.  The finite and countable
weights agree on configurations using only slots `< N`, and the remaining
mass of both tends to zero.  An explicit gluing construction turns the finite
optimal coupling into a countable coupling whose cost tends to the finite
bound.
-/

namespace CI2ZF.Appendix.Edge.OneLabel
open PottsCI PottsCI.FinDist CI2ZF.Appendix.Edge Filter Topology
open scoped BigOperators
noncomputable section
attribute [local instance low] Classical.propDecidable
set_option linter.unusedSectionVars false

/-! ## Couplings of countable laws -/

section Abstract
variable {Ω : Type*}

/-- A coupling of two countable weight functions `p` and `q`. -/
structure CCoupling (p q : Ω → ℝ) where
  w : Ω × Ω → ℝ
  nonneg : ∀ z, 0 ≤ w z
  row : ∀ x, HasSum (fun y => w (x, y)) (p x)
  col : ∀ y, HasSum (fun x => w (x, y)) (q y)

namespace CCoupling
variable {p q : Ω → ℝ}

/-- Expected cost of a coupling. -/
def cost (π : CCoupling p q) (d : Ω → Ω → ℝ) : ℝ := ∑' z, π.w z * d z.1 z.2

theorem summable (π : CCoupling p q) (hp : Summable p) : Summable π.w := by
  refine (summable_prod_of_nonneg (fun z => π.nonneg z)).mpr
    ⟨fun x => (π.row x).summable, ?_⟩
  simpa only [(π.row _).tsum_eq] using hp

/-- For a probability law and a bounded cost the expected cost is a genuine
convergent sum, so `cost` is never a junk value. -/
theorem summable_cost (π : CCoupling p q) (hp : Summable p) {d : Ω → Ω → ℝ} {D : ℝ}
    (hd : ∀ x y, 0 ≤ d x y) (hD : ∀ x y, d x y ≤ D) :
    Summable (fun z => π.w z * d z.1 z.2) :=
  Summable.of_nonneg_of_le (fun z => mul_nonneg (π.nonneg z) (hd _ _))
    (fun z => mul_le_mul_of_nonneg_left (hD _ _) (π.nonneg z)) ((π.summable hp).mul_right D)

theorem cost_nonneg (π : CCoupling p q) {d : Ω → Ω → ℝ} (hd : ∀ x y, 0 ≤ d x y) :
    0 ≤ π.cost d :=
  tsum_nonneg fun z => mul_nonneg (π.nonneg z) (hd _ _)

end CCoupling

/-- The transport (Wasserstein) distance between two countable laws for the
cost `d`: the infimum of the expected costs of all couplings. -/
def CW (d : Ω → Ω → ℝ) (p q : Ω → ℝ) : ℝ :=
  sInf (Set.range fun π : CCoupling p q => π.cost d)

theorem CW_nonneg {d : Ω → Ω → ℝ} (hd : ∀ x y, 0 ≤ d x y) (p q : Ω → ℝ) : 0 ≤ CW d p q := by
  apply Real.sInf_nonneg
  rintro _ ⟨π, rfl⟩
  exact π.cost_nonneg hd

theorem CW_le {d : Ω → Ω → ℝ} (hd : ∀ x y, 0 ≤ d x y) {p q : Ω → ℝ} {b : ℝ}
    (h : ∀ η > 0, ∃ π : CCoupling p q, π.cost d ≤ b + η) : CW d p q ≤ b := by
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨π, hπ⟩ := h η hη
  have hb : BddBelow (Set.range fun π : CCoupling p q => π.cost d) :=
    ⟨0, by rintro _ ⟨π, rfl⟩; exact π.cost_nonneg hd⟩
  exact (csInf_le hb ⟨π, rfl⟩).trans hπ

/-- The independent coupling of two probability laws. -/
def prodCoupling (p q : Ω → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ y, 0 ≤ q y)
    (hp : HasSum p 1) (hq : HasSum q 1) : CCoupling p q where
  w z := p z.1 * q z.2
  nonneg z := mul_nonneg (hp0 _) (hq0 _)
  row x := by simpa using hq.mul_left (p x)
  col y := by simpa using hp.mul_right (q y)

/-! ## Gluing a finite coupling into a countable one -/

section Transfer
variable {S : Type*} [Fintype S]

/-- Let `J : S → Ω` embed a finite space. On the `good` part of `S`, the
countable laws `p, q` are constant multiples `cα μ`, `cβ ν` of finite laws.
Then every finite coupling `π'` of `μ, ν` produces a countable coupling of
`p, q` whose cost is at most `λ · cost π' + D · (1 - λ(1 - μ(bad) - ν(bad)))`,
where `λ = min cα cβ` and `D` bounds the cost function. -/
theorem transfer (J : S → Ω) (hJ : Function.Injective J) (good : S → Prop)
    (p q : Ω → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ y, 0 ≤ q y)
    (hp : HasSum p 1) (hq : HasSum q 1)
    (μ ν : FinDist S) (π' : Coupling μ ν) {cα cβ : ℝ} (hcα : 0 ≤ cα) (hcβ : 0 ≤ cβ)
    (hμ : ∀ σ, good σ → p (J σ) = cα * μ.w σ) (hν : ∀ σ, good σ → q (J σ) = cβ * ν.w σ)
    (d : Ω → Ω → ℝ) (dS : S → S → ℝ) (hdS : ∀ σ σ', d (J σ) (J σ') = dS σ σ')
    (hdS0 : ∀ σ σ', 0 ≤ dS σ σ') {D : ℝ} (hD : 0 ≤ D)
    (hd0 : ∀ x y, 0 ≤ d x y) (hdD : ∀ x y, d x y ≤ D) :
    ∃ π : CCoupling p q, ∃ c, HasSum (fun z => π.w z * d z.1 z.2) c ∧
      c ≤ min cα cβ * π'.cost dS + D * (1 - min cα cβ *
        (1 - ∑ σ ∈ Finset.univ.filter (fun σ => ¬ good σ), μ.w σ
           - ∑ σ ∈ Finset.univ.filter (fun σ => ¬ good σ), ν.w σ)) := by
  set lam := min cα cβ with hlam
  have hlam0 : 0 ≤ lam := le_min hcα hcβ
  set Sg := Finset.univ.filter good with hSg
  set Sb := Finset.univ.filter (fun σ => ¬ good σ) with hSb
  set X : S → ℝ := fun σ => ∑ σ' ∈ Sg, π'.w σ σ' with hXdef
  set Y : S → ℝ := fun σ' => ∑ σ ∈ Sg, π'.w σ σ' with hYdef
  set m := lam * ∑ σ ∈ Sg, X σ with hm
  set P : Ω × Ω → ℝ := fun z =>
    lam * ∑ σ ∈ Sg, ∑ σ' ∈ Sg, if z = (J σ, J σ') then π'.w σ σ' else 0 with hPdef
  set r : Ω → ℝ := fun x => lam * ∑ σ ∈ Sg, if x = J σ then X σ else 0 with hrdef
  set c : Ω → ℝ := fun y => lam * ∑ σ' ∈ Sg, if y = J σ' then Y σ' else 0 with hcdef
  have hP0 : ∀ z, 0 ≤ P z := fun z => mul_nonneg hlam0 (Finset.sum_nonneg fun σ _ =>
    Finset.sum_nonneg fun σ' _ => by split_ifs <;> first | exact π'.nonneg _ _ | exact le_rfl)
  have hX0 : ∀ σ, 0 ≤ X σ := fun σ => Finset.sum_nonneg fun _ _ => π'.nonneg _ _
  have hY0 : ∀ σ, 0 ≤ Y σ := fun σ => Finset.sum_nonneg fun _ _ => π'.nonneg _ _
  -- rows and columns of the finitely supported part
  have hProw : ∀ x, HasSum (fun y => P (x, y)) (r x) := by
    intro x
    have h : ∀ σ ∈ Sg, HasSum
        (fun y => ∑ σ' ∈ Sg, if (x, y) = (J σ, J σ') then π'.w σ σ' else 0)
        (if x = J σ then X σ else 0) := by
      intro σ _
      by_cases hx : x = J σ
      · rw [if_pos hx]
        apply hasSum_sum
        intro σ' _
        convert hasSum_ite_eq (J σ') (π'.w σ σ') using 1
        funext y
        simp [Prod.ext_iff, hx]
      · rw [if_neg hx]
        convert (hasSum_zero : HasSum (fun _ : Ω => (0 : ℝ)) 0) using 1
        funext y
        simp [Prod.ext_iff, hx]
    exact (hasSum_sum h).mul_left lam
  have hPcol : ∀ y, HasSum (fun x => P (x, y)) (c y) := by
    intro y
    have h : ∀ σ' ∈ Sg, HasSum
        (fun x => ∑ σ ∈ Sg, if (x, y) = (J σ, J σ') then π'.w σ σ' else 0)
        (if y = J σ' then Y σ' else 0) := by
      intro σ' _
      by_cases hy : y = J σ'
      · rw [if_pos hy]
        apply hasSum_sum
        intro σ _
        convert hasSum_ite_eq (J σ) (π'.w σ σ') using 1
        funext x
        simp [Prod.ext_iff, hy]
      · rw [if_neg hy]
        convert (hasSum_zero : HasSum (fun _ : Ω => (0 : ℝ)) 0) using 1
        funext x
        simp [Prod.ext_iff, hy]
    have h2 := (hasSum_sum h).mul_left lam
    have hfun : (fun x => P (x, y)) = fun x => lam * ∑ σ' ∈ Sg, ∑ σ ∈ Sg,
        if (x, y) = (J σ, J σ') then π'.w σ σ' else 0 := by
      funext x
      change lam * _ = lam * _
      rw [Finset.sum_comm]
    rw [hfun]
    exact h2
  -- the partial marginals are dominated by the countable laws
  have hsingle : ∀ (Z : S → ℝ) (σ₀ : S), σ₀ ∈ Sg →
      (∑ σ ∈ Sg, if J σ₀ = J σ then Z σ else 0) = Z σ₀ := by
    intro Z σ₀ hσ₀
    rw [Finset.sum_eq_single σ₀]
    · simp
    · intro σ _ hne
      rw [if_neg]
      exact fun h => hne (hJ h).symm
    · intro h
      exact absurd hσ₀ h
  have hvanish : ∀ (Z : S → ℝ) (x : Ω), (¬ ∃ σ₀ ∈ Sg, x = J σ₀) →
      (∑ σ ∈ Sg, if x = J σ then Z σ else 0) = 0 := by
    intro Z x hx
    apply Finset.sum_eq_zero
    intro σ hσ
    rw [if_neg]
    exact fun h => hx ⟨σ, hσ, h⟩
  have hr_le : ∀ x, r x ≤ p x := by
    intro x
    by_cases hx : ∃ σ₀ ∈ Sg, x = J σ₀
    · obtain ⟨σ₀, hσ₀, rfl⟩ := hx
      have hX : X σ₀ ≤ μ.w σ₀ := by
        rw [← π'.sum_row σ₀]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => π'.nonneg _ _)
      have hg : good σ₀ := (Finset.mem_filter.mp hσ₀).2
      calc r (J σ₀) = lam * X σ₀ := by simp only [hrdef, hsingle X σ₀ hσ₀]
        _ ≤ cα * μ.w σ₀ := mul_le_mul (min_le_left _ _) hX (hX0 σ₀) hcα
        _ = p (J σ₀) := (hμ σ₀ hg).symm
    · have : r x = 0 := by simp only [hrdef, hvanish X x hx, mul_zero]
      rw [this]
      exact hp0 x
  have hc_le : ∀ y, c y ≤ q y := by
    intro y
    by_cases hy : ∃ σ₀ ∈ Sg, y = J σ₀
    · obtain ⟨σ₀, hσ₀, rfl⟩ := hy
      have hY : Y σ₀ ≤ ν.w σ₀ := by
        rw [← π'.sum_col σ₀]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => π'.nonneg _ _)
      have hg : good σ₀ := (Finset.mem_filter.mp hσ₀).2
      calc c (J σ₀) = lam * Y σ₀ := by simp only [hcdef, hsingle Y σ₀ hσ₀]
        _ ≤ cβ * ν.w σ₀ := mul_le_mul (min_le_right _ _) hY (hY0 σ₀) hcβ
        _ = q (J σ₀) := (hν σ₀ hg).symm
    · have : c y = 0 := by simp only [hcdef, hvanish Y y hy, mul_zero]
      rw [this]
      exact hq0 y
  have hr_sum : HasSum r m := by
    have h := hasSum_sum (s := Sg) (fun σ _ => hasSum_ite_eq (J σ) (X σ))
    exact h.mul_left lam
  have hc_sum : HasSum c m := by
    have h := (hasSum_sum (s := Sg) (fun σ' _ => hasSum_ite_eq (J σ') (Y σ'))).mul_left lam
    have e : lam * ∑ σ' ∈ Sg, Y σ' = m := by
      rw [hm]
      congr 1
      show ∑ σ' ∈ Sg, ∑ σ ∈ Sg, π'.w σ σ' = ∑ σ ∈ Sg, ∑ σ' ∈ Sg, π'.w σ σ'
      exact Finset.sum_comm
    rw [e] at h
    exact h
  have hm_le : m ≤ 1 := hasSum_le hr_le hr_sum hp
  have hpr : HasSum (fun x => p x - r x) (1 - m) := hp.sub hr_sum
  have hqc : HasSum (fun y => q y - c y) (1 - m) := hq.sub hc_sum
  have hpr0 : ∀ x, 0 ≤ p x - r x := fun x => sub_nonneg.mpr (hr_le x)
  have hqc0 : ∀ y, 0 ≤ q y - c y := fun y => sub_nonneg.mpr (hc_le y)
  have h1m : 0 ≤ 1 - m := sub_nonneg.mpr hm_le
  -- the glued coupling
  let Q : Ω × Ω → ℝ := fun z => (p z.1 - r z.1) * (q z.2 - c z.2) / (1 - m)
  have hQ0 : ∀ z, 0 ≤ Q z := fun z => div_nonneg (mul_nonneg (hpr0 _) (hqc0 _)) h1m
  have hrow_fix : ∀ x, r x + (p x - r x) * (1 - m) / (1 - m) = p x := by
    intro x
    by_cases h0 : 1 - m = 0
    · have hz : (fun x => p x - r x) = 0 :=
        (hasSum_zero_iff_of_nonneg hpr0).mp (h0 ▸ hpr)
      have hx := congrFun hz x
      simp only [Pi.zero_apply] at hx
      rw [h0]
      simp only [mul_zero, div_zero, add_zero]
      linarith
    · rw [mul_div_assoc, div_self h0, mul_one]
      ring
  have hcol_fix : ∀ y, c y + (1 - m) * (q y - c y) / (1 - m) = q y := by
    intro y
    by_cases h0 : 1 - m = 0
    · have hz : (fun y => q y - c y) = 0 :=
        (hasSum_zero_iff_of_nonneg hqc0).mp (h0 ▸ hqc)
      have hy := congrFun hz y
      simp only [Pi.zero_apply] at hy
      rw [h0]
      simp only [zero_mul, div_zero, add_zero]
      linarith
    · rw [mul_comm, mul_div_assoc, div_self h0, mul_one]
      ring
  let π : CCoupling p q :=
    { w := fun z => P z + Q z
      nonneg := fun z => add_nonneg (hP0 z) (hQ0 z)
      row := by
        intro x
        have h2 : HasSum (fun y => (p x - r x) * (q y - c y) / (1 - m))
            ((p x - r x) * (1 - m) / (1 - m)) := (hqc.mul_left (p x - r x)).div_const (1 - m)
        have h := (hProw x).add h2
        rw [hrow_fix x] at h
        exact h
      col := by
        intro y
        have h2 : HasSum (fun x => (p x - r x) * (q y - c y) / (1 - m))
            ((1 - m) * (q y - c y) / (1 - m)) := (hpr.mul_right (q y - c y)).div_const (1 - m)
        have h := (hPcol y).add h2
        rw [hcol_fix y] at h
        exact h }
  -- the cost of the finitely supported part
  have hPcost : HasSum (fun z => P z * d z.1 z.2)
      (lam * ∑ σ ∈ Sg, ∑ σ' ∈ Sg, π'.w σ σ' * dS σ σ') := by
    have h := hasSum_sum (s := Sg) (fun σ _ => hasSum_sum (s := Sg) (fun σ' _ =>
      hasSum_ite_eq ((J σ, J σ') : Ω × Ω) (π'.w σ σ' * dS σ σ')))
    have hfun : (fun z => P z * d z.1 z.2) = fun z => lam * ∑ σ ∈ Sg, ∑ σ' ∈ Sg,
        if z = (J σ, J σ') then π'.w σ σ' * dS σ σ' else 0 := by
      funext z
      change (lam * _) * _ = _
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ' _
      split_ifs with hz
      · subst hz
        rw [hdS]
      · exact zero_mul _
    rw [hfun]
    exact h.mul_left lam
  -- the cost of the product part
  have hQsum : HasSum Q ((1 - m) * (1 - m) / (1 - m)) :=
    (hpr.mul hqc (Summable.mul_of_nonneg hpr.summable hqc.summable hpr0 hqc0)).div_const _
  have hQd : Summable (fun z => Q z * d z.1 z.2) :=
    Summable.of_nonneg_of_le (fun z => mul_nonneg (hQ0 z) (hd0 _ _))
      (fun z => mul_le_mul_of_nonneg_left (hdD _ _) (hQ0 z)) (hQsum.summable.mul_right D)
  have hQd_le : ∑' z, Q z * d z.1 z.2 ≤ (1 - m) * D := by
    calc ∑' z, Q z * d z.1 z.2 ≤ ∑' z, Q z * D :=
          Summable.tsum_le_tsum (fun z => mul_le_mul_of_nonneg_left (hdD _ _) (hQ0 z)) hQd
            (hQsum.summable.mul_right D)
      _ = (1 - m) * (1 - m) / (1 - m) * D := (hQsum.mul_right D).tsum_eq
      _ ≤ (1 - m) * D := by
          apply mul_le_mul_of_nonneg_right _ hD
          rw [mul_div_assoc]
          exact mul_le_of_le_one_right h1m (div_self_le_one _)
  refine ⟨π, lam * (∑ σ ∈ Sg, ∑ σ' ∈ Sg, π'.w σ σ' * dS σ σ') + ∑' z, Q z * d z.1 z.2, ?_, ?_⟩
  · have h := hPcost.add hQd.hasSum
    convert h using 1
    funext z
    change (P z + Q z) * d z.1 z.2 = _
    ring
  · -- restricted cost and the lower bound on the glued mass
    have hA : (∑ σ ∈ Sg, ∑ σ' ∈ Sg, π'.w σ σ' * dS σ σ') ≤ π'.cost dS := by
      unfold Coupling.cost
      calc (∑ σ ∈ Sg, ∑ σ' ∈ Sg, π'.w σ σ' * dS σ σ')
          ≤ ∑ σ ∈ Sg, ∑ σ', π'.w σ σ' * dS σ σ' :=
            Finset.sum_le_sum fun σ _ => Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.subset_univ _) (fun σ' _ _ => mul_nonneg (π'.nonneg _ _) (hdS0 _ _))
        _ ≤ ∑ σ, ∑ σ', π'.w σ σ' * dS σ σ' :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun σ _ _ => Finset.sum_nonneg fun σ' _ => mul_nonneg (π'.nonneg _ _) (hdS0 _ _))
    have hmass : 1 - ∑ σ ∈ Sb, μ.w σ - ∑ σ ∈ Sb, ν.w σ ≤ ∑ σ ∈ Sg, X σ := by
      have htot : ∑ σ, μ.w σ = 1 := μ.sum_one
      have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ good (fun σ => μ.w σ)
      have hgood : ∑ σ ∈ Sg, μ.w σ = ∑ σ ∈ Sg, X σ + ∑ σ ∈ Sg, ∑ σ' ∈ Sb, π'.w σ σ' := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro σ _
        rw [← π'.sum_row σ]
        exact (Finset.sum_filter_add_sum_filter_not Finset.univ good (fun σ' => π'.w σ σ')).symm
      have hcross : ∑ σ ∈ Sg, ∑ σ' ∈ Sb, π'.w σ σ' ≤ ∑ σ' ∈ Sb, ν.w σ' := by
        rw [Finset.sum_comm]
        apply Finset.sum_le_sum
        intro σ' _
        rw [← π'.sum_col σ']
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => π'.nonneg _ _)
      have : ∑ σ ∈ Sg, μ.w σ + ∑ σ ∈ Sb, μ.w σ = 1 := hsplit.trans htot
      linarith
    have hm_ge : lam * (1 - ∑ σ ∈ Sb, μ.w σ - ∑ σ ∈ Sb, ν.w σ) ≤ m :=
      mul_le_mul_of_nonneg_left hmass hlam0
    have h1 : lam * (∑ σ ∈ Sg, ∑ σ' ∈ Sg, π'.w σ σ' * dS σ σ') ≤ lam * π'.cost dS :=
      mul_le_mul_of_nonneg_left hA hlam0
    have h2 : (1 - m) * D ≤ D * (1 - lam * (1 - ∑ σ ∈ Sb, μ.w σ - ∑ σ ∈ Sb, ν.w σ)) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (by linarith) hD
    linarith

end Transfer
end Abstract

/-- Products of nonnegative countable sums (a fast generic wrapper). -/
lemma hasSum_mul_nonneg {α β : Type*} {f : α → ℝ} {g : β → ℝ} {s t : ℝ}
    (hf : HasSum f s) (hg : HasSum g t) (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ b, 0 ≤ g b) :
    HasSum (fun x : α × β => f x.1 * g x.2) (s * t) :=
  hf.mul hg (Summable.mul_of_nonneg hf.summable hg.summable (fun a => hf0 a) (fun b => hg0 b))

/-! ## Lumping the slots `≥ N` -/

section Lump
variable (κ : SlotWeights) (N : ℕ)

/-- The tail mass `∑_{r ≥ N} κ_r`. -/
def tail : ℝ := ∑' k, κ.weight (k + N)

lemma tail_hasSum : HasSum (fun k => κ.weight (k + N)) (tail κ N) :=
  ((summable_nat_add_iff N).mpr κ.summable).hasSum

lemma tail_nonneg : 0 ≤ tail κ N := tsum_nonneg fun _ => κ.nonneg _

lemma tail_tendsto : Tendsto (tail κ) atTop (𝓝 0) := tendsto_sum_nat_add κ.weight

/-- The lumping map `r ↦ min r N`. -/
def lumpIdx (r : ℕ) : Fin (N + 1) := ⟨min r N, by omega⟩

/-- The lumped slot law on `Fin (N+1)`: slots `< N` are unchanged, and slot
`N` carries the whole tail. -/
def lump (i : Fin (N + 1)) : ℝ := if (i : ℕ) < N then κ.weight i else tail κ N

lemma lump_nonneg (i : Fin (N + 1)) : 0 ≤ lump κ N i := by
  unfold lump
  split_ifs
  · exact κ.nonneg _
  · exact tail_nonneg κ N

lemma lump_of_lt (i : Fin (N + 1)) (h : (i : ℕ) < N) : lump κ N i = κ.weight i := if_pos h

lemma lump_last : lump κ N (Fin.last N) = tail κ N := by
  unfold lump
  rw [if_neg (by simp)]

/-- The lumped law is the push-forward of `κ` under the lumping map. -/
lemma lump_fibre (i : Fin (N + 1)) :
    HasSum (fun r : ℕ => if lumpIdx N r = i then κ.weight r else 0) (lump κ N i) := by
  by_cases hi : (i : ℕ) < N
  · rw [lump_of_lt κ N i hi]
    have hfun : (fun r : ℕ => if lumpIdx N r = i then κ.weight r else 0) =
        fun r => if r = (i : ℕ) then κ.weight i else 0 := by
      funext r
      have hiff : lumpIdx N r = i ↔ r = (i : ℕ) := by
        simp only [lumpIdx, Fin.ext_iff]
        omega
      by_cases hr : r = (i : ℕ)
      · rw [if_pos (hiff.mpr hr), if_pos hr, hr]
      · rw [if_neg (fun h => hr (hiff.mp h)), if_neg hr]
    rw [hfun]
    exact hasSum_ite_eq (i : ℕ) (κ.weight i)
  · have hiN : (i : ℕ) = N := by omega
    rw [lump, if_neg hi]
    rw [← hasSum_nat_add_iff' N]
    have hz : ∑ j ∈ Finset.range N, (if lumpIdx N j = i then κ.weight j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [if_neg]
      intro h
      have := congrArg Fin.val h
      simp only [lumpIdx, Finset.mem_range] at this hj
      omega
    rw [hz, sub_zero]
    have hfun : (fun k : ℕ => if lumpIdx N (k + N) = i then κ.weight (k + N) else 0) =
        fun k => κ.weight (k + N) := by
      funext k
      rw [if_pos]
      apply Fin.ext
      simp only [lumpIdx]
      omega
    rw [hfun]
    exact tail_hasSum κ N

lemma lump_sum : ∑ i, lump κ N i = 1 := by
  rw [Fin.sum_univ_castSucc, lump_last]
  have h1 : (∑ i : Fin N, lump κ N i.castSucc) = ∑ i ∈ Finset.range N, κ.weight i := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    exact lump_of_lt κ N _ (by simp)
  rw [h1, tail, κ.summable.sum_add_tsum_nat_add N, κ.tsum_eq_one]

lemma lump_le_one (i : Fin (N + 1)) : lump κ N i ≤ 1 := by
  rw [← lump_sum κ N]
  exact Finset.single_le_sum (fun j _ => lump_nonneg κ N j) (Finset.mem_univ i)

end Lump

/-! ## The lumped finite endpoint-label system -/

section Model
variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
variable [DecidableEq V] [DecidableEq E] [DecidableEq C]
variable (M : SlotModel V E C) (F : Finset E) (N : ℕ)

/-- Finite lumped states `(c, r, s)` with `r, s ≤ N`. -/
abbrev FState (C : Type*) (N : ℕ) := C × Fin (N + 1) × Fin (N + 1)
/-- Finite lumped labels. -/
abbrev FLabel (C : Type*) (N : ℕ) := C × Fin (N + 1)

/-- The inclusion of lumped states into countable states. -/
def jS (a : FState C N) : C × ℕ × ℕ := (a.1, (a.2.1 : ℕ), (a.2.2 : ℕ))
/-- The inclusion of lumped labels into countable labels. -/
def jL (l : FLabel C N) : C × ℕ := (l.1, (l.2 : ℕ))

lemma jS_injective : Function.Injective (jS (C := C) N) := by
  rintro ⟨c, r, s⟩ ⟨c', r', s'⟩ h
  simp only [jS, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  subst h1
  rw [Fin.ext h2, Fin.ext h3]

lemma jL_injective : Function.Injective (jL (C := C) N) := by
  rintro ⟨c, r⟩ ⟨c', r'⟩ h
  simp only [jL, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  subst h1
  rw [Fin.ext h2]

/-- The configuration map. -/
def JS (σ : F → FState C N) : F → C × ℕ × ℕ := fun e => jS N (σ e)

lemma JS_injective : Function.Injective (JS (C := C) F N) := by
  intro σ τ h
  funext e
  exact jS_injective N (congrFun h e)

/-- The finite system obtained by lumping all slots `≥ N` of `M` into slot
`N`, on the current free-edge set `F`. -/
def fsys : FiniteSystem V F (FState C N) (FLabel C N) where
  endpoints e := M.geom.endpoints e.1
  endpoints_card e := M.geom.endpoints_card e.1
  linear e f v w hve hvf hwe hwf hne :=
    Subtype.ext (M.geom.linear e.1 f.1 v w hve hvf hwe hwf hne)
  label e y a := if y = M.geom.endpoint e.1 0 then (a.1, a.2.1) else (a.1, a.2.2)
  activity e a := M.x ^ M.exponent e.1 a.1 * lump M.κ N a.2.1 * lump M.κ N a.2.2
  activity_nonneg _ _ := mul_nonneg (mul_nonneg (pow_nonneg M.x_nonneg _)
    (lump_nonneg _ _ _)) (lump_nonneg _ _ _)

lemma jL_label (e : F) (y : V) (a : FState C N) :
    jL N ((fsys M F N).label e y a) = M.label e.1 y (jS N a) := by
  simp only [fsys, SlotModel.label, jL, jS]
  split_ifs <;> rfl

/-- The occupied labels of the lumped system. -/
def finB (B : SlotModel.Boundary V C) : FiniteSystem.Boundary V (FLabel C N) :=
  fun y => Finset.univ.filter fun l => jL N l ∈ B y

lemma mem_finB (B : SlotModel.Boundary V C) (y : V) (l : FLabel C N) :
    l ∈ finB N B y ↔ jL N l ∈ B y := by
  simp [finB]

lemma compatible_iff (B : SlotModel.Boundary V C) (e : F) (a : FState C N) :
    (fsys M F N).Compatible (finB N B) e a ↔ M.Compat B e.1 (jS N a) := by
  unfold FiniteSystem.Compatible SlotModel.Compat
  simp only [mem_finB, jL_label]
  rfl

lemma admissible_iff (B : SlotModel.Boundary V C) (σ : F → FState C N) :
    (fsys M F N).Admissible (finB N B) σ ↔ M.Admissible F B (JS F N σ) := by
  unfold FiniteSystem.Admissible SlotModel.Admissible FiniteSystem.PairwiseLabels
  simp only [compatible_iff]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro e
  apply forall_congr'
  intro f
  apply imp_congr Iff.rfl
  apply forall_congr'
  intro y
  apply imp_congr Iff.rfl
  apply imp_congr Iff.rfl
  rw [← (jL_injective (C := C) N).ne_iff, jL_label, jL_label]
  rfl

/-- The configurations using only slots `< N`. -/
def Good (σ : F → FState C N) : Prop := ∀ e, ((σ e).2.1 : ℕ) < N ∧ ((σ e).2.2 : ℕ) < N

/-- The countable configurations using only slots `< N`. -/
def GoodC (ω : F → C × ℕ × ℕ) : Prop := ∀ e, (ω e).2.1 < N ∧ (ω e).2.2 < N

lemma goodC_JS (σ : F → FState C N) : GoodC F N (JS F N σ) ↔ Good F N σ := Iff.rfl

lemma goodC_mem_range (ω : F → C × ℕ × ℕ) (hω : GoodC F N ω) :
    ∃ σ : F → FState C N, JS F N σ = ω ∧ Good F N σ := by
  refine ⟨fun e => ((ω e).1, ⟨(ω e).2.1, by have := (hω e).1; omega⟩,
    ⟨(ω e).2.2, by have := (hω e).2; omega⟩), ?_, fun e => hω e⟩
  funext e
  rfl

lemma activity_eq (e : F) (a : FState C N) (ha : ((a.2.1 : ℕ) < N ∧ (a.2.2 : ℕ) < N)) :
    (fsys M F N).activity e a = M.act e.1 (jS N a) := by
  change M.x ^ M.exponent e.1 a.1 * lump M.κ N a.2.1 * lump M.κ N a.2.2 = _
  rw [lump_of_lt _ _ _ ha.1, lump_of_lt _ _ _ ha.2]
  rfl

lemma cw_eq (B : SlotModel.Boundary V C) (σ : F → FState C N) (hσ : Good F N σ) :
    (fsys M F N).configurationWeight (finB N B) σ = M.weight F B (JS F N σ) := by
  unfold FiniteSystem.configurationWeight SlotModel.weight
  by_cases h : (fsys M F N).Admissible (finB N B) σ
  · rw [if_pos h, if_pos ((admissible_iff M F N B σ).mp h)]
    apply Finset.prod_congr rfl
    intro e _
    exact activity_eq M F N e (σ e) (hσ e)
  · rw [if_neg h, if_neg (fun h' => h ((admissible_iff M F N B σ).mpr h'))]

end Model

/-! ## Good and bad parts of the partition sums -/

section Split
variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
variable [DecidableEq V] [DecidableEq E] [DecidableEq C]
variable (M : SlotModel V E C) (F : Finset E) (N : ℕ) (B : SlotModel.Boundary V C)

/-- Lumped weight of configurations using only slots `< N`. -/
def Afin : ℝ := ∑ σ : F → FState C N,
  if Good F N σ then (fsys M F N).configurationWeight (finB N B) σ else 0

/-- Lumped weight of configurations using the lumped slot `N`. -/
def Dfin : ℝ := ∑ σ : F → FState C N,
  if Good F N σ then 0 else (fsys M F N).configurationWeight (finB N B) σ

/-- Countable weight of configurations using some slot `≥ N`. -/
def Dc : ℝ := ∑' ω : F → C × ℕ × ℕ, if GoodC F N ω then 0 else M.weight F B ω

lemma fpartition_split :
    (fsys M F N).partition (finB N B) = Afin M F N B + Dfin M F N B := by
  unfold FiniteSystem.partition Afin Dfin
  rw [← Finset.sum_add_distrib]
  congr 1
  · ext
    simp
  · funext σ
    split_ifs <;> simp

lemma hasSum_good :
    HasSum (fun ω => if GoodC F N ω then M.weight F B ω else 0) (Afin M F N B) := by
  have hv : ∀ ω ∉ Set.range (JS (C := C) F N),
      (if GoodC F N ω then M.weight F B ω else 0) = 0 := by
    intro ω hω
    rw [if_neg]
    intro hg
    obtain ⟨σ, hσ, _⟩ := goodC_mem_range F N ω hg
    exact hω ⟨σ, hσ⟩
  rw [← (JS_injective (C := C) F N).hasSum_iff hv]
  have hfun : ((fun ω => if GoodC F N ω then M.weight F B ω else 0) ∘ JS F N) =
      fun σ => if Good F N σ then (fsys M F N).configurationWeight (finB N B) σ else 0 := by
    funext σ
    simp only [Function.comp, goodC_JS]
    split_ifs with h
    · exact (cw_eq M F N B σ h).symm
    · rfl
  rw [hfun]
  exact hasSum_fintype _

lemma partition_split : M.partition F B = Afin M F N B + Dc M F N B := by
  have hs := M.weight_summable F B
  have h2 : Summable (fun ω => if GoodC F N ω then 0 else M.weight F B ω) :=
    Summable.of_nonneg_of_le
      (fun ω => by split_ifs; exacts [le_rfl, M.weight_nonneg F B ω])
      (fun ω => by split_ifs; exacts [M.weight_nonneg F B ω, le_rfl]) hs
  have h := (hasSum_good M F N B).add h2.hasSum
  have hfun : M.weight F B = fun ω => (if GoodC F N ω then M.weight F B ω else 0) +
      (if GoodC F N ω then 0 else M.weight F B ω) := by
    funext ω
    split_ifs <;> simp
  have h' : HasSum (M.weight F B) (Afin M F N B + Dc M F N B) := by
    rw [hfun]
    exact h
  exact h'.tsum_eq

/-- The countable weight of slots `≥ N` tends to zero (dominated convergence). -/
lemma Dc_tendsto : Tendsto (fun N => Dc M F N B) atTop (𝓝 0) := by
  have h := tendsto_tsum_dominated (𝓕 := atTop)
    (f := fun N ω => if GoodC F N ω then (0 : ℝ) else M.weight F B ω)
    (g := fun _ => (0 : ℝ)) (bound := M.weight F B) (M.weight_summable F B) ?_ ?_
  · simpa [Dc] using h
  · intro ω
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop
      ((Finset.univ.sup fun e => max (ω e).2.1 (ω e).2.2) + 1)] with N hN
    rw [if_pos]
    intro e
    have h1 := Finset.le_sup (f := fun e => max (ω e).2.1 (ω e).2.2) (Finset.mem_univ e)
    have h2 := le_max_left (ω e).2.1 (ω e).2.2
    have h3 := le_max_right (ω e).2.1 (ω e).2.2
    constructor <;> omega
  · exact Eventually.of_forall fun N ω => by
      have h0 : 0 ≤ (if GoodC F N ω then (0 : ℝ) else M.weight F B ω) := by
        split_ifs; exacts [le_rfl, M.weight_nonneg F B ω]
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      split_ifs; exacts [M.weight_nonneg F B ω, le_rfl]

omit [DecidableEq V] [DecidableEq E] [DecidableEq C] in
/-- Finite sums over lumped states of product functions. -/
lemma sum_state (g : C → ℝ) (u v : Fin (N + 1) → ℝ) :
    ∑ a : FState C N, g a.1 * u a.2.1 * v a.2.2 = ∑ c, g c * ((∑ i, u i) * (∑ k, v k)) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma fsys_total (f : F) : ∑ a, (fsys M F N).activity f a = ∑ c, M.x ^ M.exponent f.1 c := by
  have h := sum_state N (fun c => M.x ^ M.exponent f.1 c) (lump M.κ N) (lump M.κ N)
  rw [lump_sum, mul_one] at h
  change ∑ a : FState C N, M.x ^ M.exponent f.1 a.1 * lump M.κ N a.2.1 * lump M.κ N a.2.2 = _
  simpa only [mul_one] using h

lemma fsys_total_le (f : F) : ∑ a, (fsys M F N).activity f a ≤ Fintype.card C := by
  rw [fsys_total]
  calc (∑ c, M.x ^ M.exponent f.1 c) ≤ ∑ _c : C, (1 : ℝ) :=
        Finset.sum_le_sum fun _ _ => pow_le_one₀ M.x_nonneg M.x_le_one
    _ = Fintype.card C := by simp

/-- A lumped state is bad when it uses the lumped slot. -/
def BadState (a : FState C N) : Prop := ¬ (((a.2.1 : ℕ) < N) ∧ ((a.2.2 : ℕ) < N))

lemma fsys_bad_le (f : F) :
    ∑ a, (if BadState N a then (fsys M F N).activity f a else 0) ≤
      tail M.κ N * (2 * Fintype.card C) := by
  have hpt : ∀ a : FState C N, (if BadState N a then (fsys M F N).activity f a else 0) ≤
      M.x ^ M.exponent f.1 a.1 * (if a.2.1 = Fin.last N then lump M.κ N a.2.1 else 0) *
          lump M.κ N a.2.2 +
        M.x ^ M.exponent f.1 a.1 * lump M.κ N a.2.1 *
          (if a.2.2 = Fin.last N then lump M.κ N a.2.2 else 0) := by
    intro a
    have hx := pow_nonneg M.x_nonneg (M.exponent f.1 a.1)
    have hl1 := lump_nonneg M.κ N a.2.1
    have hl2 := lump_nonneg M.κ N a.2.2
    change (if BadState N a then M.x ^ M.exponent f.1 a.1 * lump M.κ N a.2.1 *
      lump M.κ N a.2.2 else 0) ≤ _
    by_cases hb : BadState N a
    · rw [if_pos hb]
      unfold BadState at hb
      have h1 := a.2.1.isLt
      have h2 := a.2.2.isLt
      by_cases h : (a.2.1 : ℕ) < N
      · have hk : a.2.2 = Fin.last N := by
          apply Fin.ext
          simp only [Fin.val_last]
          omega
        rw [if_pos hk]
        by_cases hi : a.2.1 = Fin.last N
        · rw [if_pos hi]
          nlinarith [mul_nonneg (mul_nonneg hx hl1) hl2]
        · rw [if_neg hi]
          nlinarith [mul_nonneg (mul_nonneg hx hl1) hl2]
      · have hi : a.2.1 = Fin.last N := by
          apply Fin.ext
          simp only [Fin.val_last]
          omega
        rw [if_pos hi]
        have hr : 0 ≤ M.x ^ M.exponent f.1 a.1 * lump M.κ N a.2.1 *
            (if a.2.2 = Fin.last N then lump M.κ N a.2.2 else 0) := by
          split_ifs
          · positivity
          · simp
        linarith
    · rw [if_neg hb]
      have h1 : 0 ≤ M.x ^ M.exponent f.1 a.1 *
          (if a.2.1 = Fin.last N then lump M.κ N a.2.1 else 0) * lump M.κ N a.2.2 := by
        split_ifs
        · positivity
        · simp
      have h2 : 0 ≤ M.x ^ M.exponent f.1 a.1 * lump M.κ N a.2.1 *
          (if a.2.2 = Fin.last N then lump M.κ N a.2.2 else 0) := by
        split_ifs
        · positivity
        · simp
      linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hpt a)
  rw [Finset.sum_add_distrib, sum_state N (fun c => M.x ^ M.exponent f.1 c)
      (fun i => if i = Fin.last N then lump M.κ N i else 0) (lump M.κ N),
    sum_state N (fun c => M.x ^ M.exponent f.1 c) (lump M.κ N)
      (fun i => if i = Fin.last N then lump M.κ N i else 0)] at hsum
  have hlast : ∑ i, (if i = Fin.last N then lump M.κ N i else 0) = tail M.κ N := by
    rw [Finset.sum_ite_eq' Finset.univ (Fin.last N), if_pos (Finset.mem_univ _), lump_last]
  rw [hlast, lump_sum] at hsum
  have hq : ∑ c, M.x ^ M.exponent f.1 c ≤ Fintype.card C := by
    rw [← fsys_total M F N f]
    exact fsys_total_le M F N f
  have ht := tail_nonneg M.κ N
  calc _ ≤ _ := hsum
    _ = tail M.κ N * (2 * ∑ c, M.x ^ M.exponent f.1 c) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        ring
    _ ≤ tail M.κ N * (2 * Fintype.card C) := by
        apply mul_le_mul_of_nonneg_left _ ht
        linarith

/-- The constant in the bound of the lumped bad weight. -/
def badConst (F : Finset E) (C : Type*) [Fintype C] : ℝ :=
  ∑ e : F, ∏ f : F, (if f = e then 2 * (Fintype.card C : ℝ) else Fintype.card C)

lemma Dfin_nonneg : 0 ≤ Dfin M F N B :=
  Finset.sum_nonneg fun σ _ => by
    split_ifs
    · exact le_rfl
    · exact (fsys M F N).configurationWeight_nonneg _ _

lemma Dfin_le : Dfin M F N B ≤ tail M.κ N * badConst F C := by
  set I := fsys M F N with hI
  let g : F → F → FState C N → ℝ := fun e f a =>
    if f = e then (if BadState N a then I.activity f a else 0) else I.activity f a
  have hstep1 : ∀ σ : F → FState C N,
      (if Good F N σ then 0 else I.configurationWeight (finB N B) σ) ≤
        ∑ e : F, ∏ f : F, g e f (σ f) := by
    intro σ
    have hterm : ∀ e : F, ∏ f : F, g e f (σ f) =
        if BadState N (σ e) then ∏ f : F, I.activity f (σ f) else 0 := by
      intro e
      by_cases hb : BadState N (σ e)
      · rw [if_pos hb]
        apply Finset.prod_congr rfl
        intro f _
        simp only [g]
        split_ifs with hfe hb'
        · rfl
        · subst hfe
          exact absurd hb hb'
        · rfl
      · rw [if_neg hb]
        apply Finset.prod_eq_zero (Finset.mem_univ e)
        simp only [g, if_true, if_neg hb]
    simp only [hterm]
    by_cases hg : Good F N σ
    · rw [if_pos hg]
      exact Finset.sum_nonneg fun e _ => by
        split_ifs
        · exact Finset.prod_nonneg fun f _ => I.activity_nonneg _ _
        · exact le_rfl
    · rw [if_neg hg]
      unfold Good at hg
      push Not at hg
      obtain ⟨e₀, he₀⟩ := hg
      have hb : BadState N (σ e₀) := by
        unfold BadState
        intro h
        exact absurd (he₀ h.1) (not_le.mpr h.2)
      have hcw : I.configurationWeight (finB N B) σ ≤ ∏ f : F, I.activity f (σ f) := by
        unfold FiniteSystem.configurationWeight
        split_ifs
        · exact le_rfl
        · exact Finset.prod_nonneg fun f _ => I.activity_nonneg _ _
      have hs := Finset.single_le_sum (s := Finset.univ)
        (f := fun e => if BadState N (σ e) then ∏ f : F, I.activity f (σ f) else 0)
        (fun e _ => by
          split_ifs
          · exact Finset.prod_nonneg fun f _ => I.activity_nonneg _ _
          · exact le_rfl) (Finset.mem_univ e₀)
      simp only [if_pos hb] at hs
      exact hcw.trans hs
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun σ _ => hstep1 σ)
  have hswap : (∑ σ : F → FState C N, ∑ e : F, ∏ f : F, g e f (σ f)) =
      ∑ e : F, ∏ f : F, ∑ a, g e f a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    exact (Fintype.prod_sum (fun f a => g e f a)).symm
  rw [hswap] at hsum
  have hfactor : ∀ e : F, ∏ f : F, ∑ a, g e f a ≤
      tail M.κ N * ∏ f : F, (if f = e then 2 * (Fintype.card C : ℝ) else Fintype.card C) := by
    intro e
    have hle : ∏ f : F, ∑ a, g e f a ≤
        ∏ f : F, (if f = e then tail M.κ N * (2 * (Fintype.card C : ℝ))
          else Fintype.card C) := by
      apply Finset.prod_le_prod
      · intro f _
        apply Finset.sum_nonneg
        intro a _
        simp only [g]
        split_ifs
        · exact I.activity_nonneg _ _
        · exact le_rfl
        · exact I.activity_nonneg _ _
      · intro f _
        by_cases hfe : f = e
        · rw [if_pos hfe]
          have := fsys_bad_le M F N f
          simpa only [g, if_pos hfe] using this
        · rw [if_neg hfe]
          simpa only [g, if_neg hfe] using fsys_total_le M F N f
    have hsplit : ∏ f : F, (if f = e then tail M.κ N * (2 * (Fintype.card C : ℝ))
        else Fintype.card C) = tail M.κ N *
          ∏ f : F, (if f = e then 2 * (Fintype.card C : ℝ) else Fintype.card C) := by
      have hpt : ∀ f : F, (if f = e then tail M.κ N * (2 * (Fintype.card C : ℝ))
          else Fintype.card C) = (if f = e then tail M.κ N else 1) *
            (if f = e then 2 * (Fintype.card C : ℝ) else Fintype.card C) := by
        intro f
        split_ifs <;> ring
      simp only [hpt]
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ e,
        if_pos (Finset.mem_univ _)]
    rw [← hsplit]
    exact hle
  have htot := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hfactor e)
  rw [← Finset.mul_sum] at htot
  exact hsum.trans htot

lemma Dfin_tendsto : Tendsto (fun N => Dfin M F N B) atTop (𝓝 0) := by
  have h := (tail_tendsto M.κ).mul_const (badConst F C)
  rw [zero_mul] at h
  exact squeeze_zero (fun N => Dfin_nonneg M F N B) (fun N => Dfin_le M F N B) h

end Split

/-! ## The lumped system satisfies the three bounds exactly -/

section BoundsTransfer
variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
variable [DecidableEq V] [DecidableEq E] [DecidableEq C]
variable (M : SlotModel V E C) (F : Finset E) (N : ℕ)

/-- All occupied labels use slots `< N`. -/
def Small (B : SlotModel.Boundary V C) (N : ℕ) : Prop := ∀ y, ∀ l ∈ B y, l.2 < N

lemma card_finB {B : SlotModel.Boundary V C} (hs : Small B N) (y : V) :
    (finB N B y).card = (B y).card := by
  have himage : (finB N B y).image (jL N) = B y := by
    ext l
    simp only [Finset.mem_image, mem_finB]
    constructor
    · rintro ⟨l', hl', rfl⟩
      exact hl'
    · intro hl
      refine ⟨(l.1, ⟨l.2, by have := hs y l hl; omega⟩), ?_, ?_⟩
      · simpa [jL] using hl
      · simp [jL]
  rw [← himage, Finset.card_image_of_injective _ (jL_injective N)]

lemma incident_card (y : V) : ((fsys M F N).incident y).card = M.freeDegree F y := by
  unfold FiniteSystem.incident SlotModel.freeDegree
  apply Finset.card_bij (fun e _ => e.1)
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact ⟨e.2, he⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro b hb
    simp only [Finset.mem_filter] at hb
    refine ⟨⟨b, hb.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hb.2

lemma edgeDegree_eq (e : F) : (fsys M F N).edgeDegree e = M.adjDegree F e.1 := by
  unfold FiniteSystem.edgeDegree FiniteSystem.neighbours SlotModel.adjDegree
  apply Finset.card_bij (fun f _ => f.1)
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    simp only [Finset.mem_filter, Finset.mem_erase]
    exact ⟨⟨fun h => hf.1 (Subtype.ext h), f.2⟩, hf.2⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_erase] at hb
    refine ⟨⟨b, hb.1.2⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => hb.1.1 (congrArg Subtype.val h), hb.2⟩

lemma fibreBound : (fsys M F N).FibreBound := by
  intro e v _ l
  have hq : ∀ (g : C → ℝ) (u : Fin (N + 1) → ℝ),
      (∑ c, (if c = l.1 then g l.1 else 0) * ((∑ i, (if i = l.2 then u i else 0)) *
        (∑ k, lump M.κ N k))) = g l.1 * u l.2 := by
    intro g u
    rw [lump_sum, mul_one, Finset.sum_ite_eq' Finset.univ l.2, if_pos (Finset.mem_univ _),
      ← Finset.sum_mul, Finset.sum_ite_eq' Finset.univ l.1, if_pos (Finset.mem_univ _)]
  have hq' : ∀ (g : C → ℝ) (u : Fin (N + 1) → ℝ),
      (∑ c, (if c = l.1 then g l.1 else 0) * ((∑ k, lump M.κ N k) *
        (∑ i, (if i = l.2 then u i else 0)))) = g l.1 * u l.2 := by
    intro g u
    simp only [mul_comm (∑ k, lump M.κ N k)]
    exact hq g u
  have hx : M.x ^ M.exponent e.1 l.1 * lump M.κ N l.2 ≤ 1 :=
    mul_le_one₀ (pow_le_one₀ M.x_nonneg M.x_le_one) (lump_nonneg _ _ _) (lump_le_one _ _ _)
  by_cases hv : v = M.geom.endpoint e.1 0
  · calc _ = ∑ a : FState C N, (if a.1 = l.1 then M.x ^ M.exponent e.1 l.1 else 0) *
          (if a.2.1 = l.2 then lump M.κ N a.2.1 else 0) * lump M.κ N a.2.2 := by
          apply Finset.sum_congr rfl
          intro a _
          have hlabel : (fsys M F N).label e v a = (a.1, a.2.1) := by
            show (if v = M.geom.endpoint e.1 0 then (a.1, a.2.1) else (a.1, a.2.2)) = _
            rw [if_pos hv]
          have hact : (fsys M F N).activity e a =
              M.x ^ M.exponent e.1 a.1 * lump M.κ N a.2.1 * lump M.κ N a.2.2 := rfl
          rw [hlabel, hact]
          by_cases h1 : a.1 = l.1
          · by_cases h2 : a.2.1 = l.2
            · rw [if_pos (Prod.ext h1 h2), if_pos h1, if_pos h2, h1]
            · rw [if_neg (fun h => h2 (congrArg Prod.snd h)), if_neg h2]
              simp
          · rw [if_neg (fun h => h1 (congrArg Prod.fst h)), if_neg h1]
            simp
      _ = M.x ^ M.exponent e.1 l.1 * lump M.κ N l.2 := by
          rw [sum_state N (fun c => if c = l.1 then M.x ^ M.exponent e.1 l.1 else 0)
            (fun i => if i = l.2 then lump M.κ N i else 0) (lump M.κ N)]
          exact hq (fun c => M.x ^ M.exponent e.1 c) (lump M.κ N)
      _ ≤ 1 := hx
  · calc _ = ∑ a : FState C N, (if a.1 = l.1 then M.x ^ M.exponent e.1 l.1 else 0) *
          lump M.κ N a.2.1 * (if a.2.2 = l.2 then lump M.κ N a.2.2 else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          have hlabel : (fsys M F N).label e v a = (a.1, a.2.2) := by
            show (if v = M.geom.endpoint e.1 0 then (a.1, a.2.1) else (a.1, a.2.2)) = _
            rw [if_neg hv]
          have hact : (fsys M F N).activity e a =
              M.x ^ M.exponent e.1 a.1 * lump M.κ N a.2.1 * lump M.κ N a.2.2 := rfl
          rw [hlabel, hact]
          by_cases h1 : a.1 = l.1
          · by_cases h2 : a.2.2 = l.2
            · rw [if_pos (Prod.ext h1 h2), if_pos h1, if_pos h2, h1]
            · rw [if_neg (fun h => h2 (congrArg Prod.snd h)), if_neg h2]
              simp
          · rw [if_neg (fun h => h1 (congrArg Prod.fst h)), if_neg h1]
            simp
      _ = M.x ^ M.exponent e.1 l.1 * lump M.κ N l.2 := by
          rw [sum_state N (fun c => if c = l.1 then M.x ^ M.exponent e.1 l.1 else 0)
            (lump M.κ N) (fun i => if i = l.2 then lump M.κ N i else 0)]
          exact hq' (fun c => M.x ^ M.exponent e.1 c) (lump M.κ N)
      _ ≤ 1 := hx

lemma mem_lump {B : SlotModel.Boundary V C} (hs : Small B N) (y : V) (c : C) (r : ℕ) :
    (c, min r N) ∈ B y ↔ (c, r) ∈ B y := by
  by_cases hr : r < N
  · rw [min_eq_left hr.le]
  · constructor
    · intro h
      have := hs y _ h
      simp only at this
      omega
    · intro h
      have := hs y _ h
      simp only at this
      omega

/-- The lumping map on countable states. -/
def lumpState (ξ : C × ℕ × ℕ) : FState C N := (ξ.1, lumpIdx N ξ.2.1, lumpIdx N ξ.2.2)

lemma compat_lump {B : SlotModel.Boundary V C} (hs : Small B N) (e : E) (ξ : C × ℕ × ℕ) :
    M.Compat B e (jS N (lumpState N ξ)) ↔ M.Compat B e ξ := by
  unfold SlotModel.Compat
  apply forall_congr'
  intro y
  apply imp_congr Iff.rfl
  apply not_congr
  simp only [SlotModel.label, jS, lumpState, lumpIdx]
  split_ifs
  · exact mem_lump N hs y _ _
  · exact mem_lump N hs y _ _

/-- The fibres of the lumping map carry exactly the lumped activities. -/
lemma act_fibre (e : F) (a : FState C N) :
    HasSum (fun ξ => if lumpState N ξ = a then M.act e.1 ξ else 0)
      ((fsys M F N).activity e a) := by
  have hc : HasSum (fun c : C => if c = a.1 then M.x ^ M.exponent e.1 a.1 else 0)
      (M.x ^ M.exponent e.1 a.1) := hasSum_ite_eq a.1 _
  have h1 := lump_fibre M.κ N a.2.1
  have h2 := lump_fibre M.κ N a.2.2
  have hnn : ∀ (i : Fin (N + 1)) (r : ℕ),
      0 ≤ (if lumpIdx N r = i then M.κ.weight r else 0) := by
    intro i r
    split_ifs
    · exact M.κ.nonneg r
    · exact le_rfl
  have hp := hasSum_mul_nonneg h1 h2 (hnn a.2.1) (hnn a.2.2)
  have hcn : ∀ c : C, 0 ≤ (if c = a.1 then M.x ^ M.exponent e.1 a.1 else 0) := by
    intro c
    split_ifs
    · exact pow_nonneg M.x_nonneg _
    · exact le_rfl
  have hall := hasSum_mul_nonneg hc hp hcn (fun p => mul_nonneg (hnn _ _) (hnn _ _))
  have hfun : (fun ξ : C × ℕ × ℕ => if lumpState N ξ = a then M.act e.1 ξ else 0) =
      fun x : C × (ℕ × ℕ) => (if x.1 = a.1 then M.x ^ M.exponent e.1 a.1 else 0) *
        ((if lumpIdx N x.2.1 = a.2.1 then M.κ.weight x.2.1 else 0) *
          (if lumpIdx N x.2.2 = a.2.2 then M.κ.weight x.2.2 else 0)) := by
    funext ξ
    obtain ⟨c, r, s⟩ := ξ
    rw [SlotModel.act_apply]
    by_cases h1 : c = a.1
    · by_cases h2 : lumpIdx N r = a.2.1
      · by_cases h3 : lumpIdx N s = a.2.2
        · have ha : lumpState N (c, r, s) = a := by
            show (c, lumpIdx N r, lumpIdx N s) = a
            rw [h1, h2, h3]
          rw [if_pos ha, if_pos h1, if_pos h2, if_pos h3, h1]
          ring
        · have ha : lumpState N (c, r, s) ≠ a :=
            fun h => h3 (congrArg (fun z : FState C N => z.2.2) h)
          rw [if_neg ha, if_neg h3]
          simp
      · have ha : lumpState N (c, r, s) ≠ a :=
          fun h => h2 (congrArg (fun z : FState C N => z.2.1) h)
        rw [if_neg ha, if_neg h2]
        simp
    · have ha : lumpState N (c, r, s) ≠ a :=
        fun h => h1 (congrArg (fun z : FState C N => z.1) h)
      rw [if_neg ha, if_neg h1]
      simp
  have hval : (fsys M F N).activity e a =
      M.x ^ M.exponent e.1 a.1 * (lump M.κ N a.2.1 * lump M.κ N a.2.2) := by
    change M.x ^ M.exponent e.1 a.1 * lump M.κ N a.2.1 * lump M.κ N a.2.2 = _
    rw [mul_assoc]
  rw [hfun, hval]
  exact hall

/-- The compatible activity `M_e(B)` is unchanged by lumping, provided every
occupied label uses a slot `< N`. -/
lemma compatibleMass_eq {B : SlotModel.Boundary V C} (hs : Small B N) (e : F) :
    (fsys M F N).compatibleMass (finB N B) e = M.compatMass B e.1 := by
  have hterm : ∀ a : FState C N, HasSum
      (fun ξ => if M.Compat B e.1 (jS N a) then
        (if lumpState N ξ = a then M.act e.1 ξ else 0) else 0)
      (if M.Compat B e.1 (jS N a) then (fsys M F N).activity e a else 0) := by
    intro a
    by_cases hc : M.Compat B e.1 (jS N a)
    · simp only [if_pos hc]
      exact act_fibre M F N e a
    · simp only [if_neg hc]
      exact hasSum_zero
  have hs' := hasSum_sum (s := Finset.univ) (fun a _ => hterm a)
  have hfun : (fun ξ => ∑ a ∈ Finset.univ, if M.Compat B e.1 (jS N a) then
        (if lumpState N ξ = a then M.act e.1 ξ else 0) else 0) =
      compatibleWeight (M.act e.1) (M.Compat B e.1) := by
    funext ξ
    have hswap : ∀ a : FState C N, (if M.Compat B e.1 (jS N a) then
        (if lumpState N ξ = a then M.act e.1 ξ else 0) else 0) =
        if lumpState N ξ = a then (if M.Compat B e.1 (jS N a) then M.act e.1 ξ else 0)
          else 0 := by
      intro a
      split_ifs <;> rfl
    simp only [hswap]
    rw [Finset.sum_ite_eq Finset.univ (lumpState N ξ), if_pos (Finset.mem_univ _)]
    unfold compatibleWeight
    rw [compat_lump M N hs]
  rw [hfun] at hs'
  unfold SlotModel.compatMass compatibleMass
  rw [hs'.tsum_eq]
  unfold FiniteSystem.compatibleMass
  apply Finset.sum_congr rfl
  intro a _
  simp only [compatible_iff]

/-- **The lumped system satisfies (load), (fibre), (slack) exactly.** -/
theorem fin_bounds {B : SlotModel.Boundary V C} (hs : Small B N) {Δ : ℕ}
    (hB : M.Bounds Δ F B) : (fsys M F N).Bounds (finB N B) Δ := by
  refine ⟨fun y => ?_, fibreBound M F N, fun e => ?_⟩
  · rw [incident_card, card_finB N hs]
    exact hB.1 y
  · rw [compatibleMass_eq M F N hs, edgeDegree_eq]
    exact hB.2.2 e.1 e.2

end BoundsTransfer

/-! ## The one-label coupling bound for the countable lift -/

section Main
variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
variable [DecidableEq V] [DecidableEq E] [DecidableEq C]

/-- The finite endpoint-label library uses classical decidable equality on the
edge type; we use the same on the current free-edge subtype, so that the
finite laws and our finite sums share one `Fintype` instance. -/
local instance (priority := 2000) finsetDecEq (F : Finset E) : DecidableEq F :=
  Classical.decEq _

omit [Fintype V] [Fintype E] [Fintype C] [DecidableEq V] [DecidableEq E] [DecidableEq C] in
lemma mem_insert_any {α : Type*} {inst : DecidableEq α} {s : Finset α} {a b : α} :
    a ∈ @insert _ _ (@Finset.instInsert α inst) b s ↔ a = b ∨ a ∈ s := by
  let _ := inst
  exact Finset.mem_insert

/-- Adding one occupied label `l` at `v` (countable labels). -/
def addB (B : SlotModel.Boundary V C) (v : V) (l : C × ℕ) : SlotModel.Boundary V C :=
  Function.update B v (insert l (B v))

lemma addB_self (B : SlotModel.Boundary V C) (v : V) (l : C × ℕ) :
    addB B v l v = insert l (B v) := Function.update_self _ _ _

lemma addB_other (B : SlotModel.Boundary V C) (v y : V) (l : C × ℕ) (h : y ≠ v) :
    addB B v l y = B y := Function.update_of_ne h _ _

lemma finB_addB (N : ℕ) (B : SlotModel.Boundary V C) (v : V) (l : C × ℕ) (hl : l.2 < N + 1) :
    finB N (addB B v l) = FiniteSystem.addBoundary (finB N B) v (l.1, ⟨l.2, hl⟩) := by
  funext y
  ext l'
  by_cases hy : y = v
  · subst hy
    rw [FiniteSystem.addBoundary_self, mem_insert_any, mem_finB, mem_finB, addB_self,
      Finset.mem_insert]
    apply or_congr_left
    constructor
    · intro h
      apply jL_injective N
      exact h
    · rintro rfl
      rfl
  · rw [FiniteSystem.addBoundary_other _ _ _ _ hy, mem_finB, mem_finB, addB_other _ _ _ _ hy]

omit [Fintype V] [Fintype E] [Fintype C] [DecidableEq V] [DecidableEq E] [DecidableEq C] in
/-- The finite one-label bound, for any boundary equal to a single addition and
for any decidable-equality instance in the Hamming cost. -/
lemma replacement_of_eq {V' E' A L : Type*} [Fintype V'] [Fintype E'] [Fintype A] [Fintype L]
    (I : FiniteSystem V' E' A L) {Δ : ℕ} {t : ℝ} (h : I.SingleReplacementCI Δ t)
    (B : FiniteSystem.Boundary V' L) (v : V') (a b : L) (ha : a ∉ B v) (hb : b ∉ B v)
    {Ba Bb : FiniteSystem.Boundary V' L} (hBa : Ba = FiniteSystem.addBoundary B v a)
    (hBb : Bb = FiniteSystem.addBoundary B v b) (hA : I.Bounds Ba Δ) (hB : I.Bounds Bb Δ)
    [inst : DecidableEq A] :
    W (@ham E' A _ inst) (I.validLaw Ba hA) (I.validLaw Bb hB) ≤ t := by
  subst hBa hBb
  have h' := h B v a b ha hb hA hB
  convert h' using 3

lemma ham_JS (F : Finset E) (N : ℕ) [inst : DecidableEq (FState C N)]
    (σ σ' : F → FState C N) :
    ham (JS F N σ) (JS F N σ') = @ham F (FState C N) _ inst σ σ' := by
  unfold ham hamCard
  congr 1
  apply Finset.card_bij (fun e _ => e)
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact fun h => he (congrArg (jS N) h)
  · intro a _ b _ h
    exact h
  · intro e he
    refine ⟨e, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact fun h => he (jS_injective N h)

/-- **Lemma 8.5 (`lem:edge-one-label`), coupling form, for the countable lift.**
For every countable slot model, every current free-edge set `F` with at most
`n` edges, every occupied-label family `B` and distinct-or-equal labels
`α, β ∉ B_v` such that both `B^α = B ∪ {α at v}` and `B^β` satisfy
(load), (fibre), (slack), and every `η > 0`, there is a coupling of the two
countable lifted laws `ν_{F,B^α}`, `ν_{F,B^β}` with expected Hamming cost at
most `(Δ-1)/2 · (1 - ((Δ-1)/Δ)^n) + η`. -/
theorem edge_one_label_coupling (M : SlotModel V E C) {Δ n : ℕ} {F : Finset E}
    (hF : F.card ≤ n) (B : SlotModel.Boundary V C) (v : V) (α β : C × ℕ)
    (hα : α ∉ B v) (hβ : β ∉ B v)
    (hBα : M.Bounds Δ F (addB B v α)) (hBβ : M.Bounds Δ F (addB B v β))
    {η : ℝ} (hη : 0 < η) :
    ∃ π : CCoupling (M.law F (addB B v α)) (M.law F (addB B v β)),
      π.cost ham ≤ oneLabelBound Δ n + η := by
  set Bα := addB B v α with hBαdef
  set Bβ := addB B v β with hBβdef
  have hΔ : 1 ≤ Δ := by
    have h := hBα.1 v
    rw [hBαdef, addB_self, Finset.card_insert_of_notMem hα] at h
    omega
  have hb0 : 0 ≤ oneLabelBound Δ n :=
    FiniteSystem.oneLabelBound_nonneg (by exact_mod_cast hΔ) n
  have hZα := M.partition_pos hBα
  have hZβ := M.partition_pos hBβ
  have hpα := SlotModel.Bounds.law_hasSum M hBα
  have hpβ := SlotModel.Bounds.law_hasSum M hBβ
  have hp0 : ∀ ω, 0 ≤ M.law F Bα ω := fun ω => div_nonneg (M.weight_nonneg F Bα ω) hZα.le
  have hq0 : ∀ ω, 0 ≤ M.law F Bβ ω := fun ω => div_nonneg (M.weight_nonneg F Bβ ω) hZβ.le
  by_cases hFe : F = ∅
  · -- no free edge: the laws live on a one-point space
    refine ⟨prodCoupling _ _ hp0 hq0 hpα hpβ, ?_⟩
    have hham : ∀ x y : F → C × ℕ × ℕ, ham x y = 0 := by
      intro x y
      have hle := ham_le_card x y
      have hc : Fintype.card F = 0 := by
        rw [Fintype.card_coe, hFe, Finset.card_empty]
      rw [hc] at hle
      exact le_antisymm (by exact_mod_cast hle) (ham_nonneg x y)
    unfold CCoupling.cost
    simp only [hham, mul_zero, tsum_zero]
    linarith
  obtain ⟨e₀, he₀⟩ := Finset.nonempty_iff_ne_empty.mpr hFe
  have hC : Nonempty C := by
    have hs := hBα.2.2 e₀ he₀
    have hpos : 0 < M.compatMass Bα e₀ := by
      have := Nat.cast_nonneg (α := ℝ) (M.adjDegree F e₀)
      have := Nat.cast_nonneg (α := ℝ) Δ
      linarith
    obtain ⟨ξ, _, _⟩ := exists_positive_compatible (M.act e₀) (M.Compat Bα e₀) hpos
    exact ⟨ξ.1⟩
  set b := oneLabelBound (Δ : ℝ) n with hbdef
  set Zα := M.partition F Bα with hZαdef
  set Zβ := M.partition F Bβ with hZβdef
  set ZfA : ℕ → ℝ := fun N => (fsys M F N).partition (finB N Bα) with hZfAdef
  set ZfB : ℕ → ℝ := fun N => (fsys M F N).partition (finB N Bβ) with hZfBdef
  have hZfA_eq : ∀ N, ZfA N = Zα - Dc M F N Bα + Dfin M F N Bα := by
    intro N
    have h1 := fpartition_split M F N Bα
    have h2 := partition_split M F N Bα
    simp only [hZfAdef, hZαdef]
    rw [h1, h2]
    ring
  have hZfB_eq : ∀ N, ZfB N = Zβ - Dc M F N Bβ + Dfin M F N Bβ := by
    intro N
    have h1 := fpartition_split M F N Bβ
    have h2 := partition_split M F N Bβ
    simp only [hZfBdef, hZβdef]
    rw [h1, h2]
    ring
  have hZfA_t : Tendsto ZfA atTop (𝓝 Zα) := by
    have h := ((tendsto_const_nhds (x := Zα)).sub (Dc_tendsto M F Bα)).add
      (Dfin_tendsto M F Bα)
    rw [sub_zero, add_zero] at h
    exact h.congr (fun N => (hZfA_eq N).symm)
  have hZfB_t : Tendsto ZfB atTop (𝓝 Zβ) := by
    have h := ((tendsto_const_nhds (x := Zβ)).sub (Dc_tendsto M F Bβ)).add
      (Dfin_tendsto M F Bβ)
    rw [sub_zero, add_zero] at h
    exact h.congr (fun N => (hZfB_eq N).symm)
  set lamF : ℕ → ℝ := fun N => min (ZfA N / Zα) (ZfB N / Zβ) with hlamFdef
  set bound : ℕ → ℝ := fun N => lamF N * b + (n : ℝ) *
    (1 - lamF N * (1 - Dfin M F N Bα / ZfA N - Dfin M F N Bβ / ZfB N)) with hbounddef
  have hlam_t : Tendsto lamF atTop (𝓝 1) := by
    have h := (hZfA_t.div_const Zα).min (hZfB_t.div_const Zβ)
    rw [div_self hZα.ne', div_self hZβ.ne', min_self] at h
    exact h
  have hbound_t : Tendsto bound atTop (𝓝 b) := by
    have hd1 := (Dfin_tendsto M F Bα).div hZfA_t hZα.ne'
    have hd2 := (Dfin_tendsto M F Bβ).div hZfB_t hZβ.ne'
    have h := (hlam_t.mul_const b).add ((tendsto_const_nhds (x := (n : ℝ))).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub
        (hlam_t.mul (((tendsto_const_nhds (x := (1 : ℝ))).sub hd1).sub hd2))))
    have hlim : (1 : ℝ) * b + (n : ℝ) * (1 - 1 * (1 - 0 / Zα - 0 / Zβ)) = b := by
      simp
    rw [hlim] at h
    exact h
  have hev : ∀ᶠ N in atTop, bound N < b + η :=
    Filter.Tendsto.eventually_lt_const (by linarith) hbound_t
  set K := (Finset.univ.sup fun y => (Bα y ∪ Bβ y).sup fun l => l.2) + 1 with hK
  have hsmall : ∀ N, K ≤ N → Small Bα N ∧ Small Bβ N := by
    intro N hN
    have key : ∀ y, ∀ l ∈ Bα y ∪ Bβ y, l.2 < N := by
      intro y l hl
      have h1 : l.2 ≤ (Bα y ∪ Bβ y).sup fun l => l.2 :=
        Finset.le_sup (f := fun l : C × ℕ => l.2) hl
      have h2 : ((Bα y ∪ Bβ y).sup fun l => l.2) ≤
          Finset.univ.sup fun y => (Bα y ∪ Bβ y).sup fun l => l.2 :=
        Finset.le_sup (f := fun y => (Bα y ∪ Bβ y).sup fun l : C × ℕ => l.2)
          (Finset.mem_univ y)
      omega
    exact ⟨fun y l hl => key y l (Finset.mem_union_left _ hl),
      fun y l hl => key y l (Finset.mem_union_right _ hl)⟩
  obtain ⟨N, hKN, hNb⟩ := ((eventually_ge_atTop K).and hev).exists
  obtain ⟨hsα, hsβ⟩ := hsmall N hKN
  have hαN : α.2 < N + 1 := by
    have := hsα v α (by rw [hBαdef, addB_self]; exact Finset.mem_insert_self _ _)
    omega
  have hβN : β.2 < N + 1 := by
    have := hsβ v β (by rw [hBβdef, addB_self]; exact Finset.mem_insert_self _ _)
    omega
  set I := fsys M F N with hIdef
  have hfa : I.Bounds (finB N Bα) Δ := fin_bounds M F N hsα hBα
  have hfb : I.Bounds (finB N Bβ) Δ := fin_bounds M F N hsβ hBβ
  have : Nonempty (FState C N) := ⟨(Classical.arbitrary C, 0, 0)⟩
  have hcard : Fintype.card F ≤ n := by
    rw [Fintype.card_coe]
    exact hF
  have hci := FiniteSystem.single_replacement_ci_bound n I hΔ hcard
  have hα' : ((α.1, ⟨α.2, hαN⟩) : FLabel C N) ∉ finB N B v := by
    rw [mem_finB]
    exact hα
  have hβ' : ((β.1, ⟨β.2, hβN⟩) : FLabel C N) ∉ finB N B v := by
    rw [mem_finB]
    exact hβ
  have hW : W ham (I.validLaw (finB N Bα) hfa) (I.validLaw (finB N Bβ) hfb) ≤ b :=
    replacement_of_eq I hci (finB N B) v _ _ hα' hβ' (finB_addB N B v α hαN)
      (finB_addB N B v β hβN) hfa hfb
  set μ' := I.validLaw (finB N Bα) hfa with hμ'def
  set ν' := I.validLaw (finB N Bβ) hfb with hν'def
  obtain ⟨π', hπ'⟩ := exists_optimal_coupling μ' ν' ham ham_nonneg
  have hcost' : π'.cost ham ≤ b := hπ'.trans_le hW
  have hZfApos : 0 < ZfA N := FiniteSystem.Bounds.partition_pos I (finB N Bα) hfa
  have hZfBpos : 0 < ZfB N := FiniteSystem.Bounds.partition_pos I (finB N Bβ) hfb
  have hμ : ∀ σ, Good F N σ → M.law F Bα (JS F N σ) = (ZfA N / Zα) * μ'.w σ := by
    intro σ hσ
    change M.weight F Bα (JS F N σ) / Zα =
      ZfA N / Zα * (I.configurationWeight (finB N Bα) σ / I.partition (finB N Bα))
    rw [← cw_eq M F N Bα σ hσ]
    have hne : I.partition (finB N Bα) ≠ 0 := hZfApos.ne'
    change _ = I.partition (finB N Bα) / Zα * _
    rw [div_mul_div_comm, mul_comm (I.partition (finB N Bα)), mul_div_mul_right _ _ hne]
  have hν : ∀ σ, Good F N σ → M.law F Bβ (JS F N σ) = (ZfB N / Zβ) * ν'.w σ := by
    intro σ hσ
    change M.weight F Bβ (JS F N σ) / Zβ =
      ZfB N / Zβ * (I.configurationWeight (finB N Bβ) σ / I.partition (finB N Bβ))
    rw [← cw_eq M F N Bβ σ hσ]
    have hne : I.partition (finB N Bβ) ≠ 0 := hZfBpos.ne'
    change _ = I.partition (finB N Bβ) / Zβ * _
    rw [div_mul_div_comm, mul_comm (I.partition (finB N Bβ)), mul_div_mul_right _ _ hne]
  have hD : ∀ x y : F → C × ℕ × ℕ, ham x y ≤ (n : ℝ) := by
    intro x y
    refine (ham_le_card x y).trans ?_
    exact_mod_cast hcard
  obtain ⟨π, c, hc, hcle⟩ := transfer (JS F N) (JS_injective F N) (Good F N)
    (M.law F Bα) (M.law F Bβ) hp0 hq0 hpα hpβ μ' ν' π'
    (div_nonneg hZfApos.le hZα.le) (div_nonneg hZfBpos.le hZβ.le) hμ hν ham ham
    (fun σ σ' => ham_JS F N σ σ') ham_nonneg (Nat.cast_nonneg n) ham_nonneg hD
  have hbadα : ∑ σ ∈ Finset.univ.filter (fun σ => ¬ Good F N σ), μ'.w σ =
      Dfin M F N Bα / ZfA N := by
    rw [Finset.sum_filter]
    unfold Dfin
    rw [Finset.sum_div]
    refine Finset.sum_congr (by ext; simp) (fun σ _ => ?_)
    by_cases hg : Good F N σ
    · simp [hg]
    · rw [if_pos hg, if_neg hg]
      rfl
  have hbadβ : ∑ σ ∈ Finset.univ.filter (fun σ => ¬ Good F N σ), ν'.w σ =
      Dfin M F N Bβ / ZfB N := by
    rw [Finset.sum_filter]
    unfold Dfin
    rw [Finset.sum_div]
    refine Finset.sum_congr (by ext; simp) (fun σ _ => ?_)
    by_cases hg : Good F N σ
    · simp [hg]
    · rw [if_pos hg, if_neg hg]
      rfl
  rw [hbadα, hbadβ] at hcle
  refine ⟨π, ?_⟩
  have hcost : π.cost ham = c := hc.tsum_eq
  rw [hcost]
  have hlam0 : 0 ≤ lamF N := le_min (div_nonneg hZfApos.le hZα.le) (div_nonneg hZfBpos.le hZβ.le)
  have h1 : lamF N * π'.cost ham ≤ lamF N * b := mul_le_mul_of_nonneg_left hcost' hlam0
  have h2 : c ≤ bound N := by
    change c ≤ lamF N * b + (n : ℝ) *
      (1 - lamF N * (1 - Dfin M F N Bα / ZfA N - Dfin M F N Bβ / ZfB N))
    have : c ≤ lamF N * π'.cost ham + (n : ℝ) *
        (1 - lamF N * (1 - Dfin M F N Bα / ZfA N - Dfin M F N Bβ / ZfB N)) := hcle
    linarith
  linarith

/-- **Lemma 8.5 (`lem:edge-one-label`) for the countable lift.** The
Wasserstein distance `W_{1,F}` (infimum over couplings of the countable laws of
the expected Hamming cost) between `ν_{F,B^α}` and `ν_{F,B^β}` is at most
`(Δ-1)/2 · (1 - ((Δ-1)/Δ)^n)` whenever `|F| ≤ n` and both boundaries satisfy
(load), (fibre), (slack). Equivalently `T_n ≤ (Δ-1)/2 · (1 - ((Δ-1)/Δ)^n)`. -/
theorem edge_one_label (M : SlotModel V E C) {Δ n : ℕ} {F : Finset E}
    (hF : F.card ≤ n) (B : SlotModel.Boundary V C) (v : V) (α β : C × ℕ)
    (hα : α ∉ B v) (hβ : β ∉ B v)
    (hBα : M.Bounds Δ F (addB B v α)) (hBβ : M.Bounds Δ F (addB B v β)) :
    CW ham (M.law F (addB B v α)) (M.law F (addB B v β)) ≤ oneLabelBound Δ n :=
  CW_le ham_nonneg fun _ hη => edge_one_label_coupling M hF B v α β hα hβ hBα hBβ hη

/-- The second inequality of `eq:edge-one-label-bound`: the bound is at most
`(Δ-1)/2`, uniformly in `n`. -/
theorem edge_one_label_half (M : SlotModel V E C) {Δ n : ℕ} {F : Finset E}
    (hF : F.card ≤ n) (B : SlotModel.Boundary V C) (v : V) (α β : C × ℕ)
    (hα : α ∉ B v) (hβ : β ∉ B v)
    (hBα : M.Bounds Δ F (addB B v α)) (hBβ : M.Bounds Δ F (addB B v β)) :
    CW ham (M.law F (addB B v α)) (M.law F (addB B v β)) ≤ ((Δ : ℝ) - 1) / 2 := by
  have hΔ : 1 ≤ Δ := by
    have h := hBα.1 v
    rw [addB_self, Finset.card_insert_of_notMem hα] at h
    omega
  exact (edge_one_label M hF B v α β hα hβ hBα hBβ).trans
    (oneLabelBound_le (by exact_mod_cast hΔ) n)

/-- `T_0 = 0`: with no free edge the two lifted laws are at distance zero. -/
theorem edge_one_label_zero (M : SlotModel V E C) {Δ : ℕ} {F : Finset E}
    (hF : F.card = 0) (B : SlotModel.Boundary V C) (v : V) (α β : C × ℕ)
    (hα : α ∉ B v) (hβ : β ∉ B v)
    (hBα : M.Bounds Δ F (addB B v α)) (hBβ : M.Bounds Δ F (addB B v β)) :
    CW ham (M.law F (addB B v α)) (M.law F (addB B v β)) = 0 := by
  apply le_antisymm _ (CW_nonneg ham_nonneg _ _)
  have h := edge_one_label M (n := 0) (le_of_eq hF) B v α β hα hβ hBα hBβ
  rwa [oneLabelBound_zero] at h

/-- Every coupling of the two lifted laws has a genuinely convergent expected
Hamming cost, so `CW` is the infimum of actual expectations. -/
theorem cost_summable (M : SlotModel V E C) {Δ : ℕ} {F : Finset E}
    {B B' : SlotModel.Boundary V C} (hB : M.Bounds Δ F B)
    (π : CCoupling (M.law F B) (M.law F B')) :
    Summable (fun z => π.w z * ham z.1 z.2) :=
  π.summable_cost (SlotModel.Bounds.law_hasSum M hB).summable ham_nonneg
    (fun x y => ham_le_card x y)

end Main

end
end CI2ZF.Appendix.Edge.OneLabel
