import CI2ZF.Coupling.BBR.Proposition26

/-!
# BBR Proposition 2.6(i) at degree gap two (companion, `bbr-large-girth.tex`, lines 117-128)

The companion asserts that the proof of BBR Proposition 2.6(i) is valid for
`d ≥ q + 1`, i.e. `Δ ≥ q + 2`, although BBR print `d ≥ q + 2`.  The library
theorem `CI2ZF.Appendix.BBR.proposition_2_6_i_holds` is stated for
`q + 3 ≤ Δ`.  Here the same statement is proved for `q + 2 ≤ Δ`, reusing
the library's lemmas verbatim, and the companion's derivation of the
contraction certificate from the published bound is carried out for every
`Δ ≥ q + 2` (so the gap-two pairs no longer need the separate annulus
argument).
-/

namespace CI2ZF.Appendix.BBR
open scoped BigOperators
open Finset Set PottsCI
open CI2ZF.Appendix CI2ZF.Appendix.BBR CI2ZF.Appendix.Girth
noncomputable section
set_option linter.unusedSectionVars false

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

/-- **BBR Proposition 2.6(i) for `Δ ≥ q + 2`** (that is, `d = Δ - 1 ≥ q + 1`).
The statement is that of `proposition_2_6_i_holds` with the degree gap
weakened from `q + 3 ≤ Δ` to `q + 2 ≤ Δ`; the proof is the library proof,
which only uses `q + 2 ≤ Δ`. -/
theorem proposition_2_6_i_of_gap_two : ∀ (Δ : ℕ) (_hq : 3 ≤ Fintype.card C)
    (_hgap : Fintype.card C + 2 ≤ Δ) (x : ℝ), 0 < x → x < 1 →
    1 - (Fintype.card C : ℝ) / Δ ≤ x →
    ∀ (t u : Girth.CavityTree C), t.DegreeBudget Δ → u.DegreeBudget Δ →
      CLMM.SameDomain t u → t.boundary = u.boundary →
      segmentWeightSquare x (t.message x) (u.message x) ≤
        publishedWeightBound (Fintype.card C) Δ t.degree := by
  intro Δ hq hgap x hx0 hx1 hxlow t u ht hu hdom hb
  have hq0 : (0 : ℝ) < Fintype.card C := Nat.cast_pos.mpr Fintype.card_pos
  have hΔq : (Fintype.card C : ℝ) + 2 ≤ Δ := by exact_mod_cast hgap
  have hΔ : (0 : ℝ) < Δ := by linarith
  have hK0 : 0 < parameter (Fintype.card C) Δ := parameter_pos hq0 (by linarith)
  have hKΔ : parameter (Fintype.card C) Δ < Δ := parameter_lt_degree hq (by omega)
  set q : ℝ := (Fintype.card C : ℝ) with hqdef
  set K := parameter q Δ with hKdef
  set W := weightBase Δ K with hWdef
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlogK : 0 ≤ Real.log K := by
    apply Real.log_nonneg
    have h1 : (1 : ℝ) ≤ (Δ - q / 2) / (Δ - q) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    have : K = Real.exp 1 * ((Δ - q / 2) / (Δ - q)) := by
      rw [hKdef]; unfold parameter; ring
    rw [this]
    nlinarith
  have hlogW : 0 ≤ Real.log W := by
    apply Real.log_nonneg
    have h1 : (1 : ℝ) ≤ (Δ - K / 2) / (Δ - K) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    have : W = Real.exp 1 * ((Δ - K / 2) / (Δ - K)) := by
      rw [hWdef]; unfold weightBase; ring
    rw [this]
    nlinarith
  have hxq : -Real.log x ≤ q / Δ * Real.log K := by
    have h := lemma_4_3' (k := q) (D := Δ) hq0 (by linarith)
    have hpos : 0 < 1 - q / Δ := by
      have : q / Δ < 1 := (div_lt_one hΔ).2 (by linarith)
      linarith
    have hlog : Real.log (1 - q / Δ) ≤ Real.log x := Real.log_le_log hpos hxlow
    have hK : K = Real.exp 1 * (Δ - q / 2) / (Δ - q) := rfl
    rw [← hK] at h
    linarith
  have hWK : -Real.log (1 - K / Δ) ≤ K / Δ * Real.log W := lemma_4_3' hK0 hKΔ
  have hBt := budget_real t ht
  have hlogx0 : 0 ≤ -Real.log x := by linarith [Real.log_nonpos hx0.le hx1.le]
  have hfloor : K⁻¹ ≤ Real.exp (((Δ : ℝ) - 1) * Real.log x / q) := by
    rw [← Real.exp_log hK0, ← Real.exp_neg]
    apply Real.exp_le_exp.2
    have h := exponent_bound (B := (Δ : ℝ) - 1) (f := 0) (a := -Real.log x) (g := 0) (W := W)
      hq0 hK0 (by linarith) (by linarith) le_rfl (by linarith) hxq
      (by positivity) hlogK hlogW
    have heq : ((Δ : ℝ) - 1) * Real.log x / q = -(((Δ : ℝ) - 1) * (-Real.log x / q)) := by ring
    rw [heq]
    simp only [zero_div, sub_zero, one_mul, mul_zero, add_zero, zero_mul] at h
    linarith
  have hα : 1 - x ≤ q / Δ := by linarith
  have hdeg := sameDomain_degree hdom
  have hbsum : ∑ c, (u.boundary c : ℝ) = ∑ c, (t.boundary c : ℝ) := by rw [hb]
  -- the two lower bounds on `logMass`
  have hL1t := logMass_lower_budget hx0 hx1.le t ht
  have hL1u := logMass_lower_budget hx0 hx1.le u hu
  have hL2t := logMass_lower_free hx0 hx1.le hK0 hKΔ hα hfloor t ht
  have hL2u := logMass_lower_free hx0 hx1.le hK0 hKΔ hα hfloor u hu
  rw [hdeg, hbsum] at hL2u
  set f : ℝ := (t.degree : ℝ) with hfdef
  set L2 := (∑ c, (t.boundary c : ℝ)) * Real.log x + f * (q / K * Real.log (1 - K / Δ))
    with hL2def
  set E := (1 - f / ((Δ : ℝ) - 1)) * Real.log K + f / ((Δ : ℝ) - 1) * Real.log W with hEdef
  have hE : -(L2 / q) ≤ E := by
    have h := exponent_bound (B := ∑ c, (t.boundary c : ℝ)) (f := f) (a := -Real.log x)
      (g := -Real.log (1 - K / Δ)) hq0 hK0 (by linarith)
      (Finset.sum_nonneg fun c _ => Nat.cast_nonneg _) (Nat.cast_nonneg _) hBt hxq hWK hlogK hlogW
    have heq : -(L2 / q) = (∑ c, (t.boundary c : ℝ)) * (-Real.log x / q) +
        f * (-Real.log (1 - K / Δ) / K) := by
      rw [hL2def]
      field_simp
      ring
    rw [heq]
    exact h
  have hρ : K / Δ < 1 := (div_lt_one hΔ).2 hKΔ
  -- the segment
  apply csSup_le (segmentWeightSet_nonempty x _ _)
  rintro z ⟨s, hs, c, rfl⟩
  set Y := BBR.segment s (t.message x) (u.message x) with hYdef
  have hYc (c : C) : 0 ≤ Y c ∧ Y c ≤ 1 := by
    have h1 := (t.message_bounds hx0 hx1.le c).2
    have h2 := (u.message_bounds hx0 hx1.le c).2
    have h3 := (t.message_pos hx0 c).le
    have h4 := (u.message_pos hx0 c).le
    have hs0 := hs.1
    have hs1 := sub_nonneg.2 hs.2
    rw [hYdef]
    unfold BBR.segment
    constructor
    · positivity
    · nlinarith
  have hYpos (c : C) : 0 < Y c ^ 2 := by
    have := log_segment hs (t.message_pos hx0 c) (u.message_pos hx0 c)
    have h3 := t.message_pos hx0 c
    have h4 := u.message_pos hx0 c
    have hne : Y c ≠ 0 := by
      intro h0
      rw [hYdef] at h0
      unfold BBR.segment at h0
      rcases eq_or_lt_of_le hs.1 with hs0 | hs0
      · rw [← hs0] at h0; simp at h0; linarith
      · nlinarith [mul_pos hs0 h3, mul_nonneg (sub_nonneg.2 hs.2) h4.le]
    positivity
  have hlogY := segment_log_lower hx0 t u hs
  rw [← hYdef] at hlogY
  have hamgm := amgm_log (fun c => Y c ^ 2) hYpos
  have hSdef : squareMass Y = ∑ c, Y c ^ 2 := rfl
  rw [← hSdef] at hamgm
  have hSpos : 0 < squareMass Y := Finset.sum_pos (fun c _ => hYpos c) Finset.univ_nonempty
  -- first lower bound: `S ≥ q/K`
  have hS2 : q / K ≤ squareMass Y := by
    have h1 : ((Δ : ℝ) - 1) * Real.log x ≤ ∑ c, Real.log (Y c ^ 2) := by
      have ha := mul_le_mul_of_nonneg_left hL1t hs.1
      have hb := mul_le_mul_of_nonneg_left hL1u (sub_nonneg.2 hs.2)
      linarith
    have h2 : Real.exp (((Δ : ℝ) - 1) * Real.log x / q) ≤
        Real.exp ((∑ c, Real.log (Y c ^ 2)) / q) :=
      Real.exp_le_exp.2 (div_le_div_of_nonneg_right h1 hq0.le)
    rw [div_eq_mul_inv]
    exact (mul_le_mul_of_nonneg_left (hfloor.trans h2) hq0.le).trans hamgm
  -- second lower bound: `S ≥ q exp(-E)`
  have hS1 : 1 / squareMass Y ≤ 1 / q * Real.exp E := by
    have h1 : L2 ≤ ∑ c, Real.log (Y c ^ 2) := by
      have ha := mul_le_mul_of_nonneg_left hL2t hs.1
      have hb := mul_le_mul_of_nonneg_left hL2u (sub_nonneg.2 hs.2)
      linarith
    have h2 : Real.exp (-E) ≤ Real.exp ((∑ c, Real.log (Y c ^ 2)) / q) := by
      apply Real.exp_le_exp.2
      have := div_le_div_of_nonneg_right h1 hq0.le
      linarith
    have h3 : q * Real.exp (-E) ≤ squareMass Y :=
      (mul_le_mul_of_nonneg_left h2 hq0.le).trans hamgm
    rw [div_le_iff₀ hSpos]
    calc (1 : ℝ) = 1 / q * Real.exp E * (q * Real.exp (-E)) := by
          rw [Real.exp_neg]; field_simp
      _ ≤ 1 / q * Real.exp E * squareMass Y :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  have hαS : 1 - x ≤ squareMass Y * (K / Δ) := by
    calc 1 - x ≤ q / Δ := hα
      _ = q / K * (K / Δ) := by field_simp
      _ ≤ squareMass Y * (K / Δ) := mul_le_mul_of_nonneg_right hS2 (by positivity)
  have hY1 : Y c ^ 2 ≤ 1 := pow_le_one₀ (hYc c).1 (hYc c).2
  have hmain := ratio_le_of_mass hSpos hY1 (by linarith) hαS hρ hS1
  unfold excludedMass
  refine hmain.trans (le_of_eq ?_)
  unfold publishedWeightBound
  rw [← hKdef, ← hWdef, ← hEdef]
  ring

/-- The library statement is the special case `q + 3 ≤ Δ`. -/
theorem proposition_2_6_i_holds_of_gap_two_version : ∀ (Δ : ℕ) (_hq : 3 ≤ Fintype.card C)
    (_hgap : Fintype.card C + 3 ≤ Δ) (x : ℝ), 0 < x → x < 1 →
    1 - (Fintype.card C : ℝ) / Δ ≤ x →
    ∀ (t u : Girth.CavityTree C), t.DegreeBudget Δ → u.DegreeBudget Δ →
      CLMM.SameDomain t u → t.boundary = u.boundary →
      segmentWeightSquare x (t.message x) (u.message x) ≤
        publishedWeightBound (Fintype.card C) Δ t.degree :=
  fun Δ hq hgap => proposition_2_6_i_of_gap_two Δ hq (by omega)

/-- **The contraction certificate from Proposition 2.6(i), for every
`Δ ≥ q + 2`.**  This is the companion's extraction
(`lem:bbr-certificate`, non-exceptional case): the published bound of
Proposition 2.6(i) at `d ≥ q + 1`, followed by the scalar estimate
`certificate_of_published_bound`, gives
`f (1-x)/e L_x(R,R')^2 ≤ (Δ-1)/Δ` on `[x₀, 1]`. -/
theorem contraction_certificate_of_gap_two {Δ : ℕ}
    (hq : 3 ≤ Fintype.card C) (hgap : Fintype.card C + 2 ≤ Δ)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / Fintype.card C)
    {x : ℝ} (hx : x ∈ Icc (intervalStart (Fintype.card C) Δ) 1)
    (t u : Girth.CavityTree C) (ht : t.DegreeBudget Δ) (hu : u.DegreeBudget Δ)
    (hdom : CLMM.SameDomain t u) (hb : t.boundary = u.boundary) :
    (t.degree : ℝ) * ((1 - x) / Real.exp 1) * segmentWeightSquare x (t.message x) (u.message x) ≤
      contractionSquare Δ := by
  have hq0 : (0 : ℝ) < Fintype.card C := Nat.cast_pos.mpr Fintype.card_pos
  have hdq := degree_gt_colours hq0 hr
  have hkΔ := parameter_lt_degree hq hgap
  have hx0 : 0 < x := (interval_formula_mem_Ioo hq0 hdq (parameter_pos hq0 hdq) hkΔ).1.trans_le hx.1
  have hΔ : 2 ≤ Δ := by omega
  by_cases hxone : x = 1
  · rw [hxone]
    simpa only [sub_self, zero_div, mul_zero, zero_mul] using (contractionSquare_mem hΔ).1.le
  have hxlt : x < 1 := lt_of_le_of_ne hx.2 hxone
  have hbasic := intervalStart_ge_basic hq0 hdq (parameter_pos hq0 hdq) hkΔ
  have hpublished := proposition_2_6_i_of_gap_two Δ hq hgap x hx0 hxlt (hbasic.trans hx.1)
    t u ht hu hdom hb
  have htdegree : t.degree ≤ Δ - 1 := (Nat.le_add_right _ _).trans (cavity_total_degree t ht)
  have hfreer : (t.degree : ℝ) ≤ (Δ : ℝ) - 1 := by
    have hh : (t.degree : ℝ) + 1 ≤ Δ := by exact_mod_cast (show t.degree + 1 ≤ Δ by omega)
    linarith
  exact certificate_of_published_bound hq0 (by exact_mod_cast (show 1 < Δ by omega)) hr hkΔ
    ⟨Nat.cast_nonneg _, hfreer⟩ hx.1 hx.2 hpublished

end
end CI2ZF.Appendix.BBR
