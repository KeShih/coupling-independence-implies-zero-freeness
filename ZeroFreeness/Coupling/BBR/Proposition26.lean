import ZeroFreeness.Coupling.BBR.Certificate
import ZeroFreeness.Coupling.BBR.Theorem25

/-!
# BBR Proposition 2.6(i), proved

A complete proof of the `proposition_2_6_i` field of
`ZeroFreeness.Appendix.BBR.Literature`, for every colour type.

The proof follows BBR (EJP 30 (2025), paper 65), Section 4, but replaces
their Lemma 4.1 (smoothing) and Lemma 4.2(i) (conditioning on neighbour
colourings) by two applications of concavity of `log`:
* chord bound `log (1 - α p) ≥ (p/β) log (1 - α β)` for `0 ≤ p ≤ β`;
* Jensen / AM-GM `∑ y ≥ q exp ((∑ log y)/q)`.
Lemma 4.3 is proved by a derivative argument.
-/

namespace ZeroFreeness.Appendix.BBR
open scoped BigOperators
open Finset Set PottsCI
open ZeroFreeness.Appendix.Girth
noncomputable section
set_option linter.unusedSectionVars false

/-! ## Scalar lemmas -/

theorem phi_hasDerivAt {y : ℝ} (hy : y < 1) :
    HasDerivAt (fun y : ℝ => y + y * Real.log (1 - y / 2) + (1 - y) * Real.log (1 - y))
      (Real.log (1 - y / 2) - Real.log (1 - y) - y / (2 - y)) y := by
  have h1 : (1 - y / 2) ≠ 0 := by
    have : 0 < 1 - y / 2 := by linarith
    exact this.ne'
  have h2 : (1 - y) ≠ 0 := by
    have : 0 < 1 - y := by linarith
    exact this.ne'
  have h3 : (2 - y) ≠ 0 := by
    have : 0 < 2 - y := by linarith
    exact this.ne'
  have hd1 : HasDerivAt (fun y : ℝ => 1 - y / 2) (-(1 / 2)) y := by
    simpa using ((hasDerivAt_id y).div_const 2).const_sub 1
  have hd2 : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub 1
  have hl1 := hd1.log h1
  have hl2 := hd2.log h2
  have h := ((hasDerivAt_id' y).add ((hasDerivAt_id' y).mul hl1)).add (hd2.mul hl2)
  refine h.congr_deriv ?_
  field_simp
  ring

/-- BBR Lemma 4.3 in logarithmic form. -/
theorem lemma_4_3 {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    -Real.log (1 - z) ≤ z * Real.log (Real.exp 1 * (1 - z / 2) / (1 - z)) := by
  let φ : ℝ → ℝ := fun y => y + y * Real.log (1 - y / 2) + (1 - y) * Real.log (1 - y)
  have hmono : MonotoneOn φ (Icc 0 z) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 z)
      (f' := fun y => Real.log (1 - y / 2) - Real.log (1 - y) - y / (2 - y))
    · intro y hy
      exact (phi_hasDerivAt (by linarith [hy.2])).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact (phi_hasDerivAt (by linarith [hy.2])).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hy0 := hy.1
      have hy1 : y < 1 := by linarith [hy.2]
      have ha : 0 < 1 - y := by linarith
      have hb : 0 < 1 - y / 2 := by linarith
      have hr : 0 < (1 - y / 2) / (1 - y) := div_pos hb ha
      have hlog := Real.one_sub_inv_le_log_of_pos hr
      rw [Real.log_div hb.ne' ha.ne', inv_div] at hlog
      have h2y : (2 - y) ≠ 0 := by
        have : 0 < 2 - y := by linarith
        exact this.ne'
      have heq : 1 - (1 - y) / (1 - y / 2) = y / (2 - y) := by
        field_simp
        ring
      linarith
  have h := hmono ⟨le_refl 0, hz0.le⟩ ⟨hz0.le, le_refl z⟩ hz0.le
  have hφ0 : φ 0 = 0 := by simp [φ]
  have ha : 0 < 1 - z := by linarith
  have hb : 0 < 1 - z / 2 := by linarith
  rw [Real.log_div (by positivity) ha.ne', Real.log_mul (Real.exp_pos 1).ne' hb.ne', Real.log_exp]
  have hφ : 0 ≤ z + z * Real.log (1 - z / 2) + (1 - z) * Real.log (1 - z) := by
    have := h
    rw [hφ0] at this
    exact this
  nlinarith

/-- Lemma 4.3 at `z = k/D`. -/
theorem lemma_4_3' {k D : ℝ} (hk : 0 < k) (hkD : k < D) :
    -Real.log (1 - k / D) ≤ k / D * Real.log (Real.exp 1 * (D - k / 2) / (D - k)) := by
  have hD : 0 < D := hk.trans hkD
  have h := lemma_4_3 (div_pos hk hD) ((div_lt_one hD).2 hkD)
  have heq : Real.exp 1 * (1 - k / D / 2) / (1 - k / D) = Real.exp 1 * (D - k / 2) / (D - k) := by
    have : D - k ≠ 0 := (sub_pos.2 hkD).ne'
    field_simp
  rwa [heq] at h

theorem log_chord {α p β : ℝ} (hp : 0 ≤ p) (hpβ : p ≤ β) (hβ : 0 < β)
    (hαβ : α * β < 1) :
    p / β * Real.log (1 - α * β) ≤ Real.log (1 - α * p) := by
  have hl0 : 0 ≤ p / β := div_nonneg hp hβ.le
  have hl1 : p / β ≤ 1 := (div_le_one hβ).2 hpβ
  have h := strictConcaveOn_log_Ioi.concaveOn.2 (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show 1 - α * β ∈ Set.Ioi 0 by simp only [Set.mem_Ioi]; linarith)
    (show 0 ≤ 1 - p / β by linarith) hl0 (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at h
  have heq : 1 - p / β + p / β * (1 - α * β) = 1 - α * p := by
    field_simp
    ring
  rwa [heq] at h

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

theorem sum_log_chord {α β : ℝ} (p : C → ℝ) (hβ : 0 < β) (hαβ : α * β < 1)
    (hp : ∀ c, 0 ≤ p c ∧ p c ≤ β) (hsum : ∑ c, p c = 1) :
    1 / β * Real.log (1 - α * β) ≤ ∑ c, Real.log (1 - α * p c) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset C))
    (fun c _ => log_chord (hp c).1 (hp c).2 hβ hαβ)
  have heq : ∑ c, p c / β * Real.log (1 - α * β) = 1 / β * Real.log (1 - α * β) := by
    rw [← Finset.sum_mul, ← Finset.sum_div, hsum]
  linarith

theorem amgm_log (y : C → ℝ) (hy : ∀ c, 0 < y c) :
    (Fintype.card C : ℝ) * Real.exp ((∑ c, Real.log (y c)) / Fintype.card C) ≤ ∑ c, y c := by
  have hq : (0 : ℝ) < Fintype.card C := Nat.cast_pos.mpr Fintype.card_pos
  have h := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := (Finset.univ : Finset C))
    (w := fun _ => 1 / (Fintype.card C : ℝ)) (p := y)
    (fun _ _ => by positivity)
    (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
    (fun c _ => hy c)
  simp only [smul_eq_mul] at h
  rw [← Finset.mul_sum, ← Finset.mul_sum] at h
  have hs : 0 < ∑ c, y c := Finset.sum_pos (fun c _ => hy c) Finset.univ_nonempty
  have he := Real.exp_le_exp.2 h
  rw [Real.exp_log (by positivity)] at he
  have heq : 1 / (Fintype.card C : ℝ) * ∑ c, Real.log (y c) =
      (∑ c, Real.log (y c)) / Fintype.card C := by ring
  rw [heq] at he
  calc
    _ ≤ (Fintype.card C : ℝ) * (1 / (Fintype.card C : ℝ) * ∑ c, y c) :=
      mul_le_mul_of_nonneg_left he hq.le
    _ = _ := by field_simp

theorem log_segment {s X X' : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hX : 0 < X) (hX' : 0 < X') :
    s * Real.log X + (1 - s) * Real.log X' ≤ Real.log (s * X + (1 - s) * X') := by
  have h := strictConcaveOn_log_Ioi.concaveOn.2 (show X ∈ Set.Ioi 0 from hX)
    (show X' ∈ Set.Ioi 0 from hX') hs.1 (sub_nonneg.2 hs.2) (by ring)
  simpa only [smul_eq_mul] using h

/-! ## Cavity-tree estimates -/

theorem budget_real {Δ : ℕ} (t : Girth.CavityTree C) (ht : t.DegreeBudget Δ) :
    (t.degree : ℝ) + ∑ c, (t.boundary c : ℝ) + 1 ≤ Δ := by
  cases t with
  | node d b child =>
    have h := ht.1
    simp only [Girth.CavityTree.degree, Girth.CavityTree.boundary]
    exact_mod_cast h

/-- The sum of the logarithms of the squared message coordinates. -/
def logMass (x : ℝ) (t : Girth.CavityTree C) : ℝ := ∑ c, Real.log (t.ratioSquare x c)

theorem logMass_node {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (d : ℕ) (b : C → ℕ)
    (child : Fin d → Girth.CavityTree C) :
    logMass x (Girth.CavityTree.node d b child) =
      (∑ c, (b c : ℝ)) * Real.log x +
        ∑ i, ∑ c, Real.log (1 - (1 - x) * (child i).probability x c) := by
  unfold logMass
  have hc (c : C) : Real.log ((Girth.CavityTree.node d b child).ratioSquare x c) =
      (b c : ℝ) * Real.log x + ∑ i, Real.log (1 - (1 - x) * (child i).probability x c) := by
    have hf (i : Fin d) : 0 < 1 - (1 - x) * (child i).probability x c :=
      hx.trans_le ((child i).edgeFactor_mem hx hx1 c).1
    show Real.log (x ^ b c * ∏ i, (1 - (1 - x) * (child i).probability x c)) = _
    rw [Real.log_mul (pow_pos hx _).ne' (Finset.prod_pos fun i _ => hf i).ne', Real.log_pow,
      Real.log_prod (fun i _ => (hf i).ne')]
  simp_rw [hc]
  rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_comm]

/-- (T1): the free-child factors are at least `x` in geometric mean. -/
theorem logMass_lower_basic {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (t : Girth.CavityTree C) :
    ((t.degree : ℝ) + ∑ c, (t.boundary c : ℝ)) * Real.log x ≤ logMass x t := by
  cases t with
  | node d b child =>
    rw [logMass_node hx hx1]
    have hi (i : Fin d) :
        Real.log x ≤ ∑ c, Real.log (1 - (1 - x) * (child i).probability x c) := by
      have h := sum_log_chord (α := 1 - x) (β := 1) ((child i).probability x)
        one_pos (by linarith)
        (fun c => ⟨((child i).probabilityLaw x hx).nonneg c, ((child i).probabilityLaw x hx).le_one c⟩)
        ((child i).probabilityLaw x hx).sum_one
      have he : (1 : ℝ) / 1 * Real.log (1 - (1 - x) * 1) = Real.log x := by norm_num
      rwa [he] at h
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d))) (fun i _ => hi i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    simp only [Girth.CavityTree.degree, Girth.CavityTree.boundary]
    linarith

theorem logMass_lower_budget {Δ : ℕ} {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (t : Girth.CavityTree C) (ht : t.DegreeBudget Δ) :
    ((Δ : ℝ) - 1) * Real.log x ≤ logMass x t := by
  have hlogx : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1
  have hB := budget_real t ht
  have hL := logMass_lower_basic hx hx1 t
  have h : ((Δ : ℝ) - 1) * Real.log x ≤
      ((t.degree : ℝ) + ∑ c, (t.boundary c : ℝ)) * Real.log x :=
    mul_le_mul_of_nonpos_right (by linarith) hlogx
  linarith

/-- (T2): replaces BBR Lemma 4.2(i) and Corollary 4.5(i). -/
theorem probability_le_param {Δ : ℕ} {x K : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hK : 0 < K)
    (hfloor : K⁻¹ ≤ Real.exp (((Δ : ℝ) - 1) * Real.log x / Fintype.card C))
    (t : Girth.CavityTree C) (ht : t.DegreeBudget Δ) (c : C) :
    t.probability x c ≤ K / Fintype.card C := by
  have hq : (0 : ℝ) < Fintype.card C := Nat.cast_pos.mpr Fintype.card_pos
  have hL' := logMass_lower_budget hx hx1 t ht
  unfold logMass at hL'
  have hsum := amgm_log (t.ratioSquare x) (t.ratioSquare_pos hx)
  have hexp : Real.exp (((Δ : ℝ) - 1) * Real.log x / Fintype.card C) ≤
      Real.exp ((∑ c, Real.log (t.ratioSquare x c)) / Fintype.card C) :=
    Real.exp_le_exp.2 (div_le_div_of_nonneg_right hL' hq.le)
  have hS : (Fintype.card C : ℝ) / K ≤ ∑ c, t.ratioSquare x c := by
    rw [div_eq_mul_inv]
    exact (mul_le_mul_of_nonneg_left (hfloor.trans hexp) hq.le).trans hsum
  have hp : t.probability x c = t.ratioSquare x c / ∑ c, t.ratioSquare x c := by
    rw [t.probability_eq_square hx c, t.message_sq hx c]
    unfold squareMass
    simp_rw [t.message_sq hx]
  rw [hp]
  have hr1 := (t.ratioSquare_bounds hx hx1 c).2
  have hSpos : 0 < ∑ c, t.ratioSquare x c := lt_of_lt_of_le (div_pos hq hK) hS
  rw [div_le_iff₀ hSpos]
  calc t.ratioSquare x c ≤ 1 := hr1
    _ = K / Fintype.card C * (Fintype.card C / K) := by field_simp
    _ ≤ K / Fintype.card C * ∑ c, t.ratioSquare x c :=
      mul_le_mul_of_nonneg_left hS (div_pos hK hq).le

/-- (T3): replaces BBR Lemma 4.1 at the bound `K/q`. -/
theorem logMass_lower_free {Δ : ℕ} {x K : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hK : 0 < K)
    (hKΔ : K < Δ) (hα : 1 - x ≤ (Fintype.card C : ℝ) / Δ)
    (hfloor : K⁻¹ ≤ Real.exp (((Δ : ℝ) - 1) * Real.log x / Fintype.card C))
    (t : Girth.CavityTree C) (ht : t.DegreeBudget Δ) :
    (∑ c, (t.boundary c : ℝ)) * Real.log x +
      (t.degree : ℝ) * ((Fintype.card C : ℝ) / K * Real.log (1 - K / Δ)) ≤ logMass x t := by
  have hq : (0 : ℝ) < Fintype.card C := Nat.cast_pos.mpr Fintype.card_pos
  have hΔ : (0 : ℝ) < Δ := hK.trans hKΔ
  cases t with
  | node d b child =>
    rw [logMass_node hx hx1]
    have hβ : 0 < K / Fintype.card C := div_pos hK hq
    have hαβ : (1 - x) * (K / Fintype.card C) ≤ K / Δ := by
      calc (1 - x) * (K / Fintype.card C) ≤ Fintype.card C / Δ * (K / Fintype.card C) :=
            mul_le_mul_of_nonneg_right hα hβ.le
        _ = K / Δ := by field_simp
    have hKΔ1 : K / Δ < 1 := (div_lt_one hΔ).2 hKΔ
    have hi (i : Fin d) : (Fintype.card C : ℝ) / K * Real.log (1 - K / Δ) ≤
        ∑ c, Real.log (1 - (1 - x) * (child i).probability x c) := by
      have h := sum_log_chord (α := 1 - x) (β := K / Fintype.card C) ((child i).probability x)
        hβ (by linarith)
        (fun c => ⟨((child i).probabilityLaw x hx).nonneg c,
          probability_le_param hx hx1 hK hfloor (child i) (ht.2 i) c⟩)
        ((child i).probabilityLaw x hx).sum_one
      have hmono : Real.log (1 - K / Δ) ≤ Real.log (1 - (1 - x) * (K / Fintype.card C)) :=
        Real.log_le_log (by linarith) (by linarith)
      rw [one_div_div] at h
      have h2 := mul_le_mul_of_nonneg_left hmono (div_pos hq hK).le
      linarith
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d))) (fun i _ => hi i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    simp only [Girth.CavityTree.degree, Girth.CavityTree.boundary]
    linarith

/-- Weighted AM-GM along the segment (the first step of BBR Lemma 4.6). -/
theorem segment_log_lower {x : ℝ} (hx : 0 < x) (t u : Girth.CavityTree C) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    s * logMass x t + (1 - s) * logMass x u ≤
      ∑ c, Real.log (segment s (t.message x) (u.message x) c ^ 2) := by
  unfold logMass
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro c _
  have h := log_segment hs (t.message_pos hx c) (u.message_pos hx c)
  rw [← t.message_sq hx c, ← u.message_sq hx c, Real.log_pow, Real.log_pow, Real.log_pow]
  unfold segment
  push_cast
  linarith

theorem ratio_le_of_mass {S α y ρ M : ℝ} (hS : 0 < S) (hy1 : y ≤ 1)
    (hα : 0 ≤ α) (hαS : α ≤ S * ρ) (hρ : ρ < 1) (hM : 1 / S ≤ M) :
    S / (S - α * y) ^ 2 ≤ M / (1 - ρ) ^ 2 := by
  have h1 : S * (1 - ρ) ≤ S - α * y := by nlinarith
  have h2 : 0 < S * (1 - ρ) := mul_pos hS (by linarith)
  have h3 : (S * (1 - ρ)) ^ 2 ≤ (S - α * y) ^ 2 := pow_le_pow_left₀ h2.le h1 2
  have h4 : 0 < 1 - ρ := by linarith
  calc S / (S - α * y) ^ 2 ≤ S / (S * (1 - ρ)) ^ 2 :=
        div_le_div_of_nonneg_left hS.le (by positivity) h3
    _ = (1 / S) / (1 - ρ) ^ 2 := by field_simp
    _ ≤ M / (1 - ρ) ^ 2 := div_le_div_of_nonneg_right hM (by positivity)

/-! ## Proposition 2.6(i) -/

/-- The exponent inequality combining the fixed and free contributions. -/
theorem exponent_bound {q Δ K W B f a g : ℝ} (hq : 0 < q) (hK : 0 < K) (hΔ1 : 1 < Δ)
    (hB : 0 ≤ B) (hf : 0 ≤ f) (hBf : f + B + 1 ≤ Δ)
    (ha : a ≤ q / Δ * Real.log K) (hg : g ≤ K / Δ * Real.log W)
    (hlK : 0 ≤ Real.log K) (hlW : 0 ≤ Real.log W) :
    B * (a / q) + f * (g / K) ≤
      (1 - f / (Δ - 1)) * Real.log K + f / (Δ - 1) * Real.log W := by
  have hΔ : 0 < Δ := by linarith
  have hd : 0 < Δ - 1 := by linarith
  have ha1 : a / q ≤ Real.log K / (Δ - 1) := by
    have h1 : a / q ≤ Real.log K / Δ := by
      rw [div_le_iff₀ hq]
      calc a ≤ q / Δ * Real.log K := ha
        _ = Real.log K / Δ * q := by ring
    exact h1.trans (div_le_div_of_nonneg_left hlK hd (by linarith))
  have hg1 : g / K ≤ Real.log W / (Δ - 1) := by
    have h1 : g / K ≤ Real.log W / Δ := by
      rw [div_le_iff₀ hK]
      calc g ≤ K / Δ * Real.log W := hg
        _ = Real.log W / Δ * K := by ring
    exact h1.trans (div_le_div_of_nonneg_left hlW hd (by linarith))
  have h1 : B * (a / q) ≤ (Δ - 1 - f) * (Real.log K / (Δ - 1)) :=
    (mul_le_mul_of_nonneg_left ha1 hB).trans
      (mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hlK hd.le))
  have h2 : f * (g / K) ≤ f * (Real.log W / (Δ - 1)) := mul_le_mul_of_nonneg_left hg1 hf
  have h3 : (Δ - 1 - f) * (Real.log K / (Δ - 1)) + f * (Real.log W / (Δ - 1)) =
      (1 - f / (Δ - 1)) * Real.log K + f / (Δ - 1) * Real.log W := by
    field_simp
  linarith

theorem sameDomain_degree {t u : Girth.CavityTree C} (h : CLMM.SameDomain t u) :
    u.degree = t.degree := by
  cases h
  rfl

/-- **BBR Proposition 2.6(i)**, exactly the `proposition_2_6_i` field of `Literature`. -/
theorem proposition_2_6_i_holds : ∀ (Δ : ℕ) (_hq : 3 ≤ Fintype.card C)
    (_hgap : Fintype.card C + 3 ≤ Δ) (x : ℝ), 0 < x → x < 1 →
    1 - (Fintype.card C : ℝ) / Δ ≤ x →
    ∀ (t u : Girth.CavityTree C), t.DegreeBudget Δ → u.DegreeBudget Δ →
      CLMM.SameDomain t u → t.boundary = u.boundary →
      segmentWeightSquare x (t.message x) (u.message x) ≤
        publishedWeightBound (Fintype.card C) Δ t.degree := by
  intro Δ hq hgap x hx0 hx1 hxlow t u ht hu hdom hb
  have hq0 : (0 : ℝ) < Fintype.card C := Nat.cast_pos.mpr Fintype.card_pos
  have hΔq : (Fintype.card C : ℝ) + 3 ≤ Δ := by exact_mod_cast hgap
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
  set Y := segment s (t.message x) (u.message x) with hYdef
  have hYc (c : C) : 0 ≤ Y c ∧ Y c ≤ 1 := by
    have h1 := (t.message_bounds hx0 hx1.le c).2
    have h2 := (u.message_bounds hx0 hx1.le c).2
    have h3 := (t.message_pos hx0 c).le
    have h4 := (u.message_pos hx0 c).le
    have hs0 := hs.1
    have hs1 := sub_nonneg.2 hs.2
    rw [hYdef]
    unfold segment
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
      unfold segment at h0
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

/-- Both cited BBR results, Proposition 2.6(i) and Theorem 2.5, are proved,
so the `Literature` bundle used by the BBR modules holds for every colour type. -/
theorem literature (C : Type*) [Fintype C] [DecidableEq C] [Nonempty C] : Literature C :=
  ⟨proposition_2_6_i_holds, theorem_2_5_holds⟩

end
end ZeroFreeness.Appendix.BBR
