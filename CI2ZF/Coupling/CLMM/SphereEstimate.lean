import CI2ZF.Coupling.CLMM.Transfer
import CI2ZF.Coupling.CLMM.AmbientDegree
import CI2ZF.Coupling.Girth.Covariance.Graph.ResponseRoot

/-!
# CLMM2023 Equation (10): the graph sphere estimate

A complete proof of the `sphere_estimate` field of
`CI2ZF.Appendix.CLMM.Literature` from tree total-influence decay and
ratio-form relative SSM (Lemmas 5.19 and 5.20 of CLMM2023).
-/

namespace CI2ZF.Appendix.CLMM.Eq10
open scoped BigOperators
open Finset CI2ZF.Appendix.Girth

noncomputable section
set_option linter.unusedSectionVars false

universe u v

/-! ## Lemma 5.19 in abstract kernel form -/
section L519
variable {Y ι C : Type*} [Fintype Y] [Fintype C]

theorem lemma519_abstract (P Q : Y → ℝ) (Mf Mg : Y → ι → C → ℝ) (mf mg : ι → C → ℝ)
    (hP0 : ∀ y, 0 ≤ P y) (hQ0 : ∀ y, 0 ≤ Q y) (hP1 : ∑ y, P y = 1)
    (hMf0 : ∀ y i c, 0 ≤ Mf y i c) (hMg0 : ∀ y i c, 0 ≤ Mg y i c)
    (hMf1 : ∀ y i, ∑ c, Mf y i c ≤ 1) (hMg1 : ∀ y i, ∑ c, Mg y i c ≤ 1)
    (hmf : ∀ i c, mf i c = ∑ y, P y * Mf y i c) (hmg : ∀ i c, mg i c = ∑ y, Q y * Mg y i c)
    (S : Finset ι) (E2 : ℝ) (hE2 : 0 ≤ E2)
    (hloc : ∀ y, 0 < P y → 0 < Q y →
      ∑ i ∈ S, (1/2 : ℝ) * ∑ c, |Mf y i c - Mg y i c| ≤ E2) :
    ∑ i ∈ S, (1/2 : ℝ) * ∑ c, |mf i c - mg i c| ≤
      (S.card : ℝ) * ((1/2 : ℝ) * ∑ y, |P y - Q y|) + E2 := by
  set m : Y → ℝ := fun y => min (P y) (Q y) with hm
  have hm0 : ∀ y, 0 ≤ m y := fun y => le_min (hP0 y) (hQ0 y)
  have hmP : ∀ y, m y ≤ P y := fun y => min_le_left _ _
  have hmQ : ∀ y, m y ≤ Q y := fun y => min_le_right _ _
  have hPQ : ∀ y, (P y - m y) + (Q y - m y) = |P y - Q y| := by
    intro y
    simp only [hm]
    rcases le_total (P y) (Q y) with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
  -- pointwise bound
  have hpt : ∀ i c, |mf i c - mg i c| ≤ ∑ y, (m y * |Mf y i c - Mg y i c| +
      (P y - m y) * Mf y i c + (Q y - m y) * Mg y i c) := by
    intro i c
    rw [hmf, hmg, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    have he : P y * Mf y i c - Q y * Mg y i c =
        m y * (Mf y i c - Mg y i c) + (P y - m y) * Mf y i c - (Q y - m y) * Mg y i c := by ring
    rw [he]
    have h1 := abs_sub (m y * (Mf y i c - Mg y i c) + (P y - m y) * Mf y i c)
      ((Q y - m y) * Mg y i c)
    have h2 := abs_add_le (m y * (Mf y i c - Mg y i c)) ((P y - m y) * Mf y i c)
    rw [abs_mul, abs_of_nonneg (hm0 y)] at h2
    rw [abs_of_nonneg (mul_nonneg (by linarith [hmP y]) (hMf0 y i c))] at h2
    rw [abs_of_nonneg (mul_nonneg (by linarith [hmQ y]) (hMg0 y i c))] at h1
    linarith
  -- sum over colours
  have hsite : ∀ i, (1/2 : ℝ) * ∑ c, |mf i c - mg i c| ≤
      ∑ y, m y * ((1/2 : ℝ) * ∑ c, |Mf y i c - Mg y i c|) + (1/2 : ℝ) * ∑ y, |P y - Q y| := by
    intro i
    have hs : ∑ c, |mf i c - mg i c| ≤
        ∑ y, (m y * ∑ c, |Mf y i c - Mg y i c|) + ∑ y, |P y - Q y| := by
      calc ∑ c, |mf i c - mg i c|
          ≤ ∑ c, ∑ y, (m y * |Mf y i c - Mg y i c| +
            (P y - m y) * Mf y i c + (Q y - m y) * Mg y i c) := Finset.sum_le_sum fun c _ => hpt i c
        _ = ∑ y, (m y * ∑ c, |Mf y i c - Mg y i c| +
            (P y - m y) * ∑ c, Mf y i c + (Q y - m y) * ∑ c, Mg y i c) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y _
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
        _ ≤ ∑ y, (m y * ∑ c, |Mf y i c - Mg y i c| + (P y - m y) + (Q y - m y)) := by
          apply Finset.sum_le_sum
          intro y _
          have a1 := mul_le_mul_of_nonneg_left (hMf1 y i) (by linarith [hmP y] : 0 ≤ P y - m y)
          have a2 := mul_le_mul_of_nonneg_left (hMg1 y i) (by linarith [hmQ y] : 0 ≤ Q y - m y)
          linarith
        _ = ∑ y, (m y * ∑ c, |Mf y i c - Mg y i c|) + ∑ y, |P y - Q y| := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro y _
          rw [← hPQ y]; ring
    have : ∑ y, m y * ((1/2 : ℝ) * ∑ c, |Mf y i c - Mg y i c|) =
        (1/2 : ℝ) * ∑ y, (m y * ∑ c, |Mf y i c - Mg y i c|) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; ring
    rw [this]
    linarith
  -- sum over sites
  have hmsum : ∑ y, m y ≤ 1 := by
    rw [← hP1]; exact Finset.sum_le_sum fun y _ => hmP y
  have hloc' : ∀ y, m y * (∑ i ∈ S, (1/2 : ℝ) * ∑ c, |Mf y i c - Mg y i c|) ≤ m y * E2 := by
    intro y
    rcases eq_or_lt_of_le (hm0 y) with h0 | hpos
    · rw [← h0]; simp
    · have hp : 0 < P y := lt_of_lt_of_le hpos (hmP y)
      have hq : 0 < Q y := lt_of_lt_of_le hpos (hmQ y)
      exact mul_le_mul_of_nonneg_left (hloc y hp hq) (hm0 y)
  calc ∑ i ∈ S, (1/2 : ℝ) * ∑ c, |mf i c - mg i c|
      ≤ ∑ i ∈ S, (∑ y, m y * ((1/2 : ℝ) * ∑ c, |Mf y i c - Mg y i c|) +
          (1/2 : ℝ) * ∑ y, |P y - Q y|) := Finset.sum_le_sum fun i _ => hsite i
    _ = ∑ y, m y * (∑ i ∈ S, (1/2 : ℝ) * ∑ c, |Mf y i c - Mg y i c|) +
          (S.card : ℝ) * ((1/2 : ℝ) * ∑ y, |P y - Q y|) := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    _ ≤ ∑ y, m y * E2 + (S.card : ℝ) * ((1/2 : ℝ) * ∑ y, |P y - Q y|) := by
      have := Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) => hloc' y
      linarith
    _ ≤ E2 + (S.card : ℝ) * ((1/2 : ℝ) * ∑ y, |P y - Q y|) := by
      rw [← Finset.sum_mul]
      have := mul_le_mul_of_nonneg_right hmsum hE2
      linarith
    _ = _ := by ring

end L519

/-! ## Weighted masses and the kernel decomposition -/
section Masses
variable {Ω Y ι C : Type*} [Fintype Ω] [Fintype Y] [DecidableEq Y] [Fintype C] [DecidableEq C]

def fibMass (f : Ω → ℝ) (π : Ω → Y) (y : Y) : ℝ := ∑ ω, if π ω = y then f ω else 0

def condMass (f : Ω → ℝ) (π : Ω → Y) (obs : ι → Ω → C) (y : Y) (i : ι) (c : C) : ℝ :=
  (∑ ω, if π ω = y ∧ obs i ω = c then f ω else 0) / fibMass f π y

def siteMass (f : Ω → ℝ) (obs : ι → Ω → C) (i : ι) (c : C) : ℝ :=
  (∑ ω, if obs i ω = c then f ω else 0) / ∑ ω, f ω

variable (f : Ω → ℝ) (π : Ω → Y) (obs : ι → Ω → C)

theorem fibMass_nonneg (hf : ∀ ω, 0 ≤ f ω) (y : Y) : 0 ≤ fibMass f π y :=
  Finset.sum_nonneg fun ω _ => by split_ifs; exact hf ω; exact le_rfl

theorem sum_fibMass : ∑ y, fibMass f π y = ∑ ω, f ω := by
  unfold fibMass
  rw [Finset.sum_comm]
  simp

theorem condMass_nonneg (hf : ∀ ω, 0 ≤ f ω) (y : Y) (i : ι) (c : C) :
    0 ≤ condMass f π obs y i c :=
  div_nonneg (Finset.sum_nonneg fun ω _ => by split_ifs; exact hf ω; exact le_rfl)
    (fibMass_nonneg f π hf y)

theorem sum_condMass_le (_hf : ∀ ω, 0 ≤ f ω) (y : Y) (i : ι) :
    ∑ c, condMass f π obs y i c ≤ 1 := by
  unfold condMass
  rw [← Finset.sum_div]
  have hnum : ∑ c, (∑ ω, if π ω = y ∧ obs i ω = c then f ω else 0) = fibMass f π y := by
    unfold fibMass
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : π ω = y
    · simp [h]
    · simp [h]
  rw [hnum]
  by_cases h0 : fibMass f π y = 0
  · rw [h0]; simp
  · rw [div_self h0]

theorem siteMass_decomp (hf : ∀ ω, 0 ≤ f ω) (i : ι) (c : C) :
    siteMass f obs i c = ∑ y, (fibMass f π y / ∑ ω, f ω) * condMass f π obs y i c := by
  unfold siteMass
  have hpt : ∀ y, (fibMass f π y / ∑ ω, f ω) * condMass f π obs y i c =
      (∑ ω, if π ω = y ∧ obs i ω = c then f ω else 0) / ∑ ω, f ω := by
    intro y
    unfold condMass
    by_cases h0 : fibMass f π y = 0
    · have hz : (∑ ω, if π ω = y ∧ obs i ω = c then f ω else 0) = 0 := by
        apply le_antisymm _ (Finset.sum_nonneg fun ω _ => by split_ifs; exact hf ω; exact le_rfl)
        calc (∑ ω, if π ω = y ∧ obs i ω = c then f ω else 0) ≤ fibMass f π y := by
              unfold fibMass
              apply Finset.sum_le_sum
              intro ω _
              by_cases h1 : π ω = y
              · by_cases h2 : obs i ω = c <;> simp [h1, h2, hf ω]
              · simp [h1]
          _ = 0 := h0
      rw [hz, h0]; simp
    · field_simp
  simp_rw [hpt]
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : obs i ω = c
  · simp [h]
  · simp [h]

end Masses

/-! ## Lemma 5.20 in abstract ratio form -/
section L520
variable {Y C : Type*} [Fintype Y]

theorem lemma520_abstract (P : Y → C → ℝ) (w : Y → ℝ)
    (hP : ∀ y c, 0 < P y c) (hw : ∀ y, 0 ≤ w y) (hW : 0 < ∑ y, w y)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hratio : ∀ y y' c, |P y c / P y' c - 1| ≤ ε) (a b : C) :
    (1/2 : ℝ) * ∑ y, |P y a * w y / (∑ y', P y' a * w y') -
      P y b * w y / (∑ y', P y' b * w y')| ≤ 2 * ε := by
  set W := ∑ y, w y
  set ma := ∑ y', P y' a * w y'
  set mb := ∑ y', P y' b * w y'
  have hpos : ∀ c, 0 < ∑ y', P y' c * w y' := by
    intro c
    have hex : ∃ y0, 0 < w y0 := by
      by_contra hc
      have : ∑ y, w y ≤ 0 := Finset.sum_nonpos fun y _ => not_lt.mp fun h => hc ⟨y, h⟩
      linarith
    obtain ⟨y0, hy0⟩ := hex
    have hle := Finset.single_le_sum (f := fun y' => P y' c * w y')
      (fun y' _ => mul_nonneg (hP y' c).le (hw y')) (Finset.mem_univ y0)
    exact lt_of_lt_of_le (mul_pos (hP y0 c) hy0) hle
  have hma := hpos a
  have hmb := hpos b
  -- two-sided comparisons of the averages
  have hA : ∀ y, (1 - ε) * ma ≤ P y a * W ∧ P y a * W ≤ (1 + ε) * ma := by
    intro y
    have hle : ∀ y', (1 - ε) * P y' a ≤ P y a ∧ P y a ≤ (1 + ε) * P y' a := by
      intro y'
      have h := abs_le.mp (hratio y y' a)
      have hp' := hP y' a
      have e1 : P y a / P y' a * P y' a = P y a := div_mul_cancel₀ _ hp'.ne'
      constructor <;> nlinarith
    constructor
    · rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro y' _
      have := mul_le_mul_of_nonneg_right (hle y').1 (hw y')
      linarith
    · rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro y' _
      have := mul_le_mul_of_nonneg_right (hle y').2 (hw y')
      linarith
  have hB : ∀ y, (1 - ε) * (P y b * W) ≤ mb ∧ mb ≤ (1 + ε) * (P y b * W) := by
    intro y
    have hle : ∀ y', (1 - ε) * P y b ≤ P y' b ∧ P y' b ≤ (1 + ε) * P y b := by
      intro y'
      have h := abs_le.mp (hratio y' y b)
      have hp' := hP y b
      have e1 : P y' b / P y b * P y b = P y' b := div_mul_cancel₀ _ hp'.ne'
      constructor <;> nlinarith
    constructor
    · rw [← mul_assoc, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro y' _
      have := mul_le_mul_of_nonneg_right (hle y').1 (hw y')
      linarith
    · rw [← mul_assoc, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro y' _
      have := mul_le_mul_of_nonneg_right (hle y').2 (hw y')
      linarith
  have hpt : ∀ y, |P y a * w y / ma - P y b * w y / mb| ≤ 3 * ε * (P y b * w y / mb) := by
    intro y
    set X := P y a * W / ma
    set Z := mb / (P y b * W)
    have hpb := hP y b
    have hpbW : 0 < P y b * W := mul_pos hpb hW
    have hX : |X - 1| ≤ ε := by
      apply abs_le.mpr
      have h1 := (hA y).1
      have h2 := (hA y).2
      constructor
      · have : 1 - ε ≤ X := by rw [le_div_iff₀ hma]; linarith
        linarith
      · have : X ≤ 1 + ε := by rw [div_le_iff₀ hma]; linarith
        linarith
    have hZ : |Z - 1| ≤ ε := by
      apply abs_le.mpr
      have h1 := (hB y).1
      have h2 := (hB y).2
      constructor
      · have : 1 - ε ≤ Z := by rw [le_div_iff₀ hpbW]; linarith
        linarith
      · have : Z ≤ 1 + ε := by rw [div_le_iff₀ hpbW]; linarith
        linarith
    have hXZ : |X * Z - 1| ≤ 3 * ε := by
      have he : X * Z - 1 = (X - 1) * Z + (Z - 1) := by ring
      rw [he]
      have hZ2 : |Z| ≤ 2 := by
        have := abs_le.mp hZ
        rw [abs_le]; constructor <;> linarith
      calc |(X - 1) * Z + (Z - 1)| ≤ |(X - 1) * Z| + |Z - 1| := abs_add_le _ _
        _ = |X - 1| * |Z| + |Z - 1| := by rw [abs_mul]
        _ ≤ ε * 2 + ε := by
          have := mul_le_mul hX hZ2 (abs_nonneg _) hε0
          linarith
        _ = 3 * ε := by ring
    have hkey : P y a * w y / ma - P y b * w y / mb = (P y b * w y / mb) * (X * Z - 1) := by
      have hma' : ma ≠ 0 := hma.ne'
      have hmb' : mb ≠ 0 := hmb.ne'
      have hW' : W ≠ 0 := hW.ne'
      have hpb' : P y b ≠ 0 := hpb.ne'
      simp only [X, Z]
      field_simp
    rw [hkey, abs_mul, abs_of_nonneg (div_nonneg (mul_nonneg hpb.le (hw y)) hmb.le)]
    have h0 : 0 ≤ P y b * w y / mb := div_nonneg (mul_nonneg hpb.le (hw y)) hmb.le
    nlinarith
  have hsum1 : ∑ y, P y b * w y / mb = 1 := by
    rw [← Finset.sum_div]; exact div_self hmb.ne'
  calc (1/2 : ℝ) * ∑ y, |P y a * w y / ma - P y b * w y / mb|
      ≤ (1/2 : ℝ) * ∑ y, 3 * ε * (P y b * w y / mb) := by
        apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => hpt y) (by norm_num)
    _ = (3/2 : ℝ) * ε := by rw [← Finset.mul_sum, hsum1]; ring
    _ ≤ 2 * ε := by linarith

theorem small_of_log {B ρ : ℝ} {K : ℕ} (hB : 0 < B) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hK : Real.log B / (1 - ρ) ≤ K) : B * ρ ^ K ≤ 1 := by
  have h1 : Real.log B ≤ K * (1 - ρ) := (div_le_iff₀ (by linarith)).mp hK
  have h2 : Real.log ρ ≤ ρ - 1 := Real.log_le_sub_one_of_pos hρ
  have hpos : 0 < B * ρ ^ K := mul_pos hB (pow_pos hρ K)
  have hlog : Real.log (B * ρ ^ K) ≤ 0 := by
    rw [Real.log_mul hB.ne' (pow_pos hρ K).ne', Real.log_pow]
    have : (K : ℝ) * Real.log ρ ≤ K * (ρ - 1) :=
      mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg K)
    nlinarith
  have := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_log hpos, Real.exp_zero] at this

end L520
set_option linter.unusedSectionVars false

/-! ## Girth facts about distance layers -/
section Girth
variable {A : Type*} (G : SimpleGraph A)

theorem edist_adj_le {r v w : A} (h : G.Adj v w) : G.edist r w ≤ G.edist r v + 1 := by
  calc G.edist r w ≤ G.edist r v + G.edist v w := G.edist_triangle
    _ = G.edist r v + 1 := by rw [SimpleGraph.edist_eq_one_iff_adj.mpr h]

theorem edist_le_of_mem_support {r x v : A} (p : G.Walk r x) (hv : v ∈ p.support) :
    G.edist r v ≤ p.length := by
  classical
  calc G.edist r v ≤ (p.takeUntil v hv).length := SimpleGraph.edist_le _
    _ ≤ p.length := by exact_mod_cast p.length_takeUntil_le_length hv

theorem edist_lt_of_mem_edges {r u w : A} (p : G.Walk r u) (hne : u ≠ w)
    (he : s(u, w) ∈ p.edges) : G.edist r w < p.length := by
  classical
  have hw : w ∈ p.support := p.snd_mem_support_of_mem_edges he
  have hspec := p.take_spec hw
  have hlen : (p.takeUntil w hw).length + (p.dropUntil w hw).length = p.length := by
    conv_rhs => rw [← hspec]
    rw [SimpleGraph.Walk.length_append]
  have hpos : (p.dropUntil w hw).length ≠ 0 := by
    intro h0
    exact hne (SimpleGraph.Walk.eq_of_length_eq_zero h0).symm
  calc G.edist r w ≤ (p.takeUntil w hw).length := SimpleGraph.edist_le _
    _ < p.length := by exact_mod_cast (by omega)

theorem egirth_le_of_two_walks [DecidableEq A] {r u w : A} (h : G.Adj u w)
    (p : G.Walk r u) (q : G.Walk r w) (hp : s(u, w) ∉ p.edges) (hq : s(u, w) ∉ q.edges) :
    G.egirth ≤ p.length + q.length + 1 := by
  let W : G.Walk w u := q.reverse.append p
  have hW : s(u, w) ∉ W.edges := by
    simp only [W, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse,
      List.mem_append, List.mem_reverse, not_or]
    exact ⟨hq, hp⟩
  let B := W.bypass
  have hB : s(u, w) ∉ B.edges := fun hm => hW (W.edges_bypass_subset_edges hm)
  have hcyc : (SimpleGraph.Walk.cons h B).IsCycle :=
    (SimpleGraph.Walk.cons_isCycle_iff B h).mpr ⟨W.bypass_isPath, hB⟩
  have hlen : B.length ≤ W.length := W.length_bypass_le_length
  have hWlen : W.length = q.length + p.length := by
    simp [W, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  calc G.egirth ≤ (SimpleGraph.Walk.cons h B).length := G.egirth_le_length hcyc
    _ = B.length + 1 := by simp
    _ ≤ p.length + q.length + 1 := by exact_mod_cast (by omega)

/-- No edge joins two vertices at the same distance `j` when `2j+1 < girth`. -/
theorem egirth_le_of_same_layer {r u w : A} {j : ℕ} (h : G.Adj u w)
    (hu : G.edist r u = j) (hw : G.edist r w = j) : G.egirth ≤ 2 * j + 1 := by
  classical
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe hu
  obtain ⟨q, hq⟩ := SimpleGraph.exists_walk_of_edist_eq_coe hw
  have hpe : s(u, w) ∉ p.edges := by
    intro he
    have := edist_lt_of_mem_edges G p h.ne he
    rw [hw, hp] at this
    exact lt_irrefl _ this
  have hqe : s(u, w) ∉ q.edges := by
    intro he
    rw [Sym2.eq_swap] at he
    have := edist_lt_of_mem_edges G q h.ne.symm he
    rw [hu, hq] at this
    exact lt_irrefl _ this
  have := egirth_le_of_two_walks G h p q hpe hqe
  rw [hp, hq] at this
  calc G.egirth ≤ (j : ℕ∞) + j + 1 := this
    _ = 2 * j + 1 := by ring

/-- A vertex at distance `j+1` has at most one neighbour at distance `j`
when `2j+2 < girth`. -/
theorem egirth_le_of_two_parents {r u w w' : A} {j : ℕ} (h : G.Adj u w) (h' : G.Adj u w')
    (hu : G.edist r u = (j + 1 : ℕ)) (hw : G.edist r w = j) (hw' : G.edist r w' = j)
    (hne : w ≠ w') : G.egirth ≤ 2 * j + 2 := by
  classical
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe hw
  obtain ⟨q0, hq0⟩ := SimpleGraph.exists_walk_of_edist_eq_coe hw'
  let q : G.Walk r u := q0.concat h'.symm
  have hqlen : q.length = j + 1 := by simp [q, hq0]
  have hu_not : ∀ (x : A) (s : G.Walk r x), s.length = j → u ∉ s.support := by
    intro x s hs hmem
    have := edist_le_of_mem_support G s hmem
    rw [hu, hs] at this
    exact absurd (by exact_mod_cast this : j + 1 ≤ j) (by omega)
  have hpe : s(w, u) ∉ p.edges := by
    intro he
    exact hu_not w p hp (p.snd_mem_support_of_mem_edges he)
  have hqe : s(w, u) ∉ q.edges := by
    intro he
    simp only [q, SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.mem_append,
      List.mem_singleton] at he
    rcases he with he | he
    · exact hu_not w' q0 hq0 (q0.snd_mem_support_of_mem_edges he)
    · rcases Sym2.eq_iff.mp he with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hne h1
      · exact h.ne h1.symm
  have := egirth_le_of_two_walks G h.symm p q hpe hqe
  rw [hp, hqlen] at this
  calc G.egirth ≤ (j : ℕ∞) + ((j + 1 : ℕ) : ℕ∞) + 1 := this
    _ = 2 * j + 2 := by push_cast; ring

/-- Sphere sizes in a graph of maximum degree `Δ`. -/
theorem card_sphere_le [Fintype A] [DecidableEq A] [DecidableRel G.Adj] (r : A) (Δ : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (n : ℕ) :
    (univ.filter fun v => G.edist r v = n).card ≤ Δ ^ n := by
  induction n with
  | zero =>
    have : (univ.filter fun v => G.edist r v = ((0 : ℕ) : ℕ∞)) = {r} := by
      ext v
      simp only [mem_filter, mem_univ, true_and, mem_singleton, Nat.cast_zero]
      constructor
      · intro h; exact (SimpleGraph.edist_eq_zero_iff.mp h).symm
      · rintro rfl; exact SimpleGraph.edist_self
    rw [this]; simp
  | succ n ih =>
    have hsub : (univ.filter fun v => G.edist r v = ((n + 1 : ℕ) : ℕ∞)) ⊆
        (univ.filter fun v => G.edist r v = n).biUnion fun z => G.neighborFinset z := by
      intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv
      obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe hv
      cases hpr : p.reverse with
      | nil =>
        have := congrArg SimpleGraph.Walk.length hpr
        simp [hp] at this
      | @cons _ z _ hvz q =>
        have hql : q.length = n := by
          have := congrArg SimpleGraph.Walk.length hpr
          simp only [SimpleGraph.Walk.length_reverse, hp, SimpleGraph.Walk.length_cons] at this
          omega
        have hz1 : G.edist r z ≤ n := by
          have := SimpleGraph.edist_le q.reverse
          rw [SimpleGraph.Walk.length_reverse, hql] at this
          exact this
        have hz2 : (n + 1 : ℕ∞) ≤ G.edist r z + 1 := by
          have := edist_adj_le G (r := r) hvz.symm
          rw [hv] at this
          exact_mod_cast this
        have hz : G.edist r z = n := by
          obtain ⟨m, hm⟩ : ∃ m : ℕ, G.edist r z = m :=
            ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (by simp) hz1) |>.imp fun _ h => h.symm
          rw [hm] at hz1 hz2 ⊢
          have h1 : m ≤ n := by exact_mod_cast hz1
          have h2 : n + 1 ≤ m + 1 := by exact_mod_cast hz2
          have : m = n := by omega
          rw [this]
        simp only [mem_biUnion, mem_filter, mem_univ, true_and, SimpleGraph.mem_neighborFinset]
        exact ⟨z, hz, hvz.symm⟩
    calc _ ≤ ((univ.filter fun v => G.edist r v = n).biUnion fun z => G.neighborFinset z).card :=
          card_le_card hsub
      _ ≤ ∑ z ∈ univ.filter (fun v => G.edist r v = n), (G.neighborFinset z).card :=
          card_biUnion_le
      _ ≤ ∑ z ∈ univ.filter (fun v => G.edist r v = n), Δ :=
          sum_le_sum fun z _ => by rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg z
      _ = Δ * (univ.filter fun v => G.edist r v = n).card := by
          rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ Δ * Δ ^ n := Nat.mul_le_mul_left Δ ih
      _ = Δ ^ (n + 1) := by ring

end Girth
set_option linter.unusedSectionVars false


/-! ## Independence of coordinate-disjoint observables under counting measure -/
section Indep
variable {X : Type*} [Fintype X] [DecidableEq X] {C : Type*} [Fintype C] [DecidableEq C]
  [Nonempty C]

def DepOn (f : (X → C) → ℝ) (D : Set X) : Prop :=
  ∀ τ τ' : X → C, (∀ v ∈ D, τ v = τ' v) → f τ = f τ'

theorem DepOn.mono {f : (X → C) → ℝ} {D E : Set X} (h : DepOn f D) (hDE : D ⊆ E) :
    DepOn f E := fun τ τ' hτ => h τ τ' fun v hv => hτ v (hDE hv)

open Classical in
def mixCfg (D : Set X) (τ τ' : X → C) : X → C := fun v => if v ∈ D then τ v else τ' v

theorem sum_mul_sum_indep (f g : (X → C) → ℝ) (D : Set X) (hf : DepOn f D) (hg : DepOn g Dᶜ) :
    (∑ τ, f τ) * (∑ τ, g τ) = (Fintype.card (X → C) : ℝ) * ∑ τ, f τ * g τ := by
  classical
  let Φ : (X → C) × (X → C) → (X → C) × (X → C) :=
    fun p => (mixCfg D p.1 p.2, mixCfg D p.2 p.1)
  have hΦ : Function.Involutive Φ := by
    intro p
    ext v
    · simp only [Φ, mixCfg]; split_ifs <;> rfl
    · simp only [Φ, mixCfg]; split_ifs <;> rfl
  have h1 : ∀ τ τ', f τ * g τ' = f (mixCfg D τ τ') * g (mixCfg D τ τ') := by
    intro τ τ'
    rw [hf τ (mixCfg D τ τ') (fun v hv => by simp [mixCfg, hv]),
      hg τ' (mixCfg D τ τ') (fun v hv => by
        simp only [Set.mem_compl_iff] at hv; simp [mixCfg, hv])]
  calc (∑ τ, f τ) * (∑ τ, g τ) = ∑ τ, ∑ τ', f τ * g τ' := Finset.sum_mul_sum _ _ _ _
    _ = ∑ p : (X → C) × (X → C), (fun q => f q * g q) (Φ p).1 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro τ _
      apply Finset.sum_congr rfl; intro τ' _
      exact h1 τ τ'
    _ = ∑ p : (X → C) × (X → C), (fun q => f q * g q) p.1 :=
      Fintype.sum_equiv (hΦ.toPerm Φ) _ _ (fun p => rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Finset.mul_sum]

def avg (f : (X → C) → ℝ) : ℝ := (∑ τ, f τ) / (Fintype.card (X → C) : ℝ)

theorem card_cfg_pos : (0 : ℝ) < (Fintype.card (X → C) : ℝ) := by
  exact_mod_cast Fintype.card_pos

theorem avg_mul {f g : (X → C) → ℝ} {D D' : Set X} (hf : DepOn f D) (hg : DepOn g D')
    (hD : Disjoint D D') : avg (fun τ => f τ * g τ) = avg f * avg g := by
  have hg' : DepOn g Dᶜ := hg.mono (fun v hv => Set.disjoint_right.mp hD hv)
  have h := sum_mul_sum_indep f g D hf hg'
  have hN := (card_cfg_pos (X := X) (C := C)).ne'
  unfold avg
  rw [div_mul_div_comm, h]
  field_simp

theorem depOn_prod {ι : Type*} (s : Finset ι) (f : ι → (X → C) → ℝ) (D : ι → Set X)
    (E : Set X) (hf : ∀ i ∈ s, DepOn (f i) (D i)) (hE : ∀ i ∈ s, D i ⊆ E) :
    DepOn (fun τ => ∏ i ∈ s, f i τ) E := by
  intro τ τ' hτ
  apply Finset.prod_congr rfl
  intro i hi
  exact (hf i hi).mono (hE i hi) τ τ' hτ

theorem avg_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → (X → C) → ℝ)
    (D : ι → Set X) (hf : ∀ i ∈ s, DepOn (f i) (D i))
    (hD : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (D i) (D j)) :
    avg (fun τ => ∏ i ∈ s, f i τ) = ∏ i ∈ s, avg (f i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    unfold avg
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact div_self (card_cfg_pos (X := X) (C := C)).ne'
  | @insert j s hj ih =>
    have hf' : ∀ i ∈ s, DepOn (f i) (D i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hD' : ∀ i ∈ s, ∀ k ∈ s, i ≠ k → Disjoint (D i) (D k) := fun i hi k hk hik =>
      hD i (Finset.mem_insert_of_mem hi) k (Finset.mem_insert_of_mem hk) hik
    rw [Finset.prod_insert hj]
    simp_rw [Finset.prod_insert hj]
    have hrest : DepOn (fun τ => ∏ i ∈ s, f i τ) (⋃ i ∈ s, D i) :=
      depOn_prod s f D _ hf' (fun i hi => Set.subset_biUnion_of_mem (u := D) hi)
    have hdisj : Disjoint (D j) (⋃ i ∈ s, D i) := by
      rw [Set.disjoint_iUnion_right]
      intro i
      rw [Set.disjoint_iUnion_right]
      intro hi
      exact hD j (Finset.mem_insert_self j s) i (Finset.mem_insert_of_mem hi)
        (fun h => hj (h ▸ hi))
    rw [avg_mul (hf j (Finset.mem_insert_self j s)) hrest hdisj, ih hf' hD']

theorem avg_indicator_coord (v : X) (c : C) :
    avg (fun τ : X → C => if τ v = c then (1 : ℝ) else 0) = 1 / (Fintype.card C : ℝ) := by
  have hswap : ∀ c', (∑ τ : X → C, if τ v = c then (1 : ℝ) else 0) =
      ∑ τ : X → C, if τ v = c' then (1 : ℝ) else 0 := by
    intro c'
    apply Fintype.sum_equiv (Equiv.piCongrRight fun _ => Equiv.swap c c')
    intro τ
    simp only [Equiv.piCongrRight_apply]
    by_cases h : τ v = c
    · simp [h]
    · have : Equiv.swap c c' (τ v) ≠ c' := by
        intro h'
        apply h
        have := congrArg (Equiv.swap c c') h'
        simpa using this
      simp [h, this]
  have htot : ∑ c', (∑ τ : X → C, if τ v = c' then (1 : ℝ) else 0) =
      (Fintype.card (X → C) : ℝ) := by
    rw [Finset.sum_comm]
    simp
  simp_rw [← hswap] at htot
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at htot
  unfold avg
  have hC : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hN := (card_cfg_pos (X := X) (C := C))
  rw [div_eq_div_iff hN.ne' hC.ne', ← htot]
  ring

theorem depOn_indicator_coord (v : X) (c : C) :
    DepOn (fun τ : X → C => if τ v = c then (1 : ℝ) else 0) {v} := by
  intro τ τ' h
  simp only [h v (Set.mem_singleton v)]

end Indep

section TreeBuild
variable {X : Type u} [Fintype X] [DecidableEq X] {C : Type v} [Fintype C] [DecidableEq C]
variable (H : SimpleGraph X) [DecidableRel H.Adj] (d : X → ℕ∞) (b : X → C → ℕ)

def down (v : X) : Finset X := univ.filter fun w => H.Adj v w ∧ d w = d v + 1

def child (v : X) (i : Fin (down H d v).card) : X := ((down H d v).equivFin.symm i).1

def tree (y : X → C) : ℕ → X → CavityTree C
  | 0, v => .node 0 (fun c => b v c + ((down H d v).filter fun w => y w = c).card) Fin.elim0
  | n + 1, v => .node (down H d v).card (b v) (fun i => tree y n (child H d v i))

def desc : ℕ → X → Finset X
  | 0, v => {v}
  | n + 1, v => insert v ((down H d v).biUnion (desc n))

def reader (y : X → C) : (n : ℕ) → (v : X) → (X → C) → (tree H d b y n v).Configuration
  | 0, v, τ => (τ v, fun i => Fin.elim0 i)
  | n + 1, v, τ => (τ v, fun i => reader y n (child H d v i) τ)

def label (y : X → C) : (n : ℕ) → (v : X) → (k : ℕ) → (tree H d b y n v).Level k → X
  | _, v, 0, _ => v
  | 0, _, _ + 1, ℓ => Fin.elim0 ℓ.1
  | n + 1, v, k + 1, ℓ => label y n (child H d v ℓ.1) k ℓ.2


theorem mem_down {v w : X} : w ∈ down H d v ↔ H.Adj v w ∧ d w = d v + 1 := by
  simp [down]

theorem child_mem (v : X) (i : Fin (down H d v).card) : child H d v i ∈ down H d v :=
  ((down H d v).equivFin.symm i).2

theorem child_injective (v : X) : Function.Injective (child H d v) := by
  intro i i' h
  exact (down H d v).equivFin.symm.injective (Subtype.ext h)

theorem exists_child {v w : X} (hw : w ∈ down H d v) : ∃ i, child H d v i = w :=
  ⟨(down H d v).equivFin ⟨w, hw⟩, by simp [child]⟩

theorem prod_child {M : Type*} [CommMonoid M] (v : X) (f : X → M) :
    ∏ i, f (child H d v i) = ∏ w ∈ down H d v, f w := by
  rw [← Finset.prod_coe_sort (down H d v)]
  exact Fintype.prod_equiv (down H d v).equivFin.symm _ _ (fun i => rfl)

theorem down_dist {v w : X} {j : ℕ} (hv : d v = j) (hw : w ∈ down H d v) :
    d w = ((j + 1 : ℕ) : ℕ∞) := by
  rw [((mem_down H d).mp hw).2, hv]; push_cast; rfl

theorem self_mem_desc (n : ℕ) (v : X) : v ∈ desc H d n v := by
  cases n <;> simp [desc]

theorem desc_subset {n : ℕ} {v w : X} (hw : w ∈ down H d v) :
    desc H d n w ⊆ desc H d (n + 1) v := by
  intro u hu
  simp only [desc, mem_insert, mem_biUnion]
  exact Or.inr ⟨w, hw, hu⟩

theorem mem_desc_dist : ∀ (n : ℕ) (v : X) (j : ℕ), d v = j → ∀ u ∈ desc H d n v,
    ∃ m, m ≤ n ∧ d u = ((j + m : ℕ) : ℕ∞) := by
  intro n
  induction n with
  | zero =>
    intro v j hv u hu
    simp only [desc, mem_singleton] at hu
    exact ⟨0, le_rfl, by rw [hu, hv]; simp⟩
  | succ n ih =>
    intro v j hv u hu
    simp only [desc, mem_insert, mem_biUnion] at hu
    rcases hu with rfl | ⟨w, hw, hu⟩
    · exact ⟨0, by omega, by rw [hv]; simp⟩
    · obtain ⟨m, hm, hdu⟩ := ih w (j + 1) (down_dist H d hv hw) u hu
      exact ⟨m + 1, by omega, by rw [hdu]; congr 1; omega⟩

theorem parent_exists : ∀ (n : ℕ) (v u : X), u ∈ desc H d n v → u ≠ v →
    ∃ p ∈ desc H d n v, u ∈ down H d p := by
  intro n
  induction n with
  | zero =>
    intro v u hu hne
    simp only [desc, mem_singleton] at hu
    exact absurd hu hne
  | succ n ih =>
    intro v u hu hne
    simp only [desc, mem_insert, mem_biUnion] at hu
    rcases hu with rfl | ⟨w, hw, hu⟩
    · exact absurd rfl hne
    · by_cases huw : u = w
      · subst huw
        exact ⟨v, self_mem_desc H d _ v, hw⟩
      · obtain ⟨p, hp, hup⟩ := ih w u hu huw
        exact ⟨p, desc_subset H d hw hp, hup⟩

section Unique
variable (L : ℕ)
  (hpar : ∀ (z w w' : X) (j : ℕ), H.Adj z w → H.Adj z w' → d z = ((j + 1 : ℕ) : ℕ∞) →
    d w = j → d w' = j → j + 1 ≤ L → w = w')
include hpar

theorem desc_unique : ∀ (n : ℕ) (w w' : X) (j : ℕ), d w = j → d w' = j → j + n ≤ L →
    ∀ u, u ∈ desc H d n w → u ∈ desc H d n w' → w = w' := by
  intro n
  induction n with
  | zero =>
    intro w w' j _ _ _ u hu hu'
    simp only [desc, mem_singleton] at hu hu'
    rw [← hu, hu']
  | succ n ih =>
    intro w w' j hw hw' hjn u hu hu'
    simp only [desc, mem_insert, mem_biUnion] at hu hu'
    rcases hu with rfl | ⟨z, hz, hu⟩ <;> rcases hu' with hu' | ⟨z', hz', hu'⟩
    · exact hu'
    · obtain ⟨m, _, hm⟩ := mem_desc_dist H d n z' (j + 1) (down_dist H d hw' hz') u hu'
      rw [hw] at hm
      have := (Nat.cast_injective (R := ℕ∞)) hm
      omega
    · subst hu'
      obtain ⟨m, _, hm⟩ := mem_desc_dist H d n z (j + 1) (down_dist H d hw hz) u hu
      rw [hw'] at hm
      have := (Nat.cast_injective (R := ℕ∞)) hm
      omega
    · have hzz : z = z' := ih z z' (j + 1) (down_dist H d hw hz) (down_dist H d hw' hz')
        (by omega) u hu hu'
      subst hzz
      exact hpar z w w' j ((mem_down H d).mp hz).1.symm ((mem_down H d).mp hz').1.symm
        (down_dist H d hw hz) hw hw' (by omega)

theorem desc_disjoint {n : ℕ} {v : X} {j : ℕ} (hv : d v = j) (hjn : j + 1 + n ≤ L)
    {w w' : X} (hw : w ∈ down H d v) (hw' : w' ∈ down H d v) (hne : w ≠ w') :
    Disjoint (desc H d n w) (desc H d n w') := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  exact hne (desc_unique H d L hpar n w w' (j + 1) (down_dist H d hv hw) (down_dist H d hv hw')
    hjn u hu hu')

end Unique

theorem not_mem_desc_child {n : ℕ} {v w : X} {j : ℕ} (hv : d v = j) (hw : w ∈ down H d v) :
    v ∉ desc H d n w := by
  intro h
  obtain ⟨m, _, hm⟩ := mem_desc_dist H d n w (j + 1) (down_dist H d hv hw) v h
  rw [hv] at hm
  have := (Nat.cast_injective (R := ℕ∞)) hm
  omega

variable (y : X → C)

theorem reader_root (n : ℕ) (v : X) (τ : X → C) :
    (tree H d b y n v).rootColour (reader H d b y n v τ) = τ v := by
  cases n <;> rfl

theorem reader_congr : ∀ (n : ℕ) (v : X) (τ τ' : X → C), (∀ w ∈ desc H d n v, τ w = τ' w) →
    reader H d b y n v τ = reader H d b y n v τ' := by
  intro n
  induction n with
  | zero =>
    intro v τ τ' h
    have hv := h v (self_mem_desc H d 0 v)
    show ((τ v, fun i => Fin.elim0 i) : C × _) = (τ' v, fun i => Fin.elim0 i)
    rw [hv]
  | succ n ih =>
    intro v τ τ' h
    have hv := h v (self_mem_desc H d _ v)
    show ((τ v, fun i => reader H d b y n (child H d v i) τ) : C × _) =
      (τ' v, fun i => reader H d b y n (child H d v i) τ')
    rw [hv]
    congr 1
    funext i
    exact ih _ τ τ' fun w hw => h w (desc_subset H d (child_mem H d v i) hw)

theorem card_config_zero (v : X) :
    (Fintype.card (tree H d b y 0 v).Configuration : ℝ) = Fintype.card C := by
  have : Fintype.card (tree H d b y 0 v).Configuration =
      Fintype.card (C × ((i : Fin 0) → (Fin.elim0 i : CavityTree C).Configuration)) :=
    Fintype.card_congr (Equiv.refl _)
  rw [this, Fintype.card_prod, Fintype.card_pi]
  simp

theorem card_config_succ (n : ℕ) (v : X) :
    (Fintype.card (tree H d b y (n + 1) v).Configuration : ℝ) =
      Fintype.card C * ∏ i, (Fintype.card (tree H d b y n (child H d v i)).Configuration : ℝ) := by
  have : Fintype.card (tree H d b y (n + 1) v).Configuration =
      Fintype.card (C × ((i : Fin (down H d v).card) →
        (tree H d b y n (child H d v i)).Configuration)) :=
    Fintype.card_congr (Equiv.refl _)
  rw [this, Fintype.card_prod, Fintype.card_pi]
  push_cast
  rfl

variable [Nonempty C]

section Push
variable (L : ℕ)
  (hpar : ∀ (z w w' : X) (j : ℕ), H.Adj z w → H.Adj z w' → d z = ((j + 1 : ℕ) : ℕ∞) →
    d w = j → d w' = j → j + 1 ≤ L → w = w')
include hpar

open Classical in
theorem avg_reader : ∀ (n : ℕ) (v : X) (j : ℕ), d v = j → j + n ≤ L →
    ∀ ξ : (tree H d b y n v).Configuration,
      avg (fun τ => if reader H d b y n v τ = ξ then (1 : ℝ) else 0) =
        1 / (Fintype.card (tree H d b y n v).Configuration : ℝ) := by
  intro n
  induction n with
  | zero =>
    intro v j _ _ ξ
    have hiff : ∀ τ : X → C, reader H d b y 0 v τ = ξ ↔ τ v = ξ.1 := by
      intro τ
      constructor
      · rintro rfl; rfl
      · intro h
        exact Prod.ext h (funext fun i => Fin.elim0 i)
    simp_rw [hiff]
    rw [avg_indicator_coord, card_config_zero]
  | succ n ih =>
    intro v j hv hjn ξ
    have hiff : ∀ τ : X → C, reader H d b y (n + 1) v τ = ξ ↔
        (τ v = ξ.1 ∧ ∀ i, reader H d b y n (child H d v i) τ = ξ.2 i) := by
      intro τ
      constructor
      · rintro rfl; exact ⟨rfl, fun i => rfl⟩
      · rintro ⟨h1, h2⟩
        exact Prod.ext h1 (funext h2)
    have hind : ∀ τ : X → C, (if reader H d b y (n + 1) v τ = ξ then (1 : ℝ) else 0) =
        (if τ v = ξ.1 then (1 : ℝ) else 0) *
          ∏ i, (if reader H d b y n (child H d v i) τ = ξ.2 i then (1 : ℝ) else 0) := by
      intro τ
      by_cases h1 : τ v = ξ.1
      · by_cases h2 : ∀ i, reader H d b y n (child H d v i) τ = ξ.2 i
        · rw [if_pos ((hiff τ).mpr ⟨h1, h2⟩), if_pos h1,
            Finset.prod_eq_one (fun i _ => if_pos (h2 i))]
          ring
        · push Not at h2
          obtain ⟨i, hi⟩ := h2
          rw [if_neg (fun h => hi (((hiff τ).mp h).2 i)),
            Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)]
          ring
      · rw [if_neg (fun h => h1 ((hiff τ).mp h).1), if_neg h1]
        ring
    simp_rw [hind]
    have hdep_i : ∀ i ∈ (univ : Finset (Fin (down H d v).card)),
        DepOn (fun τ => if reader H d b y n (child H d v i) τ = ξ.2 i then (1 : ℝ) else 0)
          (desc H d n (child H d v i) : Set X) := by
      intro i _ τ τ' h
      dsimp only
      rw [reader_congr H d b y n _ τ τ' (fun w hw => h w hw)]
    have hprod := avg_prod (univ : Finset (Fin (down H d v).card))
      (fun i τ => if reader H d b y n (child H d v i) τ = ξ.2 i then (1 : ℝ) else 0)
      (fun i => (desc H d n (child H d v i) : Set X)) hdep_i (by
        intro i _ i' _ hii'
        exact Finset.disjoint_coe.mpr (desc_disjoint H d L hpar hv (by omega)
          (child_mem H d v i) (child_mem H d v i') (fun h => hii' (child_injective H d v h))))
    have hdep_prod : DepOn (fun τ => ∏ i,
        (if reader H d b y n (child H d v i) τ = ξ.2 i then (1 : ℝ) else 0))
          (⋃ i, (desc H d n (child H d v i) : Set X)) :=
      depOn_prod _ _ _ _ hdep_i (fun i _ => Set.subset_iUnion
        (fun i => (desc H d n (child H d v i) : Set X)) i)
    have hdisj : Disjoint ({v} : Set X) (⋃ i, (desc H d n (child H d v i) : Set X)) := by
      rw [Set.disjoint_singleton_left, Set.mem_iUnion]
      rintro ⟨i, hi⟩
      exact not_mem_desc_child H d hv (child_mem H d v i) hi
    rw [avg_mul (depOn_indicator_coord v ξ.1) hdep_prod hdisj, hprod, avg_indicator_coord,
      card_config_succ]
    have hch : ∀ i, avg (fun τ => if reader H d b y n (child H d v i) τ = ξ.2 i then (1 : ℝ) else 0)
        = 1 / (Fintype.card (tree H d b y n (child H d v i)).Configuration : ℝ) := fun i =>
      ih (child H d v i) (j + 1) (down_dist H d hv (child_mem H d v i)) (by omega) (ξ.2 i)
    simp_rw [hch]
    rw [Finset.prod_div_distrib, Finset.prod_const_one]
    field_simp

open Classical in
theorem sum_reader (n : ℕ) (v : X) (j : ℕ) (hv : d v = j) (hjn : j + n ≤ L)
    (F : (tree H d b y n v).Configuration → ℝ) :
    ∑ τ, F (reader H d b y n v τ) =
      ((Fintype.card (X → C) : ℝ) / Fintype.card (tree H d b y n v).Configuration) *
        ∑ ξ, F ξ := by
  have h1 : ∀ τ, F (reader H d b y n v τ) =
      ∑ ξ, (if reader H d b y n v τ = ξ then (1 : ℝ) else 0) * F ξ := by
    intro τ
    simp
  simp_rw [h1]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ξ _
  rw [← Finset.sum_mul]
  have := avg_reader H d b y L hpar n v j hv hjn ξ
  unfold avg at this
  have hN := card_cfg_pos (X := X) (C := C)
  rw [div_eq_iff hN.ne'] at this
  rw [this]
  ring

end Push

section Weight
variable (L : ℕ)
  (hpar : ∀ (z w w' : X) (j : ℕ), H.Adj z w → H.Adj z w' → d z = ((j + 1 : ℕ) : ℕ∞) →
    d w = j → d w' = j → j + 1 ≤ L → w = w')
include hpar

theorem cw_reader (x : ℝ) : ∀ (n : ℕ) (v : X) (j : ℕ), d v = j → j + n ≤ L →
    ∀ τ : X → C, (∀ w, d w = ((j + n + 1 : ℕ) : ℕ∞) → τ w = y w) →
    (tree H d b y n v).configurationWeight x (reader H d b y n v τ) =
      ∏ u ∈ desc H d n v, (x ^ b u (τ u) * ∏ w ∈ down H d u, (if τ u = τ w then x else 1)) := by
  intro n
  induction n with
  | zero =>
    intro v j hv _ τ hτ
    show x ^ (b v (τ v) + ((down H d v).filter fun w => y w = τ v).card) *
      ∏ i : Fin 0, _ = _
    rw [Fin.prod_univ_zero, mul_one]
    simp only [desc, Finset.prod_singleton]
    rw [pow_add]
    congr 1
    have hdown : ∀ w ∈ down H d v, τ w = y w := by
      intro w hw
      apply hτ
      rw [down_dist H d hv hw]
    rw [Finset.prod_congr rfl (fun w hw => by rw [hdown w hw]), Finset.prod_ite,
      Finset.prod_const_one, mul_one, Finset.prod_const]
    congr 2
    ext w
    simp [eq_comm]
  | succ n ih =>
    intro v j hv hjn τ hτ
    show x ^ (b v (τ v)) * ∏ i, ((if τ v = (tree H d b y n (child H d v i)).rootColour
        (reader H d b y n (child H d v i) τ) then x else 1) *
        (tree H d b y n (child H d v i)).configurationWeight x
          (reader H d b y n (child H d v i) τ)) = _
    have hch : ∀ i, (tree H d b y n (child H d v i)).configurationWeight x
        (reader H d b y n (child H d v i) τ) =
        ∏ u ∈ desc H d n (child H d v i),
          (x ^ b u (τ u) * ∏ w ∈ down H d u, (if τ u = τ w then x else 1)) := by
      intro i
      apply ih (child H d v i) (j + 1) (down_dist H d hv (child_mem H d v i)) (by omega) τ
      intro w hw
      apply hτ
      rw [hw]; congr 1; omega
    simp_rw [reader_root, hch]
    rw [prod_child H d v (fun w => (if τ v = τ w then x else 1) *
      ∏ u ∈ desc H d n w, (x ^ b u (τ u) * ∏ w ∈ down H d u, (if τ u = τ w then x else 1)))]
    rw [Finset.prod_mul_distrib]
    have hdisj : ((down H d v : Set X)).PairwiseDisjoint (desc H d n) := by
      intro w hw w' hw' hne
      exact desc_disjoint H d L hpar hv (by omega) hw hw' hne
    have hnot : v ∉ (down H d v).biUnion (desc H d n) := by
      simp only [mem_biUnion, not_exists, not_and]
      intro w hw hmem
      exact not_mem_desc_child H d hv hw hmem
    simp only [desc]
    rw [Finset.prod_insert hnot, Finset.prod_biUnion hdisj]
    ring

end Weight

section Budget

theorem card_down_succ_le {p v : X} {j : ℕ} (hpv : H.Adj p v) (hp : d p = j)
    (hv : d v = ((j + 1 : ℕ) : ℕ∞)) : (down H d v).card + 1 ≤ H.degree v := by
  have hpn : p ∉ down H d v := by
    intro hm
    have := ((mem_down H d).mp hm).2
    rw [hp, hv] at this
    norm_cast at this
    omega
  have hsub : insert p (down H d v) ⊆ H.neighborFinset v := by
    intro w hw
    rw [mem_insert] at hw
    rw [SimpleGraph.mem_neighborFinset]
    rcases hw with rfl | hw
    · exact hpv.symm
    · exact ((mem_down H d).mp hw).1
  have := card_le_card hsub
  rw [card_insert_of_notMem hpn, SimpleGraph.card_neighborFinset_eq_degree] at this
  exact this

theorem card_down_le (v : X) : (down H d v).card ≤ H.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply card_le_card
  intro w hw
  rw [SimpleGraph.mem_neighborFinset]
  exact ((mem_down H d).mp hw).1

theorem sum_filter_card (v : X) :
    ∑ c, ((down H d v).filter fun w => y w = c).card = (down H d v).card :=
  (Finset.card_eq_sum_card_fiberwise (fun w _ => Finset.mem_univ (y w))).symm

theorem tree_budget (Δ : ℕ) (hdeg : ∀ v, H.degree v + ∑ c, b v c ≤ Δ) :
    ∀ (n : ℕ) (v p : X) (j : ℕ), H.Adj p v → d p = j → d v = ((j + 1 : ℕ) : ℕ∞) →
      (tree H d b y n v).DegreeBudget Δ := by
  intro n
  induction n with
  | zero =>
    intro v p j hpv hp hv
    have hc := card_down_succ_le H d hpv hp hv
    have hs := sum_filter_card H d y v
    refine ⟨?_, fun i => Fin.elim0 i⟩
    rw [Finset.sum_add_distrib, hs]
    have := hdeg v
    omega
  | succ n ih =>
    intro v p j hpv hp hv
    have hc := card_down_succ_le H d hpv hp hv
    refine ⟨?_, fun i => ?_⟩
    · have := hdeg v
      omega
    · exact ih (child H d v i) v (j + 1) ((mem_down H d).mp (child_mem H d v i)).1 hv
        (down_dist H d hv (child_mem H d v i))

end Budget

section Domain

theorem tree_sameDomain (y' : X → C) : ∀ (n : ℕ) (v : X),
    CI2ZF.Appendix.CLMM.SameDomain (tree H d b y n v) (tree H d b y' n v) := by
  intro n
  induction n with
  | zero =>
    intro v
    refine CI2ZF.Appendix.CLMM.SameDomain.node 0 _ _ Fin.elim0 Fin.elim0 ?_ (fun i => Fin.elim0 i)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_filter_card, sum_filter_card]
  | succ n ih =>
    intro v
    exact CI2ZF.Appendix.CLMM.SameDomain.node _ (b v) (b v) _ _ rfl (fun i => ih _)

theorem tree_agreement (y' : X → C) : ∀ (n : ℕ) (v : X),
    CavityTree.Agreement n (tree H d b y n v) (tree H d b y' n v) := by
  intro n
  induction n with
  | zero =>
    intro v
    refine CavityTree.Agreement.zero _ _ rfl ?_
    show ∑ c, (b v c + ((down H d v).filter fun w => y w = c).card) =
      ∑ c, (b v c + ((down H d v).filter fun w => y' w = c).card)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_filter_card, sum_filter_card]
  | succ n ih =>
    intro v
    exact CavityTree.Agreement.succ n _ (b v) _ _ (fun i => ih _)

end Domain

section Labels

theorem levelColour_reader : ∀ (k n : ℕ) (v : X) (ℓ : (tree H d b y n v).Level k) (τ : X → C),
    (tree H d b y n v).levelColour k ℓ (reader H d b y n v τ) = τ (label H d b y n v k ℓ) := by
  intro k
  induction k with
  | zero =>
    intro n v ℓ τ
    cases n <;> rfl
  | succ k ih =>
    intro n v ℓ τ
    cases n with
    | zero => exact Fin.elim0 ℓ.1
    | succ n => exact ih n (child H d v ℓ.1) ℓ.2 τ

theorem label_surj : ∀ (n : ℕ) (v : X) (j : ℕ), d v = j → ∀ (k : ℕ) (u : X),
    u ∈ desc H d n v → d u = ((j + k : ℕ) : ℕ∞) →
      ∃ ℓ : (tree H d b y n v).Level k, label H d b y n v k ℓ = u := by
  intro n
  induction n with
  | zero =>
    intro v j hv k u hu hdu
    simp only [desc, mem_singleton] at hu
    subst hu
    rw [hv] at hdu
    have hk : k = 0 := by have := (Nat.cast_injective (R := ℕ∞)) hdu; omega
    subst hk
    exact ⟨(), rfl⟩
  | succ n ih =>
    intro v j hv k u hu hdu
    simp only [desc, mem_insert, mem_biUnion] at hu
    rcases hu with rfl | ⟨w, hw, hu⟩
    · rw [hv] at hdu
      have hk : k = 0 := by have := (Nat.cast_injective (R := ℕ∞)) hdu; omega
      subst hk
      exact ⟨(), rfl⟩
    · obtain ⟨m, _, hm⟩ := mem_desc_dist H d n w (j + 1) (down_dist H d hv hw) u hu
      rw [hm] at hdu
      have hk : k = m + 1 := by have := (Nat.cast_injective (R := ℕ∞)) hdu; omega
      subst hk
      obtain ⟨i, rfl⟩ := exists_child H d hw
      obtain ⟨ℓ', hℓ'⟩ := ih (child H d v i) (j + 1) (down_dist H d hv hw) m u hu hm
      exact ⟨⟨i, ℓ'⟩, hℓ'⟩

end Labels

section Edges

theorem enat_eq_of_add_one {e : ℕ∞} {k : ℕ} (h : e + 1 = ((k + 1 : ℕ) : ℕ∞)) : e = k := by
  induction e using ENat.recTopCoe with
  | top =>
    rw [top_add] at h
    exact absurd h.symm (ENat.natCast_ne_top _)
  | coe a =>
    norm_cast at h
    rw [show a = k by omega]

theorem enat_near {e : ℕ∞} {m : ℕ} (h1 : e ≤ (m : ℕ∞) + 1) (h2 : (m : ℕ∞) ≤ e + 1) :
    ∃ k : ℕ, e = k ∧ k ≤ m + 1 ∧ m ≤ k + 1 := by
  induction e using ENat.recTopCoe with
  | top => simp at h1
  | coe a =>
    refine ⟨a, rfl, ?_, ?_⟩
    · exact_mod_cast h1
    · exact_mod_cast h2

variable (L : ℕ) (x₀ : X) (hx₀ : d x₀ = 0)
  (hstep : ∀ u w, H.Adj u w → d w ≤ d u + 1)
  (hlayer : ∀ (u w : X) (j : ℕ), H.Adj u w → d u = j → d w = j → j ≤ L → False)
  (hpar : ∀ (z w w' : X) (j : ℕ), H.Adj z w → H.Adj z w' → d z = ((j + 1 : ℕ) : ℕ∞) →
    d w = j → d w' = j → j + 1 ≤ L → w = w')
include hx₀ hstep hlayer hpar

theorem desc_root_dist {u : X} (hu : u ∈ desc H d L x₀) : ∃ m, m ≤ L ∧ d u = (m : ℕ∞) := by
  obtain ⟨m, hm, h⟩ := mem_desc_dist H d L x₀ 0 (by rw [hx₀]; rfl) u hu
  exact ⟨m, hm, by rw [h]; simp⟩

theorem edge_touch {a c : X} (hac : H.Adj a c) (ha : a ∈ desc H d L x₀) :
    ∃ u w, u ∈ desc H d L x₀ ∧ w ∈ down H d u ∧ s(u, w) = s(a, c) := by
  obtain ⟨m, hmL, hdm⟩ := desc_root_dist H d L x₀ hx₀ hstep hlayer hpar ha
  have h1 : d c ≤ (m : ℕ∞) + 1 := by rw [← hdm]; exact hstep a c hac
  have h2 : (m : ℕ∞) ≤ d c + 1 := by rw [← hdm]; exact hstep c a hac.symm
  obtain ⟨k, hk, hk1, hk2⟩ := enat_near h1 h2
  rcases (by omega : k = m + 1 ∨ k = m ∨ k + 1 = m) with hkm | hkm | hkm
  · refine ⟨a, c, ha, (mem_down H d).mpr ⟨hac, ?_⟩, rfl⟩
    rw [hk, hdm, hkm]; push_cast; rfl
  · exact (hlayer a c m hac hdm (by rw [hk, hkm]) hmL).elim
  · have hne : a ≠ x₀ := by
      intro h
      rw [h, hx₀] at hdm
      have : m = 0 := by exact_mod_cast hdm.symm
      omega
    obtain ⟨p, hp, hap⟩ := parent_exists H d L x₀ a ha hne
    have hdp : d p = k := by
      apply enat_eq_of_add_one
      rw [← ((mem_down H d).mp hap).2, hdm, hkm]
    have hdak : d a = ((k + 1 : ℕ) : ℕ∞) := by rw [hdm, hkm]
    have hpc : p = c := hpar a p c k ((mem_down H d).mp hap).1.symm hac hdak hdp hk (by omega)
    subst hpc
    exact ⟨p, a, hp, hap, Sym2.eq_swap⟩

open Classical in
theorem prod_edges_split (E : Finset (Sym2 X)) (hE : ∀ e, e ∈ E ↔ e ∈ H.edgeSet)
    (φ : Sym2 X → ℝ) :
    ∏ e ∈ E, φ e = (∏ u ∈ desc H d L x₀, ∏ w ∈ down H d u, φ s(u, w)) *
      ∏ e ∈ E.filter (fun e => ∀ z ∈ e, z ∉ desc H d L x₀), φ e := by
  set U := desc H d L x₀ with hU
  rw [← Finset.prod_filter_not_mul_prod_filter E (fun e => ∀ z ∈ e, z ∉ U)]
  congr 1
  rw [← Finset.prod_sigma U (down H d) (fun q => φ s(q.1, q.2))]
  symm
  apply Finset.prod_bij (fun q _ => s(q.1, q.2))
  · intro q hq
    rw [Finset.mem_sigma] at hq
    rw [Finset.mem_filter, hE]
    refine ⟨((mem_down H d).mp hq.2).1, ?_⟩
    intro hall
    exact hall q.1 (Sym2.mem_mk_left _ _) hq.1
  · intro q hq q' hq' heq
    rw [Finset.mem_sigma] at hq hq'
    obtain ⟨u, w⟩ := q
    obtain ⟨u', w'⟩ := q'
    simp only at hq hq' heq
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2; rfl
    · exfalso
      subst h1; subst h2
      obtain ⟨m, _, hm⟩ := desc_root_dist H d L x₀ hx₀ hstep hlayer hpar hq.1
      have e1 := ((mem_down H d).mp hq.2).2
      have e2 := ((mem_down H d).mp hq'.2).2
      rw [hm, e1, hm] at e2
      norm_cast at e2
      omega
  · intro e he
    rw [Finset.mem_filter, hE] at he
    obtain ⟨heE, htouch⟩ := he
    induction e using Sym2.ind with
    | _ a c =>
      have hac : H.Adj a c := heE
      push Not at htouch
      obtain ⟨z, hz, hzU⟩ := htouch
      rcases Sym2.mem_iff.mp hz with rfl | rfl
      · obtain ⟨u, w, hu, hw, heq⟩ := edge_touch H d L x₀ hx₀ hstep hlayer hpar hac hzU
        exact ⟨⟨u, w⟩, Finset.mem_sigma.mpr ⟨hu, hw⟩, heq⟩
      · obtain ⟨u, w, hu, hw, heq⟩ := edge_touch H d L x₀ hx₀ hstep hlayer hpar hac.symm hzU
        exact ⟨⟨u, w⟩, Finset.mem_sigma.mpr ⟨hu, hw⟩, heq.trans Sym2.eq_swap⟩
  · intro q _
    rfl

end Edges

section Global
variable (I : PottsCI.PinningData X C) [DecidableRel I.graph.Adj] (L : ℕ) (x₀ : X)

def fibP (y' τ : X → C) : Prop := ∀ w, d w = ((L + 1 : ℕ) : ℕ∞) → τ w = y' w

open Classical in
def extW (x : ℝ) (τ : X → C) : ℝ :=
  (∏ u ∈ (desc I.graph d L x₀)ᶜ, x ^ I.boundaryCount u (τ u)) *
    ∏ e ∈ univ.filter (fun e => e ∈ I.graph.edgeSet ∧ ∀ z ∈ e, z ∉ desc I.graph d L x₀),
      PottsCI.PinningData.edgeFactor x τ e

theorem extW_nonneg {x : ℝ} (hx : 0 ≤ x) (τ : X → C) : 0 ≤ extW d I L x₀ x τ := by
  unfold extW
  apply mul_nonneg (Finset.prod_nonneg fun u _ => pow_nonneg hx _)
  apply Finset.prod_nonneg
  intro e _
  induction e using Sym2.ind with
  | _ a c =>
    rw [PottsCI.PinningData.edgeFactor_mk]
    split_ifs
    · exact hx
    · exact zero_le_one

theorem extW_depOn (x : ℝ) :
    DepOn (extW d I L x₀ x) ((desc I.graph d L x₀ : Set X))ᶜ := by
  intro τ τ' h
  unfold extW
  congr 1
  · apply Finset.prod_congr rfl
    intro u hu
    rw [h u (by simpa using hu)]
  · apply Finset.prod_congr rfl
    intro e he
    rw [Finset.mem_filter] at he
    induction e using Sym2.ind with
    | _ a c =>
      have ha := he.2.2 a (Sym2.mem_mk_left a c)
      have hc := he.2.2 c (Sym2.mem_mk_right a c)
      rw [PottsCI.PinningData.edgeFactor_mk, PottsCI.PinningData.edgeFactor_mk,
        h a (by simpa using ha), h c (by simpa using hc)]

variable (hx₀ : d x₀ = 0)
  (hstep : ∀ u w, I.graph.Adj u w → d w ≤ d u + 1)
  (hlayer : ∀ (u w : X) (j : ℕ), I.graph.Adj u w → d u = j → d w = j → j ≤ L → False)
  (hpar : ∀ (z w w' : X) (j : ℕ), I.graph.Adj z w → I.graph.Adj z w' →
    d z = ((j + 1 : ℕ) : ℕ∞) → d w = j → d w' = j → j + 1 ≤ L → w = w')
include hx₀ hstep hlayer hpar

theorem weight_eq (x : ℝ) (τ : X → C) (hτ : fibP d L y τ) :
    I.weight x τ = extW d I L x₀ x τ *
      (tree I.graph d I.boundaryCount y L x₀).configurationWeight x
        (reader I.graph d I.boundaryCount y L x₀ τ) := by
  classical
  have hx₀' : d x₀ = ((0 : ℕ) : ℕ∞) := by rw [hx₀]; rfl
  rw [cw_reader I.graph d I.boundaryCount y L hpar x L x₀ 0 hx₀' (by omega) τ
    (fun w hw => hτ w (by rw [hw]; congr 1; omega))]
  have hw : I.weight x τ = (∏ u, x ^ I.boundaryCount u (τ u)) *
      ∏ e ∈ univ.filter (fun e => e ∈ I.graph.edgeSet), PottsCI.PinningData.edgeFactor x τ e := by
    unfold PottsCI.PinningData.weight
    congr 1
    apply Finset.prod_congr _ (fun _ _ => rfl)
    ext e; simp [SimpleGraph.mem_edgeFinset]
  rw [hw]
  unfold extW
  rw [prod_edges_split I.graph d L x₀ hx₀ hstep hlayer hpar _
    (fun e => by simp) (PottsCI.PinningData.edgeFactor x τ)]
  rw [← Finset.prod_mul_prod_compl (desc I.graph d L x₀)
    (fun u => x ^ I.boundaryCount u (τ u))]
  rw [Finset.prod_mul_distrib]
  have hfilt : (univ.filter (fun e => e ∈ I.graph.edgeSet)).filter
      (fun e => ∀ z ∈ e, z ∉ desc I.graph d L x₀) =
      univ.filter (fun e => e ∈ I.graph.edgeSet ∧ ∀ z ∈ e, z ∉ desc I.graph d L x₀) := by
    rw [Finset.filter_filter]
  rw [hfilt]
  have hedge : ∏ u ∈ desc I.graph d L x₀, ∏ w ∈ down I.graph d u,
      PottsCI.PinningData.edgeFactor x τ s(u, w) =
      ∏ u ∈ desc I.graph d L x₀, ∏ w ∈ down I.graph d u, (if τ u = τ w then x else 1) := rfl
  rw [hedge]
  ring

open Classical in
theorem sum_factor (G1 : (X → C) → ℝ)
    (hG1 : DepOn G1 ((desc I.graph d L x₀ : Set X))ᶜ) (x : ℝ)
    (F : (tree I.graph d I.boundaryCount y L x₀).Configuration → ℝ) :
    ∑ τ, (if fibP d L y τ then G1 τ * extW d I L x₀ x τ else 0) *
        F (reader I.graph d I.boundaryCount y L x₀ τ) =
      (∑ τ, if fibP d L y τ then G1 τ * extW d I L x₀ x τ else 0) * (∑ ξ, F ξ) /
        Fintype.card (tree I.graph d I.boundaryCount y L x₀).Configuration := by
  classical
  set U := desc I.graph d L x₀
  have hfib : DepOn (fun τ => if fibP d L y τ then G1 τ * extW d I L x₀ x τ else 0)
      ((U : Set X))ᶜ := by
    intro τ τ' h
    have hiff : fibP d L y τ ↔ fibP d L y τ' := by
      have hw : ∀ w, d w = ((L + 1 : ℕ) : ℕ∞) → τ w = τ' w := by
        intro w hw
        apply h w
        intro hwU
        obtain ⟨m, hm, hdm⟩ := desc_root_dist I.graph d L x₀ hx₀ hstep hlayer hpar hwU
        rw [hdm] at hw
        have := (Nat.cast_injective (R := ℕ∞)) hw
        omega
      constructor
      · intro hf w hw'; rw [← hw w hw']; exact hf w hw'
      · intro hf w hw'; rw [hw w hw']; exact hf w hw'
    simp only [hiff, hG1 τ τ' h, extW_depOn d I L x₀ x τ τ' h]
  have hread : DepOn (fun τ => F (reader I.graph d I.boundaryCount y L x₀ τ))
      ((U : Set X))ᶜᶜ := by
    intro τ τ' h
    simp only [compl_compl] at h
    dsimp only
    rw [reader_congr I.graph d I.boundaryCount y L x₀ τ τ' (fun w hw => h w hw)]
  have hx₀' : d x₀ = ((0 : ℕ) : ℕ∞) := by rw [hx₀]; rfl
  have hind := sum_mul_sum_indep _ _ _ hfib hread
  rw [sum_reader I.graph d I.boundaryCount y L hpar L x₀ 0 hx₀' (by omega) F] at hind
  have hN := card_cfg_pos (X := X) (C := C)
  have hc : (0 : ℝ) < Fintype.card (tree I.graph d I.boundaryCount y L x₀).Configuration := by
    exact_mod_cast Fintype.card_pos
  rw [eq_div_iff hc.ne']
  set S1 := ∑ τ, (if fibP d L y τ then G1 τ * extW d I L x₀ x τ else 0) *
    F (reader I.graph d I.boundaryCount y L x₀ τ)
  set S2 := ∑ τ, if fibP d L y τ then G1 τ * extW d I L x₀ x τ else 0
  set S3 := ∑ ξ, F ξ
  set M := (Fintype.card (tree I.graph d I.boundaryCount y L x₀).Configuration : ℝ)
  set N := (Fintype.card (X → C) : ℝ)
  have := hind
  field_simp at this
  linarith

end Global

end TreeBuild
theorem ratio_cancel {X S r N : ℝ} (hS : S ≠ 0) (hr : r ≠ 0) (hN : N ≠ 0) :
    (X * r / N) / (S * r / N) = X / S := by
  field_simp

/-! ## Assembly on `Option O` -/
section Assembly
variable {C : Type v} [Fintype C] [DecidableEq C] [Nonempty C]
variable {O : Type u} [Fintype O] [DecidableEq O]
variable (I : PottsCI.PinningData (Option O) C) [DecidableRel I.graph.Adj]
  (d : Option O → ℕ∞) (L : ℕ)

def cz : C := Classical.arbitrary C

def proj (τ : Option O → C) : Option O → C :=
  fun v => if d v = ((L + 1 : ℕ) : ℕ∞) then τ v else cz

def fw (x : ℝ) (c : C) (τ : Option O → C) : ℝ := if τ none = c then I.weight x τ else 0

def obsv (o : O) (τ : Option O → C) : C := τ (some o)

def vmass (x : ℝ) (y : Option O → C) (c : C) (v : Option O) (c' : C) : ℝ :=
  ∑ τ, if proj d L τ = y ∧ τ v = c' then fw I x c τ else 0

theorem proj_idem (τ : Option O → C) : proj d L (proj d L τ) = proj d L τ := by
  funext v
  unfold proj
  split_ifs <;> rfl

theorem proj_eq_iff {y : Option O → C} (hy : proj d L y = y) (τ : Option O → C) :
    proj d L τ = y ↔ fibP d L y τ := by
  constructor
  · rintro rfl w hw
    unfold proj
    rw [if_pos hw]
  · intro h
    rw [← hy]
    funext v
    unfold proj
    split_ifs with hv
    · exact h v hv
    · rfl

theorem proj_fixed_of_eq {y τ : Option O → C} (h : proj d L τ = y) : proj d L y = y := by
  rw [← h, proj_idem]

theorem fibMass_eq_zero_of_not_fixed (x : ℝ) (c : C) {y : Option O → C}
    (hy : proj d L y ≠ y) : fibMass (fw I x c) (proj d L) y = 0 := by
  unfold fibMass
  apply Finset.sum_eq_zero
  intro τ _
  rw [if_neg]
  intro h
  exact hy (proj_fixed_of_eq d L h)

theorem fw_nonneg {x : ℝ} (hx : 0 ≤ x) (c : C) (τ : Option O → C) : 0 ≤ fw I x c τ := by
  unfold fw
  split_ifs
  · exact I.weight_nonneg hx τ
  · exact le_rfl

theorem sum_fw_pos {x : ℝ} (hx : 0 < x) (c : C) : 0 < ∑ τ, fw I x c τ := by
  classical
  let τ0 : Option O → C := fun v => c
  have hle := Finset.single_le_sum (f := fw I x c) (fun τ _ => fw_nonneg I hx.le c τ)
    (Finset.mem_univ τ0)
  have : fw I x c τ0 = I.weight x τ0 := by unfold fw; rw [if_pos rfl]
  rw [this] at hle
  exact lt_of_lt_of_le (I.weight_pos hx τ0) hle

theorem extW_pos {x : ℝ} (hx : 0 < x) (τ : Option O → C) (x₀ : Option O) :
    0 < extW d I L x₀ x τ := by
  unfold extW
  apply mul_pos (Finset.prod_pos fun u _ => pow_pos hx _)
  apply Finset.prod_pos
  intro e _
  induction e using Sym2.ind with
  | _ a c =>
    rw [PottsCI.PinningData.edgeFactor_mk]
    split_ifs
    · exact hx
    · exact one_pos

open Classical in
def Sfib (x : ℝ) (y : Option O → C) : ℝ :=
  ∑ τ, if fibP d L y τ then 1 * extW d I L none x τ else 0

open Classical in
theorem Sfib_pos {x : ℝ} (hx : 0 < x) (y : Option O → C) : 0 < Sfib I d L x y := by
  unfold Sfib
  have hyy : fibP d L y y := fun w _ => rfl
  have hnn : ∀ τ ∈ (univ : Finset (Option O → C)),
      0 ≤ (if fibP d L y τ then 1 * extW d I L none x τ else 0) := by
    intro τ _
    by_cases h : fibP d L y τ
    · rw [if_pos h, one_mul]; exact (extW_pos I d L hx τ none).le
    · rw [if_neg h]
  calc (0 : ℝ) < extW d I L none x y := extW_pos I d L hx y none
    _ = (if fibP d L y y then 1 * extW d I L none x y else 0) := by rw [if_pos hyy, one_mul]
    _ ≤ _ := Finset.single_le_sum (f := fun τ => if fibP d L y τ then 1 * extW d I L none x τ else 0)
        hnn (Finset.mem_univ y)


def rootInd (t : CavityTree C) (x : ℝ) (c : C) (ξ : t.Configuration) : ℝ :=
  (if t.rootColour ξ = c then 1 else 0) * t.configurationWeight x ξ

def levelInd (t : CavityTree C) (x : ℝ) (c : C) (k : ℕ) (ℓ : t.Level k) (c' : C)
    (ξ : t.Configuration) : ℝ :=
  (if t.rootColour ξ = c then 1 else 0) *
    ((if t.levelColour k ℓ ξ = c' then 1 else 0) * t.configurationWeight x ξ)

theorem sum_rootInd (t : CavityTree C) (x : ℝ) (c : C) :
    ∑ ξ, rootInd t x c ξ = t.rootWeight x c := by
  unfold rootInd CavityTree.rootWeight
  apply Finset.sum_congr rfl
  intro ξ _
  split_ifs <;> ring

theorem sum_levelInd {x : ℝ} (hx : 0 < x) (t : CavityTree C) (c : C) (k : ℕ) (ℓ : t.Level k)
    (c' : C) :
    ∑ ξ, levelInd t x c k ℓ c' ξ =
      t.levelMarginal k (t.rootConditionalLaw x hx c) ℓ c' * t.rootWeight x c := by
  have hr := (CavityTree.rootWeight_pos hx t c).ne'
  unfold levelInd CavityTree.levelMarginal CavityTree.rootConditionalLaw
  simp only
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ξ _
  split_ifs <;> simp [div_mul_cancel₀ _ hr]

section Hyp
variable (hx₀ : d none = 0)
  (hstep : ∀ u w, I.graph.Adj u w → d w ≤ d u + 1)
  (hlayer : ∀ (u w : Option O) (j : ℕ), I.graph.Adj u w → d u = j → d w = j → j ≤ L → False)
  (hpar : ∀ (z w w' : Option O) (j : ℕ), I.graph.Adj z w → I.graph.Adj z w' →
    d z = ((j + 1 : ℕ) : ℕ∞) → d w = j → d w' = j → j + 1 ≤ L → w = w')
include hx₀ hstep hlayer hpar

open Classical in
theorem fibMass_fixed {x : ℝ} (y : Option O → C) (hy : proj d L y = y) (c : C) :
    fibMass (fw I x c) (proj d L) y =
      Sfib I d L x y * (tree I.graph d I.boundaryCount y L none).rootWeight x c /
        (Fintype.card (tree I.graph d I.boundaryCount y L none).Configuration : ℝ) := by
  have hpt : ∀ τ, (if proj d L τ = y then fw I x c τ else 0) =
      (if fibP d L y τ then (fun _ => (1 : ℝ)) τ * extW d I L none x τ else 0) *
        rootInd (tree I.graph d I.boundaryCount y L none) x c
          (reader I.graph d I.boundaryCount y L none τ) := by
    intro τ
    by_cases hf : fibP d L y τ
    · rw [if_pos ((proj_eq_iff d L hy τ).mpr hf), if_pos hf]
      unfold rootInd fw
      rw [reader_root, weight_eq d y I L none hx₀ hstep hlayer hpar x τ hf]
      split_ifs <;> ring
    · rw [if_neg (fun h => hf ((proj_eq_iff d L hy τ).mp h)), if_neg hf, zero_mul]
  calc fibMass (fw I x c) (proj d L) y
      = ∑ τ, (if fibP d L y τ then (fun _ => (1 : ℝ)) τ * extW d I L none x τ else 0) *
          rootInd (tree I.graph d I.boundaryCount y L none) x c
            (reader I.graph d I.boundaryCount y L none τ) :=
        Finset.sum_congr rfl (fun τ _ => hpt τ)
    _ = _ := sum_factor d y I L none hx₀ hstep hlayer hpar (fun _ => 1) (fun _ _ _ => rfl) x _
    _ = _ := by rw [sum_rootInd]; rfl

open Classical in
theorem vmass_label {x : ℝ} (y : Option O → C) (hy : proj d L y = y) (c c' : C) (r : ℕ)
    (ℓ : (tree I.graph d I.boundaryCount y L none).Level r) :
    vmass I d L x y c (label I.graph d I.boundaryCount y L none r ℓ) c' =
      Sfib I d L x y * (∑ ξ, levelInd (tree I.graph d I.boundaryCount y L none) x c r ℓ c' ξ) /
        (Fintype.card (tree I.graph d I.boundaryCount y L none).Configuration : ℝ) := by
  have hpt : ∀ τ, (if proj d L τ = y ∧ τ (label I.graph d I.boundaryCount y L none r ℓ) = c'
      then fw I x c τ else 0) =
      (if fibP d L y τ then (fun _ => (1 : ℝ)) τ * extW d I L none x τ else 0) *
        levelInd (tree I.graph d I.boundaryCount y L none) x c r ℓ c'
          (reader I.graph d I.boundaryCount y L none τ) := by
    intro τ
    by_cases hf : fibP d L y τ
    · rw [if_pos hf]
      unfold levelInd fw
      rw [reader_root, levelColour_reader, weight_eq d y I L none hx₀ hstep hlayer hpar x τ hf]
      have hp : proj d L τ = y := (proj_eq_iff d L hy τ).mpr hf
      simp only [hp, true_and]
      split_ifs <;> ring
    · rw [if_neg (fun h => hf ((proj_eq_iff d L hy τ).mp h.1)), if_neg hf, zero_mul]
  calc vmass I d L x y c (label I.graph d I.boundaryCount y L none r ℓ) c'
      = ∑ τ, (if fibP d L y τ then (fun _ => (1 : ℝ)) τ * extW d I L none x τ else 0) *
          levelInd (tree I.graph d I.boundaryCount y L none) x c r ℓ c'
            (reader I.graph d I.boundaryCount y L none τ) :=
        Finset.sum_congr rfl (fun τ _ => hpt τ)
    _ = _ := sum_factor d y I L none hx₀ hstep hlayer hpar (fun _ => 1) (fun _ _ _ => rfl) x _
    _ = _ := rfl

open Classical in
theorem vmass_out {x : ℝ} (y : Option O → C) (hy : proj d L y = y) (c c' : C) (v : Option O)
    (hv : v ∉ desc I.graph d L none) :
    vmass I d L x y c v c' =
      (∑ τ, if fibP d L y τ then (fun τ : Option O → C => if τ v = c' then (1 : ℝ) else 0) τ *
        extW d I L none x τ else 0) *
        (tree I.graph d I.boundaryCount y L none).rootWeight x c /
        (Fintype.card (tree I.graph d I.boundaryCount y L none).Configuration : ℝ) := by
  have hpt : ∀ τ, (if proj d L τ = y ∧ τ v = c' then fw I x c τ else 0) =
      (if fibP d L y τ then (fun τ : Option O → C => if τ v = c' then (1 : ℝ) else 0) τ *
        extW d I L none x τ else 0) *
        rootInd (tree I.graph d I.boundaryCount y L none) x c
          (reader I.graph d I.boundaryCount y L none τ) := by
    intro τ
    by_cases hf : fibP d L y τ
    · rw [if_pos hf]
      unfold rootInd fw
      rw [reader_root, weight_eq d y I L none hx₀ hstep hlayer hpar x τ hf]
      have hp : proj d L τ = y := (proj_eq_iff d L hy τ).mpr hf
      simp only [hp, true_and]
      split_ifs <;> ring
    · rw [if_neg (fun h => hf ((proj_eq_iff d L hy τ).mp h.1)), if_neg hf, zero_mul]
  have hG1 : DepOn (fun τ : Option O → C => if τ v = c' then (1 : ℝ) else 0)
      ((desc I.graph d L none : Set (Option O)))ᶜ := by
    intro τ τ' h
    dsimp only
    rw [h v (by simpa using hv)]
  calc vmass I d L x y c v c'
      = ∑ τ, (if fibP d L y τ then (fun τ : Option O → C => if τ v = c' then (1 : ℝ) else 0) τ *
          extW d I L none x τ else 0) *
          rootInd (tree I.graph d I.boundaryCount y L none) x c
            (reader I.graph d I.boundaryCount y L none τ) :=
        Finset.sum_congr rfl (fun τ _ => hpt τ)
    _ = _ := sum_factor d y I L none hx₀ hstep hlayer hpar _ hG1 x _
    _ = _ := by rw [sum_rootInd]

theorem local_tv (Δ : ℕ) {x : ℝ} (hx : 0 < x) (A ρ : ℝ)
    (hTID : CI2ZF.Appendix.CLMM.TreeTID (C := C) Δ x hx A ρ) (k r : ℕ) (hL : L = k + 1)
    (hrL : r + 1 ≤ L) (hdegI : ∀ v, I.graph.degree v + ∑ c, I.boundaryCount v c ≤ Δ)
    (a b : C) (y : Option O → C) (hPa : 0 < fibMass (fw I x a) (proj d L) y) :
    ∑ o ∈ univ.filter (fun o : O => d (some o) = ((r + 1 : ℕ) : ℕ∞)),
      (1/2 : ℝ) * ∑ c', |condMass (fw I x a) (proj d L) obsv y o c' -
        condMass (fw I x b) (proj d L) obsv y o c'| ≤ A * ρ ^ (r + 1) := by
  classical
  have hy : proj d L y = y := by
    by_contra h
    rw [fibMass_eq_zero_of_not_fixed I d L x a h] at hPa
    exact lt_irrefl _ hPa
  have hcard : (0 : ℝ) < Fintype.card (tree I.graph d I.boundaryCount y L none).Configuration := by
    exact_mod_cast Fintype.card_pos
  have hS := Sfib_pos I d L hx y
  have hrw : ∀ c, 0 < (tree I.graph d I.boundaryCount y L none).rootWeight x c :=
    fun c => CavityTree.rootWeight_pos hx _ c
  have hin : ∀ (ℓ : (tree I.graph d I.boundaryCount y L none).Level (r + 1)) (c c' : C),
      vmass I d L x y c (label I.graph d I.boundaryCount y L none (r + 1) ℓ) c' /
        fibMass (fw I x c) (proj d L) y =
      (tree I.graph d I.boundaryCount y L none).levelMarginal (r + 1)
        ((tree I.graph d I.boundaryCount y L none).rootConditionalLaw x hx c) ℓ c' := by
    intro ℓ c c'
    rw [vmass_label I d L hx₀ hstep hlayer hpar y hy c c' (r + 1) ℓ,
      fibMass_fixed I d L hx₀ hstep hlayer hpar y hy c, sum_levelInd hx]
    have h1 := hS.ne'
    have h2 := (hrw c).ne'
    have h3 := hcard.ne'
    field_simp
  have hout : ∀ v, v ∉ desc I.graph d L none → ∀ c',
      vmass I d L x y a v c' / fibMass (fw I x a) (proj d L) y =
        vmass I d L x y b v c' / fibMass (fw I x b) (proj d L) y := by
    intro v hv c'
    rw [vmass_out I d L hx₀ hstep hlayer hpar y hy a c' v hv,
      vmass_out I d L hx₀ hstep hlayer hpar y hy b c' v hv,
      fibMass_fixed I d L hx₀ hstep hlayer hpar y hy a,
      fibMass_fixed I d L hx₀ hstep hlayer hpar y hy b,
      ratio_cancel hS.ne' (hrw a).ne' hcard.ne', ratio_cancel hS.ne' (hrw b).ne' hcard.ne']
  let g : Option O → ℝ := fun v => (1/2 : ℝ) * ∑ c', |vmass I d L x y a v c' /
    fibMass (fw I x a) (proj d L) y - vmass I d L x y b v c' / fibMass (fw I x b) (proj d L) y|
  have hg0 : ∀ v, 0 ≤ g v := fun v =>
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun c' _ => abs_nonneg _)
  have hgout : ∀ v, v ∉ desc I.graph d L none → g v = 0 := by
    intro v hv
    simp only [g, hout v hv, sub_self, abs_zero, Finset.sum_const_zero, mul_zero]
  have hgin : ∀ ℓ : (tree I.graph d I.boundaryCount y L none).Level (r + 1),
      g (label I.graph d I.boundaryCount y L none (r + 1) ℓ) =
      (1/2 : ℝ) * ∑ c', |(tree I.graph d I.boundaryCount y L none).levelMarginal (r + 1)
        ((tree I.graph d I.boundaryCount y L none).rootConditionalLaw x hx a) ℓ c' -
        (tree I.graph d I.boundaryCount y L none).levelMarginal (r + 1)
        ((tree I.graph d I.boundaryCount y L none).rootConditionalLaw x hx b) ℓ c'| := by
    intro ℓ
    simp only [g, hin]
  set Sites := univ.filter (fun o : O => d (some o) = ((r + 1 : ℕ) : ℕ∞))
  have hsub : (Sites.filter (fun o => some o ∈ desc I.graph d L none)).map
      Function.Embedding.some ⊆ univ.image (label I.graph d I.boundaryCount y L none (r + 1)) := by
    intro v hv
    rw [Finset.mem_map] at hv
    obtain ⟨o, ho, rfl⟩ := hv
    rw [Finset.mem_filter, Finset.mem_filter] at ho
    obtain ⟨ℓ, hℓ⟩ := label_surj I.graph d I.boundaryCount y L none 0 (by rw [hx₀]; rfl) (r + 1)
      (some o) ho.2 (by rw [ho.1.2]; congr 1; omega)
    exact Finset.mem_image.mpr ⟨ℓ, Finset.mem_univ _, hℓ⟩
  have hTV := (tree I.graph d I.boundaryCount y L none).levelTotalVariation x hx (r + 1) a b
  calc ∑ o ∈ Sites, (1/2 : ℝ) * ∑ c', |condMass (fw I x a) (proj d L) obsv y o c' -
        condMass (fw I x b) (proj d L) obsv y o c'|
      = ∑ o ∈ Sites, g (some o) := rfl
    _ = ∑ o ∈ Sites.filter (fun o => some o ∈ desc I.graph d L none), g (some o) := by
      refine (Finset.sum_filter_of_ne (fun o _ h => ?_)).symm
      by_contra hn
      exact h (hgout _ hn)
    _ = ∑ v ∈ (Sites.filter (fun o => some o ∈ desc I.graph d L none)).map
          Function.Embedding.some, g v := (Finset.sum_map _ Function.Embedding.some g).symm
    _ ≤ ∑ v ∈ univ.image (label I.graph d I.boundaryCount y L none (r + 1)), g v :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => hg0 v)
    _ ≤ ∑ ℓ, g (label I.graph d I.boundaryCount y L none (r + 1) ℓ) :=
      Finset.sum_image_le_of_nonneg (fun v _ => hg0 v)
    _ = (tree I.graph d I.boundaryCount y L none).levelTotalVariation x hx (r + 1) a b := by
      unfold CavityTree.levelTotalVariation
      apply Finset.sum_congr rfl
      intro ℓ _
      rw [hgin ℓ]
    _ ≤ A * ρ ^ (r + 1) := by
      subst hL
      exact hTID (down I.graph d none).card (I.boundaryCount none)
        (fun i => tree I.graph d I.boundaryCount y k (child I.graph d none i))
        (by have := card_down_le I.graph d none; have := hdegI none; omega)
        (fun i => tree_budget I.graph d I.boundaryCount y Δ hdegI k _ none 0
          ((mem_down I.graph d).mp (child_mem I.graph d none i)).1 (by rw [hx₀]; rfl)
          (down_dist I.graph d (by rw [hx₀]; rfl) (child_mem I.graph d none i)))
        r a b

theorem tv_bound (Δ : ℕ) {x : ℝ} (hx : 0 < x) (B ρ : ℝ) (K₀ : ℕ)
    (hRel : CI2ZF.Appendix.CLMM.TreeRelative (C := C) Δ x B ρ K₀) (k : ℕ) (hL : L = k + 1)
    (hK₀ : K₀ ≤ k + 2) (hB : 0 < B) (hρ : 0 < ρ) (hε1 : B * ρ ^ (k + 2) ≤ 1)
    (hdegI : ∀ v, I.graph.degree v + ∑ c, I.boundaryCount v c ≤ Δ) (a b : C) :
    (1/2 : ℝ) * ∑ y, |fibMass (fw I x a) (proj d L) y / ∑ τ, fw I x a τ -
      fibMass (fw I x b) (proj d L) y / ∑ τ, fw I x b τ| ≤ 2 * (B * ρ ^ (k + 2)) := by
  classical
  let P : (Option O → C) → C → ℝ := fun y c => (tree I.graph d I.boundaryCount y L none).probability x c
  let w : (Option O → C) → ℝ := fun y => if proj d L y = y then
    Sfib I d L x y * (tree I.graph d I.boundaryCount y L none).partition x /
      (Fintype.card (tree I.graph d I.boundaryCount y L none).Configuration : ℝ) else 0
  have hfac : ∀ y c, fibMass (fw I x c) (proj d L) y = P y c * w y := by
    intro y c
    by_cases hy : proj d L y = y
    · rw [fibMass_fixed I d L hx₀ hstep hlayer hpar y hy c]
      simp only [P, w, if_pos hy]
      rw [CavityTree.probability_eq_gibbs hx]
      have h1 := ((tree I.graph d I.boundaryCount y L none).partition_pos hx).ne'
      have h2 : (Fintype.card (tree I.graph d I.boundaryCount y L none).Configuration : ℝ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      field_simp
    · rw [fibMass_eq_zero_of_not_fixed I d L x c hy]
      simp only [w, if_neg hy, mul_zero]
  have hsum : ∀ c, ∑ τ, fw I x c τ = ∑ y, P y c * w y := by
    intro c
    rw [← sum_fibMass (fw I x c) (proj d L)]
    exact Finset.sum_congr rfl (fun y _ => hfac y c)
  have hP : ∀ y c, 0 < P y c := by
    intro y c
    simp only [P]
    rw [CavityTree.probability_eq_gibbs hx]
    exact div_pos (CavityTree.rootWeight_pos hx _ c) (CavityTree.partition_pos hx _)
  have hw : ∀ y, 0 ≤ w y := by
    intro y
    simp only [w]
    split_ifs
    · apply div_nonneg (mul_nonneg (Sfib_pos I d L hx y).le
        (CavityTree.partition_pos hx _).le) (Nat.cast_nonneg _)
    · exact le_rfl
  have hW : 0 < ∑ y, w y := by
    let y0 := proj d L (fun _ => (cz : C))
    have hy0 : proj d L y0 = y0 := proj_idem d L _
    have hpos : 0 < w y0 := by
      simp only [w, if_pos hy0]
      apply div_pos (mul_pos (Sfib_pos I d L hx y0) (CavityTree.partition_pos hx _))
      exact_mod_cast Fintype.card_pos
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun y _ => hw y) (Finset.mem_univ y0))
  have hratio : ∀ y y' c, |P y c / P y' c - 1| ≤ B * ρ ^ (k + 2) := by
    intro y y' c
    subst hL
    have hroot : (down I.graph d none).card + ∑ c, I.boundaryCount none c ≤ Δ := by
      have := card_down_le I.graph d none; have := hdegI none; omega
    have hch : ∀ z : Option O → C, ∀ i, (tree I.graph d I.boundaryCount z k
        (child I.graph d none i)).DegreeBudget Δ := fun z i =>
      tree_budget I.graph d I.boundaryCount z Δ hdegI k _ none 0
        ((mem_down I.graph d).mp (child_mem I.graph d none i)).1 (by rw [hx₀]; rfl)
        (down_dist I.graph d (by rw [hx₀]; rfl) (child_mem I.graph d none i))
    exact hRel k hK₀ (down I.graph d none).card (I.boundaryCount none)
      (fun i => tree I.graph d I.boundaryCount y k (child I.graph d none i))
      (fun i => tree I.graph d I.boundaryCount y' k (child I.graph d none i))
      (fun i => tree_sameDomain I.graph d I.boundaryCount y y' k _)
      (fun i => tree_agreement I.graph d I.boundaryCount y y' k _)
      hroot (hch y) (hch y') c
  have hmain := lemma520_abstract P w hP hw hW (B * ρ ^ (k + 2))
    (mul_nonneg hB.le (pow_nonneg hρ.le _)) hε1 hratio a b
  simp_rw [hfac, hsum]
  exact hmain

theorem main_bound (Δ : ℕ) {x : ℝ} (hx : 0 < x) (A B ρ : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hρ : 0 < ρ) (K₀ : ℕ)
    (hTID : CI2ZF.Appendix.CLMM.TreeTID (C := C) Δ x hx A ρ)
    (hRel : CI2ZF.Appendix.CLMM.TreeRelative (C := C) Δ x B ρ K₀)
    (k r : ℕ) (hL : L = k + 1) (hrL : r + 1 ≤ L) (hK₀ : K₀ ≤ k + 2)
    (hε1 : B * ρ ^ (k + 2) ≤ 1)
    (hdegI : ∀ v, I.graph.degree v + ∑ c, I.boundaryCount v c ≤ Δ) (a b : C) :
    ∑ o ∈ univ.filter (fun o : O => d (some o) = ((r + 1 : ℕ) : ℕ∞)),
      (1/2 : ℝ) * ∑ c, |siteMass (fw I x a) obsv o c - siteMass (fw I x b) obsv o c| ≤
      ((univ.filter (fun o : O => d (some o) = ((r + 1 : ℕ) : ℕ∞))).card : ℝ) *
        (2 * (B * ρ ^ (k + 2))) + A * ρ ^ (r + 1) := by
  classical
  have hfa := sum_fw_pos I hx a
  have hfb := sum_fw_pos I hx b
  have h519 := lemma519_abstract
    (fun y => fibMass (fw I x a) (proj d L) y / ∑ τ, fw I x a τ)
    (fun y => fibMass (fw I x b) (proj d L) y / ∑ τ, fw I x b τ)
    (condMass (fw I x a) (proj d L) obsv) (condMass (fw I x b) (proj d L) obsv)
    (siteMass (fw I x a) obsv) (siteMass (fw I x b) obsv)
    (fun y => div_nonneg (fibMass_nonneg _ _ (fw_nonneg I hx.le a) y) hfa.le)
    (fun y => div_nonneg (fibMass_nonneg _ _ (fw_nonneg I hx.le b) y) hfb.le)
    (by rw [← Finset.sum_div, sum_fibMass]; exact div_self hfa.ne')
    (fun y i c => condMass_nonneg _ _ _ (fw_nonneg I hx.le a) y i c)
    (fun y i c => condMass_nonneg _ _ _ (fw_nonneg I hx.le b) y i c)
    (fun y i => sum_condMass_le _ _ _ (fw_nonneg I hx.le a) y i)
    (fun y i => sum_condMass_le _ _ _ (fw_nonneg I hx.le b) y i)
    (fun i c => siteMass_decomp _ (proj d L) _ (fw_nonneg I hx.le a) i c)
    (fun i c => siteMass_decomp _ (proj d L) _ (fw_nonneg I hx.le b) i c)
    (univ.filter (fun o : O => d (some o) = ((r + 1 : ℕ) : ℕ∞))) (A * ρ ^ (r + 1))
    (mul_nonneg hA.le (pow_nonneg hρ.le _))
    (fun y hPy _ => local_tv I d L hx₀ hstep hlayer hpar Δ hx A ρ hTID k r hL hrL hdegI a b y
      (by
        have := hPy
        rw [div_pos_iff_of_pos_right hfa] at this
        exact this))
  have htv := tv_bound I d L hx₀ hstep hlayer hpar Δ hx B ρ K₀ hRel k hL hK₀ hB hρ hε1 hdegI a b
  refine h519.trans ?_
  have hc : (0 : ℝ) ≤ ((univ.filter (fun o : O => d (some o) = ((r + 1 : ℕ) : ℕ∞))).card : ℝ) :=
    Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left htv hc
  linarith

end Hyp
end Assembly


/-! ## The bridge to the literature statement -/
section Bridge
open PottsCI CI2ZF.Potts CI2ZF.Appendix.CLMM

variable {C : Type v} [Fintype C] [DecidableEq C] [Nonempty C]

open Classical in
theorem singleSiteMass_eq {O : Type u} [Fintype O]
    (I : PinningData (Option O) C) {x : ℝ} (hx : 0 < x) (a : C) (hx' : 0 ≤ x)
    (ha : 0 < (optionChildData I a).partition x) (o : O) (c : C) :
    singleSiteMass ((optionChildData I a).gibbs x hx' ha) o c = siteMass (fw I x a) obsv o c := by
  have hb : (0 : ℝ) < x ^ I.boundaryCount none a := pow_pos hx _
  have hden : ∑ τ, fw I x a τ = x ^ I.boundaryCount none a * (optionChildData I a).partition x := by
    rw [GraphResponseRoot.sum_colorings, Finset.sum_eq_single a]
    · unfold PinningData.partition
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      unfold fw
      have h2 : GraphResponseRoot.join a σ none = a := rfl
      rw [if_pos h2, GraphResponseRoot.parent_weight]
    · intro a' _ ha'
      apply Finset.sum_eq_zero
      intro σ _
      unfold fw
      exact if_neg ha'
    · intro h; exact absurd (Finset.mem_univ a) h
  have hnum : (∑ τ, if obsv o τ = c then fw I x a τ else 0) =
      x ^ I.boundaryCount none a *
        ∑ σ : O → C, if σ o = c then (optionChildData I a).weight x σ else 0 := by
    rw [GraphResponseRoot.sum_colorings, Finset.sum_eq_single a]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      unfold fw obsv
      have h1 : GraphResponseRoot.join a σ (some o) = σ o := rfl
      have h2 : GraphResponseRoot.join a σ none = a := rfl
      rw [h1, h2, if_pos rfl, GraphResponseRoot.parent_weight]
      split_ifs <;> ring
    · intro a' _ ha'
      apply Finset.sum_eq_zero
      intro σ _
      unfold fw
      have h2 : GraphResponseRoot.join a' σ none = a' := rfl
      rw [h2, if_neg ha']
      split_ifs <;> rfl
    · intro h; exact absurd (Finset.mem_univ a) h
  unfold singleSiteMass siteMass
  rw [hden, hnum, mul_div_mul_left _ _ hb.ne', Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [PinningData.gibbs]
  split_ifs <;> simp


theorem sphere_estimate_proof :
    ∀ (Δ : ℕ) (x : ℝ) (hx : 0 < x) (_hx1 : x ≤ 1)
      (A B ρ : ℝ) (_hΔ : 3 ≤ Δ) (_hA : 0 < A) (_hB : 0 < B)
      (_hρ : 0 < ρ) (_hρ1 : ρ < 1) (K₀ : ℕ),
      TreeTID (C := C) Δ x hx A ρ → TreeRelative (C := C) Δ x B ρ K₀ →
      ∀ (R K : ℕ), 2 ≤ R → R < K → K₀ ≤ K →
        Real.log B / (1 - ρ) ≤ K →
        FixedAmbientSphereDecay.{u,v} C Δ (2 * K + 2) R x
          (2 * B * ρ ^ K * (Δ : ℝ) ^ R + A * ρ ^ R) := by
  intro Δ x hx _hx1 A B ρ _hΔ hA hB hρ hρ1 K₀ hTID hRel R K hR hRK hK₀ hlog A' _ J hJd hJg O _ e pin hpin
  dsimp only
  intro a b hx' ha hb
  classical
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 2 := ⟨K - 2, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, R = r + 1 := ⟨R - 1, by omega⟩
  set I := restrictPinningData J e pin with hI
  let G := J.graph
  let d : Option O → ℕ∞ := fun v => G.edist (e none) (e v)
  have hadj : ∀ u w, I.graph.Adj u w ↔ G.Adj (e u) (e w) := fun u w => Iff.rfl
  have hg : ((2 * (k + 2) + 2 : ℕ) : ℕ∞) ≤ G.egirth := hJg
  have hx₀ : d none = 0 := SimpleGraph.edist_self
  have hstep : ∀ u w, I.graph.Adj u w → d w ≤ d u + 1 :=
    fun u w h => edist_adj_le G ((hadj u w).mp h)
  have hlayer : ∀ (u w : Option O) (j : ℕ), I.graph.Adj u w → d u = j → d w = j →
      j ≤ k + 1 → False := by
    intro u w j h hu hw hj
    have h1 := egirth_le_of_same_layer G ((hadj u w).mp h) hu hw
    have h2 : ((2 * (k + 2) + 2 : ℕ) : ℕ∞) ≤ ((2 * j + 1 : ℕ) : ℕ∞) := by
      refine hg.trans (h1.trans ?_); push_cast; exact le_rfl
    have h3 : 2 * (k + 2) + 2 ≤ 2 * j + 1 := by exact_mod_cast h2
    omega
  have hpar : ∀ (z w w' : Option O) (j : ℕ), I.graph.Adj z w → I.graph.Adj z w' →
      d z = ((j + 1 : ℕ) : ℕ∞) → d w = j → d w' = j → j + 1 ≤ k + 1 → w = w' := by
    intro z w w' j h h' hz hw hw' hj
    by_contra hne
    have hne' : e w ≠ e w' := fun heq => hne (e.injective heq)
    have h1 := egirth_le_of_two_parents G ((hadj z w).mp h) ((hadj z w').mp h') hz hw hw' hne'
    have h2 : ((2 * (k + 2) + 2 : ℕ) : ℕ∞) ≤ ((2 * j + 2 : ℕ) : ℕ∞) := by
      refine hg.trans (h1.trans ?_); push_cast; exact le_rfl
    have h3 : 2 * (k + 2) + 2 ≤ 2 * j + 2 := by exact_mod_cast h2
    omega
  have hdegI : ∀ v, I.graph.degree v + ∑ c, I.boundaryCount v c ≤ Δ :=
    CI2ZF.Appendix.CLMM.restrict_degreeBound J e pin hpin hJd
  have hε1 : B * ρ ^ (k + 2) ≤ 1 := small_of_log hB hρ hρ1 hlog
  have hmain := main_bound I d (k + 1) hx₀ hstep hlayer hpar Δ hx A B ρ hA hB hρ K₀ hTID hRel
    k r rfl (by omega) hK₀ hε1 hdegI a b
  -- the sphere count
  have hcount : ((univ.filter (fun o : O => d (some o) = ((r + 1 : ℕ) : ℕ∞))).card : ℝ) ≤
      (Δ : ℝ) ^ (r + 1) := by
    have hdegG : ∀ v, J.graph.degree v ≤ Δ := by
      intro v
      have := hJd v
      unfold PinningData.constraintDegree at this
      exact le_trans (Nat.le_add_right _ _) this
    have h1 : (univ.filter (fun o : O => d (some o) = ((r + 1 : ℕ) : ℕ∞))).card ≤
        (univ.filter (fun v : A' => G.edist (e none) v = ((r + 1 : ℕ) : ℕ∞))).card := by
      apply Finset.card_le_card_of_injOn (fun o => e (some o))
      · intro o ho
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ho ⊢
        exact ho
      · intro o _ o' _ h
        exact Option.some_injective _ (e.injective h)
    have h2 := card_sphere_le J.graph (e none) Δ hdegG (r + 1)
    exact_mod_cast h1.trans h2
  -- rewrite the ambient sphere influence
  have ha' : 0 < (optionChildData I a).partition x := by convert ha using 2
  have hb' : 0 < (optionChildData I b).partition x := by convert hb using 2
  have hrew : ambientSphereInfluence J.graph e (r + 1)
      ((optionChildData I a).gibbs x hx' ha') ((optionChildData I b).gibbs x hx' hb') =
      ∑ o ∈ univ.filter (fun o : O => d (some o) = ((r + 1 : ℕ) : ℕ∞)),
        (1/2 : ℝ) * ∑ c, |siteMass (fw I x a) obsv o c - siteMass (fw I x b) obsv o c| := by
    unfold ambientSphereInfluence
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro o _
    simp only [singleSiteMass_eq I hx a hx' ha', singleSiteMass_eq I hx b hx' hb']
    rfl
  have key : ambientSphereInfluence J.graph e (r + 1)
      ((optionChildData I a).gibbs x hx' ha') ((optionChildData I b).gibbs x hx' hb') ≤
      2 * B * ρ ^ (k + 2) * (Δ : ℝ) ^ (r + 1) + A * ρ ^ (r + 1) := by
    rw [hrew]
    refine hmain.trans ?_
    have hBK : 0 ≤ 2 * (B * ρ ^ (k + 2)) := by positivity
    have := mul_le_mul_of_nonneg_right hcount hBK
    nlinarith
  convert key using 3

end Bridge

end
end CI2ZF.Appendix.CLMM.Eq10

namespace CI2ZF.Appendix.CLMM
universe u v

/-- CLMM Equation (10) is proved (`Eq10.sphere_estimate_proof`), so the
`Literature` bundle of the CLMM transfer holds for every colour type. -/
theorem literature (C : Type v) [Fintype C] [DecidableEq C] [Nonempty C] :
    Literature.{u,v} C :=
  ⟨Eq10.sphere_estimate_proof⟩

end CI2ZF.Appendix.CLMM
