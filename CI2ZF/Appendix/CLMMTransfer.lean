import CI2ZF.Appendix.GirthLevels
import CI2ZF.Appendix.CLMMAmbient
import CI2ZF.OptionPinning
import CI2ZF.PottsModel
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The eventual-depth form of the CLMM large-girth transfer

The two literature inputs are the precise sphere estimate in CLMM2023,
Equation (10), proved from Lemmas 5.19 and 5.20, and Lemma 5.13. They are
stated for the actual finite Potts laws, on spheres of the fixed base
graph under all further pinnings. Neither field assumes tree decay,
an eventual-depth transfer theorem, or the resulting uniform coupling
bound. The choice of both radii, including the extra burn-in, is proved.

Source: https://arxiv.org/html/2304.01954v3, Sections 5.2--5.4 and
Remark 5.11. Positive activities make every colour globally feasible.
-/

namespace CI2ZF.Appendix.CLMM
open scoped BigOperators
open PottsCI PottsCI.FinDist CI2ZF.Potts Filter Set
open CI2ZF.Appendix.Girth

noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

universe u v
variable {C : Type v} [Fintype C] [DecidableEq C] [Nonempty C]

/-- Equality of the free tree and the pinned domain. Pinned leaves are
individually labelled; equal total counts permit different leaf colours. -/
inductive SameDomain : CavityTree C → CavityTree C → Prop where
  | node (d : ℕ) (b b' : C → ℕ) (t t' : Fin d → CavityTree C)
      (hb : (∑ c, b c) = ∑ c, b' c) (ht : ∀ i, SameDomain (t i) (t' i)) :
      SameDomain (.node d b t) (.node d b' t')

def TreeTID (Δ : ℕ) (x : ℝ) (hx : 0 < x) (A ρ : ℝ) : Prop :=
  ∀ (d : ℕ) (b : C → ℕ) (t : Fin d → CavityTree C),
    d + (∑ c, b c) ≤ Δ → (∀ i, (t i).DegreeBudget Δ) →
    ∀ (k : ℕ) (a z : C),
      (CavityTree.node d b t).levelTotalVariation x hx (k + 1) a z ≤ A * ρ ^ (k + 1)

/-- Ratio-form SSM at the chosen depth `k+2`, on a fixed pinned domain. -/
def TreeRelative (Δ : ℕ) (x A ρ : ℝ) (K₀ : ℕ) : Prop :=
  ∀ (k : ℕ), K₀ ≤ k + 2 → ∀ (d : ℕ) (b : C → ℕ) (t t' : Fin d → CavityTree C),
    (∀ i, SameDomain (t i) (t' i)) → (∀ i, CavityTree.Agreement k (t i) (t' i)) →
    d + (∑ c, b c) ≤ Δ → (∀ i, (t i).DegreeBudget Δ) →
    (∀ i, (t' i).DegreeBudget Δ) → ∀ c,
      |(CavityTree.node d b t).probability x c /
        (CavityTree.node d b t').probability x c - 1| ≤ A * ρ ^ (k + 2)

/-- Precisely isolated literature inputs. The first field is CLMM (10)
at the explicitly chosen cutting depth; the second is Lemma 5.13.
All members here have positive unary Potts weights and hence satisfy (7).
The same-domain clause in `TreeRelative` is part of Definition 5.7. -/
structure Literature (C : Type v) [Fintype C] [DecidableEq C] [Nonempty C] : Prop where
  sphere_estimate : ∀ (Δ : ℕ) (x : ℝ) (hx : 0 < x) (_hx1 : x ≤ 1)
    (A B ρ : ℝ) (_hΔ : 3 ≤ Δ) (_hA : 0 < A) (_hB : 0 < B)
    (_hρ : 0 < ρ) (_hρ1 : ρ < 1) (K₀ : ℕ),
    TreeTID (C := C) Δ x hx A ρ → TreeRelative (C := C) Δ x B ρ K₀ →
    ∀ (R K : ℕ), 2 ≤ R → R < K → K₀ ≤ K →
      Real.log B / (1 - ρ) ≤ K →
      FixedAmbientSphereDecay.{u,v} C Δ (2 * K + 2) R x
        (2 * B * ρ ^ K * (Δ : ℝ) ^ R + A * ρ ^ R)
  sphere_to_coupling : ∀ (Δ g R : ℕ) (x ε : ℝ), 3 ≤ Δ → 2 ≤ R →
    ∀ (hx : 0 < x), x ≤ 1 → 0 < ε → ε ≤ 1 / (8 * R * Real.log Δ) →
    FixedAmbientSphereDecay.{u,v} C Δ g R x ε →
    ∀ {O : Type u} [Fintype O] (I : PinningData (Option O) C),
      I.DegreeBound Δ → (g : ℕ∞) ≤ I.graph.egirth → ∀ (a b : C)
      (ha : 0 < (optionChildData I a).partition x)
      (hb : 0 < (optionChildData I b).partition x),
      W ham ((optionChildData I a).gibbs x hx.le ha)
        ((optionChildData I b).gibbs x hx.le hb) ≤ 2 * (Δ : ℝ) ^ R

/-- Exponential decay beats all fixed influence-radius lower bounds. -/
theorem choose_influence_radius {A ρ Δ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hΔ : 1 < Δ) (R₀ : ℕ) :
    ∃ R : ℕ, R₀ ≤ R ∧ 2 ≤ R ∧ A * ρ ^ R ≤ 1 / (16 * R * Real.log Δ) := by
  have hl := Real.log_pos hΔ
  have ht : Tendsto (fun n : ℕ => (16 * Real.log Δ * A) * ((n : ℝ) * ρ ^ n))
      atTop (nhds 0) := by
    simpa using (tendsto_self_mul_const_pow_of_lt_one hρ hρ1).const_mul (16 * Real.log Δ * A)
  have he := ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨R, hsmall⟩ := (eventually_atTop.1 he)
  let r := max (max R R₀) 2
  have hrR : R ≤ r := le_trans (le_max_left _ _) (le_max_left _ _)
  have hr0 : R₀ ≤ r := le_trans (le_max_right _ _) (le_max_left _ _)
  have hr2 : 2 ≤ r := le_max_right _ _
  refine ⟨r, hr0, hr2, ?_⟩
  apply (le_div_iff₀ (by positivity : 0 < 16 * (r : ℝ) * Real.log Δ)).2
  nlinarith [hsmall r hrR]

/-- Once `R` is fixed, the cutting depth can satisfy the relative-SSM
burn-in, CLMM's logarithmic condition, and every further fixed lower bound. -/
theorem choose_cutting_depth {B ρ Δ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hΔ : 1 < Δ) (R : ℕ) (hR : 2 ≤ R) (K₀ Kmin : ℕ) :
    ∃ K : ℕ, K₀ ≤ K ∧ Kmin ≤ K ∧ R < K ∧
      Real.log B / (1 - ρ) ≤ K ∧
      2 * B * ρ ^ K * Δ ^ R ≤ 1 / (16 * R * Real.log Δ) := by
  have hl := Real.log_pos hΔ
  have heps : 0 < 1 / (16 * (R : ℝ) * Real.log Δ) := by positivity
  have ht : Tendsto (fun n : ℕ => 2 * B * ρ ^ n * Δ ^ R) atTop (nhds 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1).const_mul (2 * B)).mul_const (Δ ^ R)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds heps))
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.log B / (1 - ρ))
  let K := max (max (max N K₀) Kmin) (max (R + 1) L)
  have hN' : N ≤ K := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have h0 : K₀ ≤ K := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hmin : Kmin ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  have hR' : R + 1 ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hL' : L ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
  exact ⟨K, h0, hmin, by omega, hL.le.trans (by exact_mod_cast hL'), (hN K hN').le⟩

/-- The paper's eventual-depth transfer, uniform over any activity set.
`2 Δ^R` is the actual transport bound supplied by Lemma 5.13. -/
theorem eventual_transfer (external : Literature.{u,v} C) (Δ : ℕ) (hΔ : 3 ≤ Δ)
    (A B ρ : ℝ) (hA : 0 < A) (hB : 0 < B) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (K₀ : ℕ) (J : Set ℝ)
    (hJ : ∀ x ∈ J, 0 < x ∧ x ≤ 1)
    (htree : ∀ (x : ℝ) (hxJ : x ∈ J),
      TreeTID (C := C) Δ x (hJ x hxJ).1 A ρ ∧ TreeRelative (C := C) Δ x B ρ K₀) :
    ∃ (g : ℕ) (cost : ℝ), 3 ≤ g ∧ 0 ≤ cost ∧
      ∀ (x : ℝ) (hxJ : x ∈ J), ∀ {O : Type u} [Fintype O] (I : PinningData (Option O) C),
        I.DegreeBound Δ → (g : ℕ∞) ≤ I.graph.egirth → ∀ (a b : C)
        (ha : 0 < (optionChildData I a).partition x)
        (hb : 0 < (optionChildData I b).partition x),
        W ham ((optionChildData I a).gibbs x (hJ x hxJ).1.le ha)
          ((optionChildData I b).gibbs x (hJ x hxJ).1.le hb) ≤ cost := by
  have hd : (1 : ℝ) < Δ := by exact_mod_cast (show 1 < Δ by omega)
  obtain ⟨R, _, hR, hsmallR⟩ := choose_influence_radius (A := A) hρ.le hρ1 hd 2
  obtain ⟨K, hK₀, _, hRK, hlog, hsmallK⟩ := choose_cutting_depth (B := B) hρ.le hρ1 hd R hR K₀ 2
  let ε := 2 * B * ρ ^ K * (Δ : ℝ) ^ R + A * ρ ^ R
  have heps : ε ≤ 1 / (8 * (R : ℝ) * Real.log Δ) := by
    have hhalf : 1 / (16 * (R : ℝ) * Real.log Δ) +
        1 / (16 * (R : ℝ) * Real.log Δ) = 1 / (8 * (R : ℝ) * Real.log Δ) := by ring
    exact (add_le_add hsmallK hsmallR).trans_eq hhalf
  refine ⟨2 * K + 2, 2 * (Δ : ℝ) ^ R, by omega, by positivity, ?_⟩
  intro x hx O _ I hI hg a b ha hb
  have hs : FixedAmbientSphereDecay.{u,v} C Δ (2 * K + 2) R x ε :=
    external.sphere_estimate Δ x (hJ x hx).1 (hJ x hx).2 A B ρ hΔ hA hB hρ hρ1
    K₀ (htree x hx).1 (htree x hx).2 R K hR hRK hK₀ hlog
  exact external.sphere_to_coupling Δ (2 * K + 2) R x ε hΔ hR
    (hJ x hx).1 (hJ x hx).2 (by dsimp [ε]; positivity) heps hs I hI hg a b ha hb

end
end CI2ZF.Appendix.CLMM
