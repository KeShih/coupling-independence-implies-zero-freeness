import ZeroFreeness.Coupling.Foundations.FiniteCoupling
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! Independent finite coins and their deterministic common-noise couplings. -/

namespace ZeroFreeness

attribute [local instance] Classical.propDecidable

open PottsCI PottsCI.FinDist
open scoped BigOperators
noncomputable section

variable {K A B : Type*} [Fintype K] [DecidableEq K] [Fintype A] [Fintype B]

/-- The exact product law of finitely many finite probability distributions. -/
def productLaw (p : K → FinDist A) : FinDist (K → A) where
  w ω := ∏ k, (p k).w (ω k)
  nonneg ω := Finset.prod_nonneg fun k _ => (p k).nonneg (ω k)
  sum_one := by
    rw [← Fintype.prod_sum]
    simp only [FinDist.sum_one, Finset.prod_const_one]

/-- Pushforward commutes with coordinatewise maps of independent variables. -/
theorem map_productLaw (p : K → FinDist A) (f : K → A → B) :
    mapLaw (productLaw p) (fun ω k => f k (ω k)) =
      productLaw (fun k => mapLaw (p k) (f k)) := by
  classical
  apply FinDist.ext
  funext y
  dsimp only [mapLaw, FinDist.bind, FinDist.pure, productLaw]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [mul_ite, mul_one, mul_zero, Fintype.prod_ite_zero, funext_iff]

/-- A Bernoulli law, including parameters zero and one. -/
def bernoulliLaw (t : ℝ) (ht : t ∈ Set.Icc 0 1) : FinDist Bool where
  w b := if b then t else 1 - t
  nonneg b := by
    cases b
    · exact sub_nonneg.mpr ht.2
    · exact ht.1
  sum_one := by simp

/-- Every physical constraint receives an independent common coin. -/
def commonCoinLaw (t : ℝ) (ht : t ∈ Set.Icc 0 1) : FinDist (K → Bool) :=
  productLaw (fun _ => bernoulliLaw t ht)

/-- Coupling from a single source of randomness, with exact marginals. -/
def commonNoiseCoupling {S T U : Type*} [Fintype S] [Fintype T] [Fintype U]
    (p : FinDist S) (f : S → T) (g : S → U) :
    Coupling (mapLaw p f) (mapLaw p g) :=
  mapCoupling (Coupling.diag p) f g

theorem expectReal_mapLaw (p : FinDist A) (f : A → B) (g : B → ℝ) :
    expectReal (mapLaw p f) g = expectReal p (fun a => g (f a)) := by
  classical
  simp only [expectReal, mapLaw, FinDist.bind_w, FinDist.pure]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [mul_ite]

theorem mapLaw_comp {D : Type*} [Fintype D] (p : FinDist A) (f : A → B) (g : B → D) :
    mapLaw (mapLaw p f) g = mapLaw p (fun a => g (f a)) := by
  apply FinDist.ext
  funext d
  simp only [mapLaw, FinDist.bind_w, FinDist.pure]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single (f a)]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem mapLaw_bind {D : Type*} [Fintype D] (p : FinDist A)
    (f : A → B) (kernel : B → FinDist D) :
    (mapLaw p f).bind kernel = p.bind (fun a => kernel (f a)) := by
  apply FinDist.ext
  funext d
  exact expectReal_mapLaw p f (fun b => (kernel b).w d)

theorem expectReal_productLaw (p : K → FinDist A) (f : K → A → ℝ) :
    expectReal (productLaw p) (fun ω => ∏ k, f k (ω k)) =
      ∏ k, expectReal (p k) (f k) := by
  simp only [expectReal, productLaw, ← Finset.prod_mul_distrib, Fintype.prod_sum]

theorem expectReal_product_coordinate (p : K → FinDist A) (k : K) (f : A → ℝ) :
    expectReal (productLaw p) (fun ω => f (ω k)) = expectReal (p k) f := by
  have h := expectReal_productLaw p (fun i a => if i = k then f a else 1)
  simpa [expectReal, Finset.prod_ite_eq, FinDist.sum_one] using h

theorem mapLaw_equiv_w (p : FinDist A) (e : A ≃ B) (b : B) :
    (mapLaw p e).w b = p.w (e.symm b) := by
  simp only [mapLaw, FinDist.bind_w, FinDist.pure]
  have he (a : A) : b = e a ↔ a = e.symm b := by
    constructor
    · intro h
      exact (e.symm_apply_apply a).symm.trans (congrArg e.symm h.symm)
    · intro h
      simp [h]
  simp_rw [he, mul_ite, mul_one, mul_zero]
  simp

/-- Bit vectors and successful-coin subsets describe the same finite space. -/
def bitsEquivFinset : (K → Bool) ≃ Finset K where
  toFun ω := Finset.univ.filter (fun k => ω k = true)
  invFun s k := decide (k ∈ s)
  left_inv ω := by
    funext k
    simp
  right_inv s := by ext k; simp

theorem expected_successes_in (t : ℝ) (ht : t ∈ Set.Icc 0 1) (s : Finset K) :
    expectReal (commonCoinLaw t ht)
      (fun ω => ∑ k ∈ s, if ω k then (1 : ℝ) else 0) = s.card * t := by
  unfold expectReal
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h (k : K) : (∑ ω : K → Bool, (commonCoinLaw t ht).w ω *
      (if ω k then (1 : ℝ) else 0)) = t := by
    have hm := expectReal_product_coordinate (fun _ : K => bernoulliLaw t ht) k
      (fun b : Bool => if b then (1 : ℝ) else 0)
    simpa [commonCoinLaw, expectReal, bernoulliLaw] using hm
  simp_rw [h]
  simp

end
end ZeroFreeness
