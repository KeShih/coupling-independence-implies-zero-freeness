import ZeroFreeness.Coupling.Foundations.CommonCoins

/-! Restricting independent common coins to any injected subset of labels. -/

namespace ZeroFreeness
open PottsCI PottsCI.FinDist
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section

variable {K L A : Type*} [Fintype K] [Fintype L]
  [DecidableEq K] [DecidableEq L] [Fintype A]

theorem expectReal_product_embedding (p : L → FinDist A) (e : K ↪ L)
    (f : K → A → ℝ) :
    expectReal (productLaw p) (fun ω => ∏ k, f k (ω (e k))) =
      ∏ k, expectReal (p (e k)) (f k) := by
  let g (l : L) (a : A) : ℝ := ∏ k : K, if e k = l then f k a else 1
  have hprod (ω : L → A) : (∏ l : L, g l (ω l)) = ∏ k : K, f k (ω (e k)) := by
    unfold g
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro k _
    simp
  have hcoord (l : L) : expectReal (p l) (g l) =
      ∏ k : K, if e k = l then expectReal (p l) (f k) else 1 := by
    by_cases hl : ∃ k : K, e k = l
    · obtain ⟨k, rfl⟩ := hl
      have he (j : K) : e j = e k ↔ j = k := e.injective.eq_iff
      simp [g, he]
    · have he (k : K) : e k ≠ l := fun h => hl ⟨k, h⟩
      simp [g, he]
  have h := expectReal_productLaw p g
  simp_rw [hprod, hcoord] at h
  rw [Finset.prod_comm] at h
  simpa using h

/-- A coordinate restriction of a product law is exactly the corresponding
product of marginals, even when the complement is empty. -/
theorem map_productLaw_embedding (p : L → FinDist A) (e : K ↪ L) :
    mapLaw (productLaw p) (fun ω k => ω (e k)) = productLaw (fun k => p (e k)) := by
  apply FinDist.ext
  funext x
  have h := expectReal_product_embedding p e (fun k a => if x k = a then (1 : ℝ) else 0)
  have he (ω : L → A) : (∏ k : K, if x k = ω (e k) then (1 : ℝ) else 0) =
      if x = (fun k => ω (e k)) then (1 : ℝ) else 0 := by
    simp [Fintype.prod_boole, funext_iff]
  simp_rw [he] at h
  simpa [expectReal, mapLaw, FinDist.bind_w, FinDist.pure, productLaw, mul_ite] using h

/-- Public common-coin restriction interface used when adding a labelled
boundary constraint. -/
theorem map_commonCoinLaw_embedding (e : K ↪ L) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    mapLaw (commonCoinLaw (K := L) t ht) (fun ω k => ω (e k)) =
      commonCoinLaw (K := K) t ht :=
  map_productLaw_embedding (fun _ : L => bernoulliLaw t ht) e

end
end ZeroFreeness
