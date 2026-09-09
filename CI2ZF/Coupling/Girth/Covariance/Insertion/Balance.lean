import CI2ZF.Coupling.Girth.Covariance.Insertion.Law
import CI2ZF.Coupling.Girth.Spectral.Graph.PositivePoincare

/-! Independent-set disintegration from the actual local Gibbs balance
identities. No conditional-product conclusion is postulated. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {Ω U O C : Type*} [Fintype Ω] [Fintype U] [Fintype O] [Fintype C]
  [DecidableEq U] [DecidableEq C] [Nonempty C]

namespace InsertionBalance

theorem product_swap (p : U → FinDist C) (i : U) (α : U → C) (c : C) :
    (CI2ZF.productLaw p).w (Function.update α i c) * (p i).w (α i) =
      (CI2ZF.productLaw p).w α * (p i).w c := by
  change (∏ j, (p j).w (Function.update α i c j)) * _ = (∏ j, (p j).w (α j)) * _
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  rw [Function.update_self]
  have he : (∏ j ∈ Finset.univ.erase i, (p j).w (Function.update α i c j)) =
      ∏ j ∈ Finset.univ.erase i, (p j).w (α j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [he]
  ring

variable (μ : FinDist (Ω × ((U → C) × O))) (π : Ω → U → FinDist C)

/-- The exterior weight after the independent coordinates are summed out. -/
def exteriorMass (ξ : Ω) (o : O) : ℝ := ∑ α : U → C, μ.w (ξ,(α,o))

def LocalBalance : Prop := ∀ ξ α o u c,
  μ.w (ξ,(Function.update α u c,o)) * (π ξ u).w (α u) =
    μ.w (ξ,(α,o)) * (π ξ u).w c

theorem weight_factorization (hπ : ∀ ξ u c, 0 < (π ξ u).w c)
    (hbal : LocalBalance μ π) (ξ : Ω) (α : U → C) (o : O) :
    μ.w (ξ,(α,o)) = exteriorMass μ ξ o * (CI2ZF.productLaw (π ξ)).w α := by
  let ρ := CI2ZF.productLaw (π ξ)
  have hρ (τ : U → C) : 0 < ρ.w τ := Finset.prod_pos fun u _ => hπ ξ u (τ u)
  let r : (U → C) → ℝ := fun τ => μ.w (ξ,(τ,o)) / ρ.w τ
  have hu (τ : U → C) (u : U) (c : C) : r (Function.update τ u c) = r τ := by
    apply (div_eq_div_iff (hρ _).ne' (hρ _).ne').mpr
    apply mul_right_cancel₀ (hπ ξ u (τ u)).ne'
    calc
      (μ.w (ξ,(Function.update τ u c,o)) * ρ.w τ) * (π ξ u).w (τ u) =
          (μ.w (ξ,(Function.update τ u c,o)) * (π ξ u).w (τ u)) * ρ.w τ := by ring
      _ = (μ.w (ξ,(τ,o)) * (π ξ u).w c) * ρ.w τ := by rw [hbal]
      _ = μ.w (ξ,(τ,o)) * (ρ.w (Function.update τ u c) * (π ξ u).w (τ u)) := by
        rw [product_swap]
        ring
      _ = _ := by ring
  have hcross (τ : U → C) : μ.w (ξ,(τ,o)) * ρ.w α = μ.w (ξ,(α,o)) * ρ.w τ := by
    exact (div_eq_div_iff (hρ τ).ne' (hρ α).ne').mp (update_invariant_constant r hu τ α)
  have hs := congrArg (fun k : (U → C) → ℝ => ∑ τ, k τ) (funext hcross)
  simp only [← Finset.sum_mul, ← Finset.mul_sum, ρ.sum_one, mul_one] at hs
  exact hs.symm

def shellLaw : FinDist Ω where
  w ξ := ∑ α : U → C, ∑ o : O, μ.w (ξ,(α,o))
  nonneg ξ := Finset.sum_nonneg fun α _ => Finset.sum_nonneg fun o _ => μ.nonneg _
  sum_one := by simpa only [Fintype.sum_prod_type] using μ.sum_one

theorem sum_exteriorMass (ξ : Ω) : (∑ o, exteriorMass μ ξ o) = (shellLaw μ).w ξ :=
  Finset.sum_comm

def exteriorLaw (hS : ∀ ξ, 0 < (shellLaw μ).w ξ) (ξ : Ω) : FinDist O where
  w o := exteriorMass μ ξ o / (shellLaw μ).w ξ
  nonneg o := div_nonneg (Finset.sum_nonneg fun α _ => μ.nonneg _) (hS ξ).le
  sum_one := by rw [← Finset.sum_div, sum_exteriorMass, div_self (hS ξ).ne']

def model (hS : ∀ ξ, 0 < (shellLaw μ).w ξ) : InsertionModel Ω U O C where
  shell := shellLaw μ
  cavity := π
  exterior := exteriorLaw μ hS

/-- The literal finite distribution equals the second-layer product
model as soon as its local update balances have been verified. -/
theorem law_eq_model (hπ : ∀ ξ u c, 0 < (π ξ u).w c)
    (hbal : LocalBalance μ π) (hS : ∀ ξ, 0 < (shellLaw μ).w ξ) :
    μ = (model μ π hS).law := by
  apply FinDist.ext
  funext z
  rcases z with ⟨ξ,α,o⟩
  change μ.w (ξ,(α,o)) = (shellLaw μ).w ξ *
    ((CI2ZF.productLaw (π ξ)).w α * (exteriorMass μ ξ o / (shellLaw μ).w ξ))
  rw [weight_factorization μ π hπ hbal]
  field_simp [(hS ξ).ne']

end InsertionBalance
end
end CI2ZF.Appendix.Girth
