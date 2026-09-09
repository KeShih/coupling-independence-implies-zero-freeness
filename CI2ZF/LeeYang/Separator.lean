import CI2ZF.LeeYang.Model
import CI2ZF.Potts.Transfer.SeparatorInsidePolynomial

/-! Exact hard-colouring field factorization over a genuine graph separator.
All inside and shell field factors belong to the local coefficient; the
remaining factor is the actual field partition of the smaller exterior. -/
namespace CI2ZF.LeeYang
open scoped BigOperators
open PottsCI CI2ZF.Potts CI2ZF.Potts.Separator
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {U S O C : Type*} [Fintype U] [Fintype S] [Fintype O] [Fintype C]

def insideField (ℓ : Vertex U S O → C → ℂ) : U ⊕ S → C → ℂ :=
  fun v => ℓ (insideEmbedding v)

def exteriorField (ℓ : Vertex U S O → C → ℂ) : O → C → ℂ :=
  fun o => ℓ (Sum.inr (Sum.inr o))

/-- The hard inside indicator includes the shell's constraints; its field
monomial includes every inside and shell vertex exactly once. -/
def insideFieldWeight (I : PinningData (Vertex U S O) C)
    (ℓ : Vertex U S O → C → ℂ) (α : U → C) (ξ : S → C) : ℂ :=
  ((insideWeight I (0 : ℝ) α ξ : ℝ) : ℂ) *
    ((∏ u, ℓ (Sum.inl u) (α u)) * ∏ s, ℓ (Sum.inr (Sum.inl s)) (ξ s))

def insideFieldPartition (I : PinningData (Vertex U S O) C)
    (ℓ : Vertex U S O → C → ℂ) (ξ : S → C) : ℂ :=
  ∑ α : U → C, insideFieldWeight I ℓ α ξ

theorem fieldWeight_join (I : PinningData (Vertex U S O) C) (hsep : Separates I)
    (ℓ : Vertex U S O → C → ℂ) (α : U → C) (ξ : S → C) (ζ : O → C) :
    fieldWeight I ℓ (join α ξ ζ) =
      insideFieldWeight I ℓ α ξ * fieldWeight (exteriorData I ξ) (exteriorField ℓ) ζ := by
  have hw : I.weight 0 (join α ξ ζ) =
      insideWeight I (0 : ℝ) α ξ * (exteriorData I ξ).weight 0 ζ := by
    rw [← weight_real, weight_join I hsep, exteriorWeight_eq_pinningProductWeight I hsep]
    rfl
  rw [fieldWeight_eq_hardWeight_mul, hw, Complex.ofReal_mul, fieldWeight_eq_hardWeight_mul]
  simp only [insideFieldWeight,
    Fintype.prod_sum_type, join, Sum.elim_inl, Sum.elim_inr, exteriorField]
  ring

/-- This is the field separator identity from the original finite sum,
with an actual inherited exterior datum and no assumed factorization. -/
theorem fieldPartition_separator (I : PinningData (Vertex U S O) C)
    (hsep : Separates I) (ℓ : Vertex U S O → C → ℂ) :
    fieldPartition I ℓ = ∑ ξ : S → C,
      insideFieldPartition I ℓ ξ * fieldPartition (exteriorData I ξ) (exteriorField ℓ) := by
  let : DecidableEq (Vertex U S O) := fun _ _ => Classical.propDecidable _
  unfold fieldPartition
  rw [Fintype.sum_equiv coloringEquiv (fun σ => fieldWeight I ℓ σ)
    (fun p : (S → C) × ((U → C) × (O → C)) => fieldWeight I ℓ (join p.2.1 p.1 p.2.2))
    (fun σ => by congr 1; exact (coloringEquiv.left_inv σ).symm)]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ξ _
  simp_rw [fieldWeight_join I hsep]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  rfl

@[simp] theorem insideField_one :
    insideField (oneField : Vertex U S O → C → ℂ) = oneField := rfl

@[simp] theorem exteriorField_one :
    exteriorField (oneField : Vertex U S O → C → ℂ) = oneField := rfl

@[simp] theorem insideFieldPartition_one (I : PinningData (Vertex U S O) C) (ξ : S → C) :
    insideFieldPartition I oneField ξ = ((insidePartition I (0 : ℝ) ξ : ℝ) : ℂ) := by
  simp [insideFieldPartition, insideFieldWeight, oneField, insidePartition]

end
end CI2ZF.LeeYang
