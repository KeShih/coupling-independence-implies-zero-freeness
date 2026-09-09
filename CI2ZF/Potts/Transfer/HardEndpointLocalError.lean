import CI2ZF.Potts.Transfer.BoundedLocalFamily

/-! Uniform additive errors at the hard endpoint. No base nonvanishing
is needed, so defective inside terms are covered as well. -/
namespace CI2ZF
open PottsCI
open scoped BigOperators
noncomputable section

theorem monomial_error_zero (z : ℂ) (hz : ‖z‖ ≤ 1) (k : ℕ) :
    ‖z ^ k - (0 : ℂ) ^ k‖ ≤ ‖z‖ := by
  cases k with
  | zero => simp
  | succ k =>
    simp only [pow_succ, mul_zero, sub_zero, norm_mul, norm_pow]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg z) hz) (norm_nonneg z)).trans_eq (one_mul _)

theorem sum_monomials_error_zero {S : Type*} [Fintype S]
    (f : S → ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖(∑ s : S, z ^ f s) - ∑ s : S, (0 : ℂ) ^ f s‖ ≤
      Fintype.card S * ‖z‖ := by
  rw [← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum
    (fun s _ => monomial_error_zero z hz (f s))).trans_eq (by simp))

namespace Potts
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [Fintype C]

/-- The exact finite-colouring bound, valid even when the polynomial's
hard-endpoint value is zero. -/
theorem normalizedPartition_error_zero (tau : PartialColouring V C)
    (G : SimpleGraph V) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖normalizedPartition tau G z - normalizedPartition tau G 0‖ ≤
      ((Fintype.card C) ^ Fintype.card tau.FreeVertex : ℕ) * ‖z‖ := by
  rw [normalizedPartition_eq_sum, normalizedPartition_eq_sum]
  simpa only [Fintype.card_fun] using sum_monomials_error_zero
    (fun σ => tau.boundaryConflictCount G σ + tau.freeConflictCount G σ) z hz

theorem bounded_local_error_zero [Nonempty C] (tau : PartialColouring V C)
    (G : SimpleGraph V) (B : ℕ) (hB : Fintype.card tau.FreeVertex ≤ B)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖normalizedPartition tau G z - normalizedPartition tau G 0‖ ≤
      ((Fintype.card C) ^ B : ℕ) * ‖z‖ := by
  apply (normalizedPartition_error_zero tau G z hz).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
  exact_mod_cast Nat.pow_le_pow_right (Fintype.card_pos (α := C)) hB

end Potts
end
end CI2ZF
