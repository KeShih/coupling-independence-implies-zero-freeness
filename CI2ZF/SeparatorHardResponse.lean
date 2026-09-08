import CI2ZF.SeparatorResponse
import CI2ZF.HardEndpointRelativeError
import CI2ZF.HardMainPerturbation

/-! The actual separator response at zero, with a hard-feasible main
average and an additive error containing all inside defects. -/
namespace CI2ZF.Potts.Separator
open PottsCI PottsCI.FinDist
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
variable {U S O C : Type*} [Fintype U] [Fintype S] [Fintype O] [Fintype C]

/-- Unlike positive-base relative factorization, this identity never
divides by an inside factor: that factor is allowed to vanish at zero. -/
theorem hard_response_eq_main_add_error
    (I : PinningData (Vertex U S O) C) (hsep : Separates I)
    (hZ : 0 < I.partition 0)
    (hE : ∀ ξ : S → C, 0 < exteriorPartition I (0 : ℝ) ξ)
    (z : ℂ) (h : (S → C) → ℂ)
    (hexp : ∀ ξ, Complex.exp (h ξ) =
      exteriorPartition I z ξ / exteriorPartition I (0 : ℂ) ξ) :
    partition I z / partition I (0 : ℂ) =
      expectComplex (shellMarginal I 0 (by norm_num) hZ) (fun ξ => Complex.exp (h ξ)) +
        hardEndpointError (insidePartition I z) (insidePartition I (0 : ℂ))
          (exteriorPartition I (0 : ℝ)) h (I.partition 0) := by
  have hmapZ : partition I (0 : ℂ) = (I.partition 0 : ℂ) := by
    simpa only [Complex.ofRealHom_eq_coe, map_zero, partition_real] using
      (map_partition Complex.ofRealHom I (0 : ℝ)).symm
  have hmapD (ξ : S → C) :
      insidePartition I (0 : ℂ) ξ = ((insidePartition I (0 : ℝ) ξ : ℝ) : ℂ) := by
    simpa only [Complex.ofRealHom_eq_coe, map_zero] using
      (map_insidePartition Complex.ofRealHom I (0 : ℝ) ξ).symm
  have hmapE (ξ : S → C) :
      exteriorPartition I (0 : ℂ) ξ = ((exteriorPartition I (0 : ℝ) ξ : ℝ) : ℂ) := by
    simpa only [Complex.ofRealHom_eq_coe, map_zero] using
      (map_exteriorPartition Complex.ofRealHom I (0 : ℝ) ξ).symm
  have hEnz (ξ : S → C) : ((exteriorPartition I (0 : ℝ) ξ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (hE ξ).ne'
  have hZnz : (I.partition 0 : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  rw [partition_factorization I hsep z, hmapZ]
  unfold expectComplex hardEndpointError
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ξ _
  rw [shellMarginal_apply I hsep]
  simp only [hexp, hmapD, hmapE]
  simp only [Complex.ofReal_div, Complex.ofReal_mul]
  field_simp [hEnz ξ, hZnz]
  ring

/-- The original separator partition is nonzero when the actual defect
is small relative to one exterior response. -/
theorem partition_ne_zero_of_hard_main_error
    (I : PinningData (Vertex U S O) C) (hsep : Separates I)
    (hZ : 0 < I.partition 0)
    (hE : ∀ ξ : S → C, 0 < exteriorPartition I (0 : ℝ) ξ)
    (z : ℂ) (h : (S → C) → ℂ) (anchor : S → C)
    (hexp : ∀ ξ, Complex.exp (h ξ) =
      exteriorPartition I z ξ / exteriorPartition I (0 : ℂ) ξ)
    (hosc : ∀ ξ, ‖h ξ - h anchor‖ ≤ (1 / 4 : ℝ))
    {K r : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (herr : ‖hardEndpointError (insidePartition I z) (insidePartition I (0 : ℂ))
      (exteriorPartition I (0 : ℝ)) h (I.partition 0)‖ ≤
        K * r * ‖Complex.exp (h anchor)‖)
    (hsmall : (3 / 2 : ℝ) * K * r ≤ 1 / 2) : partition I z ≠ 0 := by
  have hn := (hard_main_plus_error (shellMarginal I 0 (by norm_num) hZ) h anchor
    hosc _ hK hr herr hsmall).1
  rw [← hard_response_eq_main_add_error I hsep hZ hE z h hexp] at hn
  exact fun hz => hn (by rw [hz, zero_div])

end
end CI2ZF.Potts.Separator
