import ZeroFreeness.Coupling.Girth.Spectral.AdditiveLift
import ZeroFreeness.Coupling.Girth.Spectral.StarSchur

/-! The two additive hypotheses of the actual star Schur argument:
H annihilates the additive range, and C has the required 1/d compression. -/

namespace ZeroFreeness.Appendix.Girth.ConditionalStar

open scoped BigOperators InnerProductSpace
open PottsCI Finset

noncomputable section
attribute [local instance] Classical.propDecidable

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]
variable (S : ConditionalStar C D)

theorem additiveRoot_complement_norm (h : D → C → ℝ) :
    ‖S.additiveRoot h - S.centreMeanHeatBath (S.additiveRoot h)‖ ^ 2 =
      expectReal S.jointLaw (fun σ =>
        (S.additiveMean h σ.1 - S.centreProjection (fun τ => S.additiveMean h τ.1) σ) ^ 2) := by
  change ‖supportedEmbed S.jointLaw (fun σ => S.additiveMean h σ.1 -
      expectReal S.jointLaw (fun τ => S.additiveMean h τ.1)) -
    S.centreHeatBath.operator (supportedEmbed S.jointLaw (fun σ => S.additiveMean h σ.1 -
      expectReal S.jointLaw (fun τ => S.additiveMean h τ.1)))‖ ^ 2 = _
  rw [SupportedOperator.intertwine, ← map_sub, supportedEmbed_norm_sq]
  apply congrArg (expectReal S.jointLaw)
  funext σ
  change ((S.additiveMean h σ.1 - expectReal S.jointLaw (fun τ => S.additiveMean h τ.1)) -
    S.centreProjection (fun σ => S.additiveMean h σ.1 -
      expectReal S.jointLaw (fun τ => S.additiveMean h τ.1)) σ) ^ 2 = _
  rw [S.centreProjection_shift]
  ring

namespace SchurParameters
variable {S} (p : S.SchurParameters)

theorem residual_additive_zero (a : S.plusSector) (ha : a ∈ S.additivePlusSpace) :
    p.residualProjection a = 0 := by
  obtain ⟨h, rfl⟩ := ha
  exact p.residual_eq_zero_of_fixed (S.additiveRootZero h) (S.additivePlusMap h) (S.additive_centre_fixed h)

theorem correction_additive_bound (a : S.plusSector) (ha : a ∈ S.additivePlusSpace) :
    (Fintype.card D : ℝ) * @Schur.energy S.plusSector (inferInstance) (inferInstance) p.correction a ≤
      ‖a‖ ^ 2 / (1 + p.δ / 2) := by
  obtain ⟨h, rfl⟩ := ha
  have he := p.correction_energy_of_fixed (S.additiveRootZero h) (S.additivePlusMap h) (S.additive_centre_fixed h)
  change @Schur.energy S.plusSector (inferInstance) (inferInstance) p.correction (S.additivePlusMap h) =
    ‖S.additiveRoot h - S.centreMeanHeatBath (S.additiveRoot h)‖ ^ 2 at he
  rw [he, S.additiveRoot_complement_norm, S.additivePlusMap_norm_sq]
  obtain ⟨_, _, hB0, hB, _, _⟩ := girthFiveThreshold_bounds p.delta_pos p.delta_le_one p.threshold
  simpa only [one_div_mul_eq_div] using S.additive_compression_energy_all p.delta_pos hB0.le hB
    (by exact_mod_cast p.degree_le) p.palette_budget p.cavity_cap p.centre_cap h

end SchurParameters
end
end ZeroFreeness.Appendix.Girth.ConditionalStar
