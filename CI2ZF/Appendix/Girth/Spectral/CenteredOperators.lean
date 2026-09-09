import CI2ZF.Appendix.Girth.Spectral.MeanZero

/-! Centering a function commutes with every constant-preserving
supported heat-bath complement. -/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators InnerProductSpace
open PottsCI

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [Fintype Ω]

theorem centeredEmbed_val (μ : FinDist Ω) (f : Ω → ℝ) :
    (centeredEmbed μ f : SupportedSpace μ) = supportedEmbed μ f - expectReal μ f • supportedOne μ := by
  change supportedEmbed μ (fun ω => f ω - expectReal μ f) = _
  rw [supportedOne, ← map_smul, ← map_sub]
  apply congrArg (supportedEmbed μ)
  funext ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]

namespace SupportedOperator

variable {μ : FinDist Ω} (T : SupportedOperator μ)

theorem complement_centered (h1 : T.operator (supportedOne μ) = supportedOne μ) (f : Ω → ℝ) :
    (centeredEmbed μ f : SupportedSpace μ) - T.operator (centeredEmbed μ f : SupportedSpace μ) =
      supportedEmbed μ (fun ω => f ω - T.raw f ω) := by
  rw [centeredEmbed_val]
  have he : supportedEmbed μ (fun ω => f ω - T.raw f ω) = supportedEmbed μ f - T.operator (supportedEmbed μ f) := by
    rw [T.intertwine]
    exact map_sub (supportedEmbed μ) f (T.raw f)
  rw [he, map_sub, map_smul, h1]
  abel

end SupportedOperator
end
end CI2ZF.Appendix.Girth
