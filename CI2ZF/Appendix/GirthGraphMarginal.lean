import CI2ZF.Appendix.GirthInsertionPoincare
import CI2ZF.Appendix.GirthResponseScore

/-! The uniform one-coordinate cap under the actual graph Gibbs law,
obtained by averaging the genuine one-site heat-bath conditional law. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C] [Nonempty C]

namespace GraphHeatBath
variable (I : PinningData V C) (x : ℝ) (hx : 0 < x)

include hx in
theorem positive_partition_at_site (σ : V → C) (v : V) : 0 < sitePartition I x σ v := by
  exact Finset.sum_pos (fun c _ => pow_pos hx _) Finset.univ_nonempty

theorem gibbs_marginal_atom_le (hx1 : x ≤ 1) {Δ : ℕ} (hd : I.DegreeBound Δ)
    {m : ℝ} (hm : 0 < m) (hq : m ≤ (Fintype.card C : ℝ) - Δ)
    (hZ : 0 < I.partition x) (v : V) (c : C) :
    (coordinateMarginal (I.gibbs x hx.le hZ) (fun σ => σ v)).w c ≤ 1 / m := by
  rw [← coordinateIndicator_mean]
  rw [← projection_stationary I x hx (positive_partition_at_site I x hx) hZ v]
  have he : projection I x hx.le (positive_partition_at_site I x hx) v
      (fun σ => colourIndicator c (σ v)) =
        fun σ => (siteLaw I x hx.le (positive_partition_at_site I x hx) σ v).w c := by
    funext σ
    change expectReal (siteLaw I x hx.le (positive_partition_at_site I x hx) σ v)
      (fun a => colourIndicator c (Function.update σ v a v)) = _
    simp only [Function.update_self]
    exact expect_colourIndicator _ _
  rw [he, ← expectReal_const (I.gibbs x hx.le hZ) (1/m)]
  exact expectReal_mono _ (fun σ => siteLaw_atom_le I x hx (positive_partition_at_site I x hx)
    hx1 hd hm hq σ v c)

end GraphHeatBath
end
end CI2ZF.Appendix.Girth
