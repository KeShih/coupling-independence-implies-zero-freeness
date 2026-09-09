import CI2ZF.Appendix.Girth.Spectral.AdditiveSchur
import CI2ZF.Appendix.Girth.Spectral.DegreeDecomposition

/-! Literal incidence and leaf-degree operators restricted to the actual
positive conditional leaf sectors. -/

namespace CI2ZF.Appendix.Girth.ConditionalStar

open scoped BigOperators InnerProductSpace
open PottsCI Finset

noncomputable section
attribute [local instance] Classical.propDecidable

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]
variable (S : ConditionalStar C D)

theorem plus_mem_iff (z : meanZeroSpace S.jointLaw) :
    z ∈ S.plusSector ↔ z ∈ S.leafSectors.degreeSpace (Set.Ici 1) := by
  rw [S.leafSectors.positive_degree_space]
  rfl

theorem singletons_le_plus : S.leafSectors.degreeSpace {1} ≤ S.plusSector := by
  intro z hz
  exact (S.plus_mem_iff z).mpr (S.leafSectors.degreeSpace_mono (by intro n hn; simp only [Set.mem_singleton_iff, Set.mem_Ici] at hn ⊢; omega) hz)

theorem higher_le_plus : S.leafSectors.degreeSpace (Set.Ici 2) ≤ S.plusSector := by
  intro z hz
  exact (S.plus_mem_iff z).mpr (S.leafSectors.degreeSpace_mono (by intro n hn; exact (show (1 : ℕ) ≤ 2 by norm_num).trans hn) hz)

theorem weighted_symmetric (β : D → ℝ) : Schur.Symmetric (S.leafSectors.weighted β) := by
  intro x y
  simp only [Schur.CommutingProjections.weighted, LinearMap.sum_apply, LinearMap.smul_apply,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [(S.leafSectors.projection i).symmetric]

theorem higher_symmetric : Schur.Symmetric S.leafSectors.higher := by
  intro x y
  have hN := S.weighted_symmetric (fun _ => 1)
  change ⟪S.leafSectors.number (S.leafSectors.number x) - S.leafSectors.number x, y⟫_ℝ =
    ⟪x, S.leafSectors.number (S.leafSectors.number y) - S.leafSectors.number y⟫_ℝ
  rw [inner_sub_left, inner_sub_right]
  simp only [Schur.CommutingProjections.number]
  rw [hN, hN, hN]


theorem weighted_mem_plus (β : D → ℝ) {z : meanZeroSpace S.jointLaw} (hz : z ∈ S.plusSector) :
    S.leafSectors.weighted β z ∈ S.plusSector :=
  (S.plus_mem_iff _).mpr (S.leafSectors.weighted_preserves_degrees β (Set.Ici 1) z ((S.plus_mem_iff z).mp hz))

theorem higher_mem_plus {z : meanZeroSpace S.jointLaw} (hz : z ∈ S.plusSector) :
    S.leafSectors.higher z ∈ S.plusSector :=
  S.plusSector.sub_mem (S.weighted_mem_plus (fun _ => 1) (S.weighted_mem_plus (fun _ => 1) hz))
    (S.weighted_mem_plus (fun _ => 1) hz)

def plusOperator (T : meanZeroSpace S.jointLaw →ₗ[ℝ] meanZeroSpace S.jointLaw)
    (hT : ∀ z ∈ S.plusSector, T z ∈ S.plusSector) : S.plusSector →ₗ[ℝ] S.plusSector :=
  (T.comp S.plusSector.subtype).codRestrict S.plusSector (fun z => hT z z.property)

def plusWeighted (β : D → ℝ) : S.plusSector →ₗ[ℝ] S.plusSector :=
  S.plusOperator (S.leafSectors.weighted β) (fun _ hz => S.weighted_mem_plus β hz)

def plusHigher : S.plusSector →ₗ[ℝ] S.plusSector :=
  S.plusOperator S.leafSectors.higher (fun _ hz => S.higher_mem_plus hz)

theorem plusWeighted_val (β : D → ℝ) (z : S.plusSector) :
    (S.plusWeighted β z : meanZeroSpace S.jointLaw) = S.leafSectors.weighted β z := rfl

theorem plusHigher_val (z : S.plusSector) :
    (S.plusHigher z : meanZeroSpace S.jointLaw) = S.leafSectors.higher z := rfl

theorem plusWeighted_symmetric (β : D → ℝ) : @Schur.Symmetric S.plusSector (inferInstance) (inferInstance) (S.plusWeighted β) :=
  fun x y => S.weighted_symmetric β x y

theorem plusHigher_symmetric : @Schur.Symmetric S.plusSector (inferInstance) (inferInstance) S.plusHigher :=
  fun x y => S.higher_symmetric x y

theorem plusWeighted_positive (β : D → ℝ) (hβ : ∀ i, 0 ≤ β i) :
    @Schur.Positive S.plusSector (inferInstance) (inferInstance) (S.plusWeighted β) :=
  fun x => S.leafSectors.weighted_positive β hβ x

def singletonComplementSpace : Submodule ℝ S.plusSector :=
  (S.leafSectors.degreeSpace {1} ⊓ S.additiveSpaceᗮ).comap S.plusSector.subtype

def higherPlusSpace : Submodule ℝ S.plusSector :=
  (S.leafSectors.degreeSpace (Set.Ici 2)).comap S.plusSector.subtype

theorem additivePlusSpace_mem_iff (a : S.plusSector) :
    a ∈ S.additivePlusSpace ↔ (a : meanZeroSpace S.jointLaw) ∈ S.additiveSpace := by
  constructor
  · rintro ⟨h, he⟩
    exact ⟨h, congrArg Subtype.val he⟩
  · rintro ⟨h, he⟩
    exact ⟨h, Subtype.ext he⟩

theorem plus_decomposition (f : S.plusSector) :
    ∃ a ∈ S.additivePlusSpace, ∃ b ∈ S.singletonComplementSpace, ∃ h ∈ S.higherPlusSpace,
      f = a + (b + h) := by
  obtain ⟨a, ha, b, hb, h, hh, he⟩ := S.leafSectors.additive_singleton_higher_decomposition
    S.additiveSpace S.additiveSpace_le_singletons ((S.plus_mem_iff f).mp f.property)
  let a' : S.plusSector := ⟨a, S.additiveSpace_le_plus ha⟩
  let b' : S.plusSector := ⟨b, S.singletons_le_plus hb.1⟩
  let h' : S.plusSector := ⟨h, S.higher_le_plus hh⟩
  refine ⟨a', (S.additivePlusSpace_mem_iff a').mpr ha, b', hb, h', hh, ?_⟩
  exact Subtype.ext he

end
end CI2ZF.Appendix.Girth.ConditionalStar
