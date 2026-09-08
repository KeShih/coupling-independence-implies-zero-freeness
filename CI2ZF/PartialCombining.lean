import CI2ZF.PartialCoupling

/-! Combine finite partial-coupling increments on disjoint row/column blocks. -/
namespace CI2ZF.PartialCoupling
open PottsCI
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
variable {S T K : Type*} [Fintype S] [Fintype T] [Fintype K]
variable {mu : FinDist S} {nu : FinDist T}

def combineDisjoint (base : PartialCoupling mu nu) (plans : K → PartialCoupling mu nu)
    (rows : K → Finset S) (cols : K → Finset T)
    (hge : ∀ k x y, base.w x y ≤ (plans k).w x y)
    (hrow : ∀ k x y, x ∉ rows k → (plans k).w x y = base.w x y)
    (hcol : ∀ k x y, y ∉ cols k → (plans k).w x y = base.w x y)
    (hrows : ∀ k l, k ≠ l → Disjoint (rows k) (rows l))
    (hcols : ∀ k l, k ≠ l → Disjoint (cols k) (cols l)) : PartialCoupling mu nu where
  w x y := base.w x y + ∑ k, ((plans k).w x y - base.w x y)
  nonneg x y := add_nonneg (base.nonneg x y)
    (Finset.sum_nonneg fun k _ => sub_nonneg.mpr (hge k x y))
  row_le x := by
    by_cases hex : ∃ k, x ∈ rows k
    · obtain ⟨k, hk⟩ := hex
      have heq (y : T) : base.w x y + ∑ l, ((plans l).w x y - base.w x y) = (plans k).w x y := by
        rw [Finset.sum_eq_single k]
        · ring
        · intro l _ hl
          have hxl : x ∉ rows l := fun hxl =>
            (Finset.disjoint_left.mp (hrows k l hl.symm)) hk hxl
          rw [hrow l x y hxl, sub_self]
        · simp
      simp_rw [heq]
      exact (plans k).row_le x
    · have heq (y : T) : base.w x y + ∑ k, ((plans k).w x y - base.w x y) = base.w x y := by
        have hz (k : K) : (plans k).w x y - base.w x y = 0 := by
          rw [hrow k x y (fun hx => hex ⟨k, hx⟩), sub_self]
        simp only [hz, Finset.sum_const_zero, add_zero]
      simp_rw [heq]
      exact base.row_le x
  col_le y := by
    by_cases hex : ∃ k, y ∈ cols k
    · obtain ⟨k, hk⟩ := hex
      have heq (x : S) : base.w x y + ∑ l, ((plans l).w x y - base.w x y) = (plans k).w x y := by
        rw [Finset.sum_eq_single k]
        · ring
        · intro l _ hl
          have hyl : y ∉ cols l := fun hyl =>
            (Finset.disjoint_left.mp (hcols k l hl.symm)) hk hyl
          rw [hcol l x y hyl, sub_self]
        · simp
      simp_rw [heq]
      exact (plans k).col_le y
    · have heq (x : S) : base.w x y + ∑ k, ((plans k).w x y - base.w x y) = base.w x y := by
        have hz (k : K) : (plans k).w x y - base.w x y = 0 := by
          rw [hcol k x y (fun hy => hex ⟨k, hy⟩), sub_self]
        simp only [hz, Finset.sum_const_zero, add_zero]
      simp_rw [heq]
      exact base.col_le y

end
end CI2ZF.PartialCoupling
