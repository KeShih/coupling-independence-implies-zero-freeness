import CI2ZF.CommonCoins

/-! Changing only the enumeration of a finite probability space preserves
its weights and all transport costs. -/
namespace PottsCI.FinDist
noncomputable section

def reenumerate {A : Type*} {i : Fintype A} [j : Fintype A]
    (μ : @FinDist A i) : @FinDist A j where
  w := @FinDist.w A i μ
  nonneg := @FinDist.nonneg A i μ
  sum_one := by
    have he : i = j := Subsingleton.elim _ _
    cases he
    exact @FinDist.sum_one A i μ

@[simp] theorem reenumerate_w {A : Type*} {i : Fintype A} [j : Fintype A]
    (μ : @FinDist A i) (a : A) : (reenumerate μ).w a = @FinDist.w A i μ a := rfl

@[simp] theorem reenumerate_same {A : Type*} [i : Fintype A]
    (μ : FinDist A) : reenumerate μ = μ := by
  apply FinDist.ext
  rfl

theorem W_reenumerate {A : Type*} {i : Fintype A} [j : Fintype A]
    (μ ν : @FinDist A i) (d : A → A → ℝ) :
    W d (reenumerate μ) (reenumerate ν) = @W A A i i d μ ν := by
  have he : i = j := Subsingleton.elim _ _
  cases he
  rw [reenumerate_same, reenumerate_same]

theorem reenumerate_mapLaw {A B : Type*} [Fintype A]
    {i : Fintype B} [j : Fintype B] (μ : FinDist A) (f : A → B) :
    reenumerate (@CI2ZF.mapLaw A B _ i μ f) = CI2ZF.mapLaw μ f := by
  have he : i = j := Subsingleton.elim _ _
  cases he
  exact reenumerate_same _

end
end PottsCI.FinDist
