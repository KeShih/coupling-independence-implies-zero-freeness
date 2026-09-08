import CI2ZF.HolantCoupling
import CI2ZF.CommonCoins

/-!
# Hamming transport when reconstructing a deleted edge

Inserting the same edge into both configurations does not increase their
distance.  Inserting it on one side costs at most one.  Both facts are
proved for the finite transport infimum, so recursive bounds do not assume
the existence of optimal couplings.
-/

namespace CI2ZF.HolantCoupling

open scoped BigOperators
open PottsCI PottsCI.FinDist

noncomputable section
attribute [local instance] Classical.propDecidable

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Hamming distance on selected-edge subsets. -/
def subsetHam (S T : Finset E) : ℝ :=
  ∑ e, if (e ∈ S ↔ e ∈ T) then 0 else 1

theorem subsetHam_nonneg (S T : Finset E) : 0 ≤ subsetHam S T := by
  unfold subsetHam
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> norm_num

@[simp] theorem subsetHam_self (S : Finset E) : subsetHam S S = 0 := by
  simp [subsetHam]

theorem subsetHam_comm (S T : Finset E) : subsetHam S T = subsetHam T S := by
  simp only [subsetHam, iff_comm]

theorem subsetHam_triangle (S T U : Finset E) :
    subsetHam S U ≤ subsetHam S T + subsetHam T U := by
  unfold subsetHam
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  by_cases hS : e ∈ S <;> by_cases hT : e ∈ T <;> by_cases hU : e ∈ U <;>
    simp [hS, hT, hU]

theorem subsetHam_le_card (S T : Finset E) : subsetHam S T ≤ Fintype.card E := by
  calc
    subsetHam S T ≤ ∑ _ : E, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro e _
      split_ifs <;> norm_num
    _ = _ := by simp

/-- The subset cost is exactly the paper's Boolean-configuration Hamming cost. -/
theorem subsetHam_eq_ham (S T : Finset E) :
    subsetHam S T = ham (fun e => decide (e ∈ S)) (fun e => decide (e ∈ T)) := by
  unfold subsetHam ham hamCard
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hS : e ∈ S <;> by_cases hT : e ∈ T <;> simp [hS, hT]

theorem subsetHam_insert_both_le (S T : Finset E) (e : E) :
    subsetHam (insert e S) (insert e T) ≤ subsetHam S T := by
  apply Finset.sum_le_sum
  intro a _
  by_cases h : a = e
  · subst a
    simp only [Finset.mem_insert_self, iff_self, ↓reduceIte]
    split_ifs <;> norm_num
  · simp [Finset.mem_insert, h]

theorem subsetHam_insert_left_le (S T : Finset E) (e : E) :
    subsetHam (insert e S) T ≤ 1 + subsetHam S T := by
  calc
    subsetHam (insert e S) T ≤
        ∑ a, ((if (a ∈ S ↔ a ∈ T) then 0 else 1) + if a = e then 1 else 0) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases h : a = e
      · subst a
        by_cases hS : e ∈ S <;> by_cases hT : e ∈ T <;> simp [hS, hT]
      · simp [Finset.mem_insert, h]
    _ = 1 + subsetHam S T := by simp [Finset.sum_add_distrib, subsetHam, add_comm]

variable {S T : Type*} [Fintype S] [Fintype T]

theorem mapLaw_identity (μ : FinDist S) : mapLaw μ id = μ := by
  classical
  ext x
  simp [mapLaw, bind_w, FinDist.pure]

/-- Deterministic maps whose cost increases by at most `c` increase optimal
transport by at most the same additive constant. -/
theorem W_mapLaw_le_add (μ ν : FinDist S) (f g : S → T)
    (d : S → S → ℝ) (d' : T → T → ℝ) (hd' : ∀ x y, 0 ≤ d' x y)
    (c : ℝ) (hcost : ∀ x y, d' (f x) (g y) ≤ c + d x y) :
    W d' (mapLaw μ f) (mapLaw ν g) ≤ c + W d μ ν := by
  have h : W d' (mapLaw μ f) (mapLaw ν g) - c ≤ W d μ ν := by
    apply le_W
    intro π
    have hmap := W_le_cost hd' (mapCoupling π f g)
    rw [cost_mapCoupling] at hmap
    have hcost' := cost_le_cost π hcost
    have hsplit : π.cost (fun x y => c + d x y) = c + π.cost d := by
      unfold Coupling.cost
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
      rw [π.total_mass, one_mul]
    rw [hsplit] at hcost'
    linarith
  linarith

theorem W_insert_both_le (μ ν : FinDist (Finset E)) (e : E) :
    W subsetHam (mapLaw μ (fun S : Finset E => insert e S)) (mapLaw ν (fun S : Finset E => insert e S)) ≤
      W subsetHam μ ν := by
  simpa using W_mapLaw_le_add μ ν (fun S : Finset E => insert e S) (fun S : Finset E => insert e S)
    subsetHam subsetHam subsetHam_nonneg 0
    (fun S T => by simpa using subsetHam_insert_both_le S T e)

theorem W_insert_left_le (μ ν : FinDist (Finset E)) (e : E) :
    W subsetHam (mapLaw μ (fun S : Finset E => insert e S)) ν ≤ 1 + W subsetHam μ ν := by
  have h := W_mapLaw_le_add μ ν (fun S : Finset E => insert e S) id
    subsetHam subsetHam subsetHam_nonneg 1
    (fun S T => subsetHam_insert_left_le S T e)
  simpa only [mapLaw_identity] using h

/-- Transposition of the finite coupling matrix. -/
def transposeCoupling {μ ν : FinDist S} (π : Coupling μ ν) : Coupling ν μ where
  w x y := π.w y x
  nonneg x y := π.nonneg y x
  sum_row := π.sum_col
  sum_col := π.sum_row

theorem W_comm (μ ν : FinDist S) (d : S → S → ℝ)
    (hd : ∀ x y, 0 ≤ d x y) (hsym : ∀ x y, d x y = d y x) :
    W d μ ν = W d ν μ := by
  have hle (μ ν : FinDist S) : W d μ ν ≤ W d ν μ := by
    apply le_W
    intro π
    have h := W_le_cost hd (transposeCoupling π)
    have heq : (transposeCoupling π).cost d = π.cost d := by
      unfold Coupling.cost transposeCoupling
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [hsym]
    rwa [heq] at h
  exact le_antisymm (hle μ ν) (hle ν μ)

end

end CI2ZF.HolantCoupling
