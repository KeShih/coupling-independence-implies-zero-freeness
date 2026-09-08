import CI2ZF.HolantModel
import CI2ZF.HolantSignatures
import CI2ZF.HolantCouplingGibbs
import CI2ZF.CommonCoins

/-! A uniform lower bound on the probability that a prescribed set of
edges is zero. This is the stopping probability in the recursive Holant
coupling. It follows directly from the actual deletion recursion. -/
namespace CI2ZF.Holant
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [DecidableEq E]

theorem shift_partition_le (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (e : E) {A : ℝ}
    (hA : 1 ≤ A) (hf : ∀ v k, 0 ≤ f v k)
    (hx : ∀ a ∈ edges, 0 ≤ x a)
    (hratio : ∀ v k, f v (k + 1) ≤ A * f v k)
    (hinc : (Finset.univ.filter (inc e)).card ≤ 2) :
    partition inc edges (shiftedSignature inc f e) x ≤
      A ^ 2 * partition inc edges f x := by
  let c : V → ℝ := fun v => if inc e v then A else 1
  have hs : partition inc edges (shiftedSignature inc f e) x ≤
      partition inc edges (fun v k => c v * f v k) x := by
    apply partition_mono_signatures inc edges _ x _
    · intro v k
      exact hf v _
    · exact hx
    · intro v k _
      by_cases h : inc e v
      · simpa [shiftedSignature, c, h] using hratio v k
      · simp [shiftedSignature, c, h]
  rw [partition_scale] at hs
  have hc : (∏ v, c v) = A ^ (Finset.univ.filter (inc e)).card := by
    simp [c, ← Finset.prod_filter]
  rw [hc] at hs
  exact hs.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA hinc)
    (by unfold partition; exact Finset.sum_nonneg fun S hS =>
      weight_nonneg inc edges f x hf hx (Finset.mem_powerset.mp hS)))

theorem partition_le_single_delete (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (e : E) (he : e ∈ edges) {A R : ℝ}
    (hA : 1 ≤ A) (_hR : 0 ≤ R) (hf : ∀ v k, 0 ≤ f v k)
    (hx : ∀ a ∈ edges, x a ∈ Set.Icc 0 R)
    (hratio : ∀ v k, f v (k + 1) ≤ A * f v k)
    (hinc : (Finset.univ.filter (inc e)).card ≤ 2) :
    partition inc edges f x ≤ (1 + A ^ 2 * R) * partition inc (edges.erase e) f x := by
  have hxe := hx e he
  have hx' : ∀ a ∈ edges.erase e, 0 ≤ x a := fun a ha => (hx a (Finset.mem_of_mem_erase ha)).1
  have hz : 0 ≤ partition inc (edges.erase e) f x := by
    unfold partition
    exact Finset.sum_nonneg fun S hS =>
      weight_nonneg inc (edges.erase e) f x hf hx' (Finset.mem_powerset.mp hS)
  have hs := shift_partition_le inc (edges.erase e) f x e hA hf hx' hratio hinc
  have hmul := mul_le_mul_of_nonneg_left hs hxe.1
  have hRmul := mul_le_mul_of_nonneg_right hxe.2 (mul_nonneg (sq_nonneg A) hz)
  rw [partition_deletion inc edges f x e he]
  nlinarith

/-- The bound is uniform in the total number of edges. Only the number of
edges required to be zero enters its exponent. -/
theorem partition_le_delete_set (inc : E → V → Prop) (edges J : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) {A R : ℝ}
    (hA : 1 ≤ A) (hR : 0 ≤ R) (hf : ∀ v k, 0 ≤ f v k)
    (hx : ∀ a ∈ edges, x a ∈ Set.Icc 0 R)
    (hratio : ∀ v k, f v (k + 1) ≤ A * f v k)
    (hinc : ∀ e ∈ edges, (Finset.univ.filter (inc e)).card ≤ 2)
    (hJ : J ⊆ edges) :
    partition inc edges f x ≤ (1 + A ^ 2 * R) ^ J.card * partition inc (edges \ J) f x := by
  induction J using Finset.induction_on generalizing edges with
  | empty => simp
  | @insert e J he ih =>
    have heE : e ∈ edges := hJ (Finset.mem_insert_self e J)
    have hJE : J ⊆ edges.erase e := by
      intro a ha
      exact Finset.mem_erase.mpr ⟨by intro hae; subst a; exact he ha,
        hJ (Finset.mem_insert_of_mem ha)⟩
    have hi := ih (edges.erase e)
      (fun a ha => hx a (Finset.mem_of_mem_erase ha))
      (fun a ha => hinc a (Finset.mem_of_mem_erase ha)) hJE
    have hs := partition_le_single_delete inc edges f x e heE hA hR hf hx hratio (hinc e heE)
    have hp : 0 ≤ 1 + A ^ 2 * R := by positivity
    have hm := mul_le_mul_of_nonneg_left hi hp
    have hd : edges.erase e \ J = edges \ insert e J := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
      tauto
    rw [hd] at hm
    rw [Finset.card_insert_of_notMem he, pow_succ]
    nlinarith

theorem delete_set_ratio_lower (inc : E → V → Prop) (edges J : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) {A R : ℝ}
    (hA : 1 ≤ A) (hR : 0 ≤ R) (hf : ∀ v k, 0 ≤ f v k)
    (hf0 : ∀ v, 0 < f v 0) (hx : ∀ a ∈ edges, x a ∈ Set.Icc 0 R)
    (hratio : ∀ v k, f v (k + 1) ≤ A * f v k)
    (hinc : ∀ e ∈ edges, (Finset.univ.filter (inc e)).card ≤ 2)
    (hJ : J ⊆ edges) :
    ((1 + A ^ 2 * R) ^ J.card)⁻¹ ≤
      partition inc (edges \ J) f x / partition inc edges f x := by
  have hz := partition_pos inc edges f x hf hf0 (fun e he => (hx e he).1)
  have hp : 0 < (1 + A ^ 2 * R) ^ J.card := by positivity
  have hb := partition_le_delete_set inc edges J f x hA hR hf hx hratio hinc hJ
  apply (le_div_iff₀ hz).mpr
  exact (inv_mul_le_iff₀ hp).mpr hb

end
end CI2ZF.Holant

namespace CI2ZF.HolantCoupling
open scoped BigOperators
open PottsCI PottsCI.FinDist CI2ZF.Holant
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def zeroOn (μ : FinDist (Finset E)) (J : Finset E) : ℝ :=
  ∑ S, μ.w S * if Disjoint S J then 1 else 0

theorem zeroOn_bind {T : Type*} [Fintype T] (μ : FinDist T)
    (K : T → FinDist (Finset E)) (J : Finset E) :
    zeroOn (μ.bind K) J = ∑ t, μ.w t * zeroOn (K t) J := by
  simp only [zeroOn, FinDist.bind_w, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem zeroOn_insert (μ : FinDist (Finset E)) (J : Finset E)
    (e : E) (he : e ∈ J) : zeroOn (mapLaw μ (insert e)) J = 0 := by
  change expectReal (mapLaw μ (insert e)) (fun S => if Disjoint S J then 1 else 0) = 0
  rw [expectReal_mapLaw]
  have hd : ∀ S : Finset E, ¬ Disjoint (insert e S) J := by
    intro S h
    exact Finset.disjoint_left.mp h (Finset.mem_insert_self e S) he
  simp [hd]

theorem zeroOn_erase_of_absent (μ : FinDist (Finset E)) (J : Finset E)
    (e : E) (he : e ∈ J) (habs : ∀ S, e ∈ S → μ.w S = 0) :
    zeroOn μ J = zeroOn μ (J.erase e) := by
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : e ∈ S
  · simp [habs S hS]
  · have hd : Disjoint S J ↔ Disjoint S (J.erase e) := by
      conv_lhs => rw [← Finset.insert_erase he]
      simp [hS]
    simp [hd]

theorem zeroOn_bernoulli_delete (μ0 μ1 : FinDist (Finset E)) (J : Finset E)
    (e : E) (he : e ∈ J) (habs : ∀ S, e ∈ S → μ0.w S = 0)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    zeroOn ((bernoulli p hp0 hp1).bind
      (fun b => if b then mapLaw μ1 (insert e) else μ0)) J =
      (1 - p) * zeroOn μ0 (J.erase e) := by
  rw [zeroOn_bind]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, bernoulli,
    zeroOn_insert μ1 J e he, mul_zero, zero_add]
  rw [zeroOn_erase_of_absent μ0 J e he habs]

theorem gibbs_zeroOn_eq_ratio (inc : E → V → Prop) (edges J : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (hf : ∀ v k, 0 ≤ f v k)
    (hf0 : ∀ v, 0 < f v 0) (hx : ∀ e ∈ edges, 0 ≤ x e) :
    zeroOn (gibbs inc edges f x hf hf0 hx) J =
      partition inc (edges \ J) f x / partition inc edges f x := by
  unfold zeroOn
  simp only [gibbs_apply]
  rw [← sum_restrictedWeight inc (edges \ J) f x, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro S _
  unfold restrictedWeight
  by_cases hS : S ⊆ edges <;> by_cases hd : Disjoint S J <;>
    simp [hS, hd, Finset.subset_sdiff]

theorem gibbs_zeroOn_lower (inc : E → V → Prop) (edges J : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) {A R : ℝ}
    (hA : 1 ≤ A) (hR : 0 ≤ R) (hf : ∀ v k, 0 ≤ f v k)
    (hf0 : ∀ v, 0 < f v 0) (hx : ∀ a ∈ edges, x a ∈ Set.Icc 0 R)
    (hratio : ∀ v k, f v (k + 1) ≤ A * f v k)
    (hinc : ∀ e ∈ edges, (Finset.univ.filter (inc e)).card ≤ 2)
    (hJ : J ⊆ edges) :
    ((1 + A ^ 2 * R) ^ J.card)⁻¹ ≤
      zeroOn (gibbs inc edges f x hf hf0 (fun e he => (hx e he).1)) J := by
  rw [gibbs_zeroOn_eq_ratio]
  exact delete_set_ratio_lower inc edges J f x hA hR hf hf0 hx hratio hinc hJ

end
end CI2ZF.HolantCoupling
