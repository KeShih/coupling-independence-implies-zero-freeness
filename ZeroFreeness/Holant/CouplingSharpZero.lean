import ZeroFreeness.Holant.CouplingZero

/-! The exact two-endpoint incidence condition removes the auxiliary
restriction `A ≥ 1` in the stopping-probability estimate. -/
namespace ZeroFreeness.HolantCoupling.Sharp
open scoped BigOperators
open PottsCI PottsCI.FinDist ZeroFreeness.Holant
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [DecidableEq E]

theorem shift_partition_le (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (e : E) {A : ℝ}
    (_hA : 0 ≤ A) (hf : ∀ v k, 0 ≤ f v k)
    (hx : ∀ a ∈ edges, 0 ≤ x a)
    (hratio : ∀ v k, f v (k + 1) ≤ A * f v k)
    (hinc : (Finset.univ.filter (inc e)).card = 2) :
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
  simpa only [hinc] using hs

theorem partition_le_single_delete (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (e : E) (he : e ∈ edges) {A R : ℝ}
    (hA : 0 ≤ A) (_hR : 0 ≤ R) (hf : ∀ v k, 0 ≤ f v k)
    (hx : ∀ a ∈ edges, x a ∈ Set.Icc 0 R)
    (hratio : ∀ v k, f v (k + 1) ≤ A * f v k)
    (hinc : (Finset.univ.filter (inc e)).card = 2) :
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
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hf : ∀ v k, 0 ≤ f v k)
    (hx : ∀ a ∈ edges, x a ∈ Set.Icc 0 R)
    (hratio : ∀ v k, f v (k + 1) ≤ A * f v k)
    (hinc : ∀ e ∈ edges, (Finset.univ.filter (inc e)).card = 2)
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
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hf : ∀ v k, 0 ≤ f v k)
    (hf0 : ∀ v, 0 < f v 0) (hx : ∀ a ∈ edges, x a ∈ Set.Icc 0 R)
    (hratio : ∀ v k, f v (k + 1) ≤ A * f v k)
    (hinc : ∀ e ∈ edges, (Finset.univ.filter (inc e)).card = 2)
    (hJ : J ⊆ edges) :
    ((1 + A ^ 2 * R) ^ J.card)⁻¹ ≤
      partition inc (edges \ J) f x / partition inc edges f x := by
  have hz := partition_pos inc edges f x hf hf0 (fun e he => (hx e he).1)
  have hp : 0 < (1 + A ^ 2 * R) ^ J.card := by positivity
  have hb := partition_le_delete_set inc edges J f x hA hR hf hx hratio hinc hJ
  apply (le_div_iff₀ hz).mpr
  exact (inv_mul_le_iff₀ hp).mpr hb


variable [DecidableEq V] [Fintype E]

theorem gibbs_zeroOn_lower (inc : E → V → Prop) (edges J : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) {A R : ℝ}
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hf : ∀ v k, 0 ≤ f v k)
    (hf0 : ∀ v, 0 < f v 0) (hx : ∀ a ∈ edges, x a ∈ Set.Icc 0 R)
    (hratio : ∀ v k, f v (k + 1) ≤ A * f v k)
    (hinc : ∀ e ∈ edges, (Finset.univ.filter (inc e)).card = 2)
    (hJ : J ⊆ edges) :
    ((1 + A ^ 2 * R) ^ J.card)⁻¹ ≤
      zeroOn (gibbs inc edges f x hf hf0 (fun e he => (hx e he).1)) J := by
  rw [gibbs_zeroOn_eq_ratio]
  exact delete_set_ratio_lower inc edges J f x hA hR hf hf0 hx hratio hinc hJ

end
end ZeroFreeness.HolantCoupling.Sharp
