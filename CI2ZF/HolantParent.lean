import CI2ZF.HolantModel
import CI2ZF.HolantAnalytic

/-! The nonvanishing induction step for the actual Holant finite sum. -/
namespace CI2ZF.Holant
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [DecidableEq E]
set_option linter.unusedSectionVars false

theorem childCoefficient_nonneg (inc : E → V → Prop) (f : V → ℕ → ℝ)
    (e : E) (hf : ∀ v k, 0 ≤ f v k) : 0 ≤ childCoefficient inc f e := by
  exact Finset.prod_nonneg fun v _ => by
    split_ifs <;> first | exact hf v 1 | norm_num

@[simp] theorem childCoefficient_ofReal (inc : E → V → Prop) (f : V → ℕ → ℝ) (e : E) :
    childCoefficient inc (fun v k => (f v k : ℂ)) e = (childCoefficient (R := ℝ) inc f e : ℂ) := by
  simp [childCoefficient, Complex.ofReal_prod, apply_ite]

@[simp] theorem normalizedChildSignature_ofReal (inc : E → V → Prop)
    (f : V → ℕ → ℝ) (e : E) :
    normalizedChildSignature inc (fun v k => (f v k : ℂ)) e =
      fun v k => (normalizedChildSignature (R := ℝ) inc f e v k : ℂ) := by
  funext v k
  by_cases h : inc e v <;> simp [normalizedChildSignature, h]

theorem normalizedChildSignature_nonneg (inc : E → V → Prop)
    (f : V → ℕ → ℝ) (e : E) (hf : ∀ v k, 0 ≤ f v k) :
    ∀ v k, 0 ≤ normalizedChildSignature inc f e v k := by
  intro v k
  unfold normalizedChildSignature
  split_ifs
  · exact div_nonneg (hf v _) (hf v _)
  · exact hf v _

theorem normalizedChildSignature_zero (inc : E → V → Prop)
    (f : V → ℕ → ℝ) (e : E) (hf0 : ∀ v, f v 0 = 1)
    (hf1 : ∀ v, inc e v → 0 < f v 1) :
    ∀ v, normalizedChildSignature inc f e v 0 = 1 := by
  intro v
  by_cases h : inc e v
  · simp [normalizedChildSignature, h, (hf1 v h).ne']
  · simp [normalizedChildSignature, h, hf0 v]

/-- The real normalized child ratio is positive and at most one. This
remains valid when the activity of the edge being pinned is zero. -/
theorem child_ratio_mem (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (e : E)
    (hf : ∀ v k, 0 ≤ f v k) (hf0 : ∀ v, f v 0 = 1)
    (hf1 : ∀ v, inc e v → 0 < f v 1)
    (hx : ∀ a ∈ edges.erase e, 0 ≤ x a)
    (hshift : ∀ v k, inc e v → k ≤ selectedDegree inc (edges.erase e) v →
      f v (k + 1) / f v 1 ≤ f v k) :
    partition inc (edges.erase e) (normalizedChildSignature inc f e) x /
      partition inc (edges.erase e) f x ∈ Set.Ioc 0 1 := by
  have h0 := partition_pos inc (edges.erase e) f x hf (fun v => by rw [hf0]; norm_num) hx
  have h1 := partition_pos inc (edges.erase e) (normalizedChildSignature inc f e) x
    (normalizedChildSignature_nonneg inc f e hf)
    (fun v => by rw [normalizedChildSignature_zero inc f e hf0 hf1]; norm_num) hx
  exact ⟨div_pos h1 h0, (div_le_one h0).mpr (child_partition_le inc edges f x e hf hx hshift)⟩

theorem partition_ne_zero_of_child_response (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (z : E → ℂ) (e : E) (he : e ∈ edges)
    (hf : ∀ v k, 0 ≤ f v k) (hf0 : ∀ v, f v 0 = 1)
    (hf1 : ∀ v, inc e v → 0 < f v 1) (hx : ∀ a ∈ edges, 0 ≤ x a)
    (hshift : ∀ v k, inc e v → k ≤ selectedDegree inc (edges.erase e) v →
      f v (k + 1) / f v 1 ≤ f v k)
    (hZ0 : partition inc (edges.erase e) (fun v k => (f v k : ℂ)) z ≠ 0)
    (ℓ : ℂ) (hℓ : ‖ℓ‖ ≤ (1 / 4 : ℝ))
    (hexp : Complex.exp ℓ =
      (partition inc (edges.erase e) (fun v k => (normalizedChildSignature (R := ℝ) inc f e v k : ℂ)) z /
        (partition (R := ℝ) inc (edges.erase e) (normalizedChildSignature inc f e) x : ℂ)) /
      (partition inc (edges.erase e) (fun v k => (f v k : ℂ)) z /
        (partition (R := ℝ) inc (edges.erase e) f x : ℂ)))
    (hsmall : childCoefficient inc f e * ‖z e - (x e : ℂ)‖ * (4 / 3) < 1) :
    partition inc edges (fun v k => (f v k : ℂ)) z ≠ 0 := by
  let Z0 := partition inc (edges.erase e) (fun v k => (f v k : ℂ)) z
  let Z1 := partition inc (edges.erase e)
    (fun v k => (normalizedChildSignature (R := ℝ) inc f e v k : ℂ)) z
  let X0 := partition inc (edges.erase e) f x
  let X1 := partition inc (edges.erase e) (normalizedChildSignature inc f e) x
  have hx' : ∀ a ∈ edges.erase e, 0 ≤ x a := fun a ha => hx a (Finset.mem_of_mem_erase ha)
  have hX0 : 0 < X0 := partition_pos inc (edges.erase e) f x hf
    (fun v => by rw [hf0]; norm_num) hx'
  have hX1 : 0 < X1 := partition_pos inc (edges.erase e) (normalizedChildSignature inc f e) x
    (normalizedChildSignature_nonneg inc f e hf)
    (fun v => by rw [normalizedChildSignature_zero inc f e hf0 hf1]; norm_num) hx'
  have hX0c : (X0 : ℂ) ≠ 0 := by exact_mod_cast hX0.ne'
  have hX1c : (X1 : ℂ) ≠ 0 := by exact_mod_cast hX1.ne'
  have hr := child_ratio_mem inc edges f x e hf hf0 hf1 hx' hshift
  have hfct := edge_factor_ne_zero (childCoefficient_nonneg inc f e hf) (hx e he)
    ⟨hr.1.le, hr.2⟩ (z e) ℓ hℓ hsmall
  have hEq : Z1 = Z0 * ((X1 / X0 : ℝ) : ℂ) * Complex.exp ℓ := by
    have hZ0' : Z0 ≠ 0 := hZ0
    change Complex.exp ℓ = (Z1 / (X1 : ℂ)) / (Z0 / (X0 : ℂ)) at hexp
    rw [Complex.ofReal_div, hexp]
    field_simp [hX0c, hX1c, hZ0']
  have h1c : ∀ v, inc e v → (f v 1 : ℂ) ≠ 0 := fun v hv => by exact_mod_cast (hf1 v hv).ne'
  rw [partition_normalized_deletion inc edges (fun v k => (f v k : ℂ)) z e he h1c,
    childCoefficient_ofReal, normalizedChildSignature_ofReal]
  change Z0 + z e * (childCoefficient (R := ℝ) inc f e : ℂ) * Z1 ≠ 0
  rw [hEq]
  have hid : Z0 + z e * (childCoefficient (R := ℝ) inc f e : ℂ) *
      (Z0 * ((X1 / X0 : ℝ) : ℂ) * Complex.exp ℓ) =
      Z0 * (1 + (childCoefficient (R := ℝ) inc f e : ℂ) * z e *
        ((X1 / X0 : ℝ) : ℂ) * Complex.exp ℓ) := by ring
  rw [hid]
  exact mul_ne_zero hZ0 hfct

end
end CI2ZF.Holant
