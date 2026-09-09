import CI2ZF.Appendix.Edge.Slots.LiftLimit
import CI2ZF.Appendix.Edge.Slots.Definitions
import CI2ZF.CommonCoins

/-! Exact fibre masses and initial slack for the actual finite-slot lift. -/

namespace CI2ZF.Appendix.Edge
open PottsCI
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) (A : Type*) : DecidableEq A := Classical.decEq A
set_option linter.unusedSectionVars false

namespace EndpointGeometry
variable {V E C R : Type*} [Fintype V] [Fintype E] [Fintype C] [Fintype R]

lemma finiteSlotCoordinate_sum (κ : R → ℝ) (hκ : ∀ r, 0 ≤ κ r)
    (hsum : ∑ r, κ r = 1) (h : Fin 2) (r : R) :
    (∑ s : Fin 2 → R, if s h = r then ∏ i, κ (s i) else 0) = κ r := by
  let p : FinDist R := ⟨κ, hκ, hsum⟩
  have hm := CI2ZF.expectReal_product_coordinate (fun _ : Fin 2 => p) h
    (fun a => if a = r then (1 : ℝ) else 0)
  simpa [expectReal, CI2ZF.productLaw, p, mul_ite] using hm

lemma finiteSlotActivity_sum (κ : R → ℝ) (hsum : ∑ r, κ r = 1)
    (x : ℝ) (b : E → C → ℕ) (e : E) :
    (∑ a : SlotState C R, finiteSlotActivity κ x b e a) = ∑ c, x ^ b e c := by
  rw [Fintype.sum_prod_type]
  simp only [finiteSlotActivity, ← Finset.mul_sum, ← Fintype.prod_sum, hsum,
    Finset.prod_const_one, mul_one]

lemma slotSystem_label_fibre (g : EndpointGeometry V E) (κ : R → ℝ)
    (hκ : ∀ r, 0 ≤ κ r) (hsum : ∑ r, κ r = 1) (x : ℝ) (hx : 0 ≤ x)
    (b : E → C → ℕ) (e : E) (h : Fin 2) (c : C) (r : R) :
    (∑ a : SlotState C R,
      if (g.slotSystem κ hκ x hx b).label e (g.endpoint e h) a = (c, r)
      then (g.slotSystem κ hκ x hx b).activity e a else 0) = x ^ b e c * κ r := by
  simp only [slotSystem_label_endpoint]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single c]
  · simp only [Prod.mk.injEq, true_and, slotSystem, finiteSlotActivity]
    rw [← finiteSlotCoordinate_sum κ hκ hsum h r, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> simp
  · intro d _ hd
    simp only [Prod.mk.injEq, hd, false_and, if_false, Finset.sum_const_zero]
  · intro hc
    exact False.elim (hc (Finset.mem_univ c))

theorem slotSystem_fibreBound (g : EndpointGeometry V E) (κ : R → ℝ)
    (hκ : ∀ r, 0 ≤ κ r) (hsum : ∑ r, κ r = 1) {x : ℝ} (hx : 0 ≤ x)
    (hx1 : x ≤ 1) (b : E → C → ℕ) : (g.slotSystem κ hκ x hx b).FibreBound := by
  intro e v hv l
  obtain ⟨h, _, hh⟩ := Finset.mem_image.mp hv
  rw [← hh, slotSystem_label_fibre g κ hκ hsum]
  have hκ1 : κ l.2 ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun r _ => hκ r) (Finset.mem_univ l.2)
  exact mul_le_one₀ (pow_le_one₀ hx hx1) (hκ l.2) hκ1

lemma slotSystem_compatibleMass_empty (g : EndpointGeometry V E) (κ : R → ℝ)
    (hκ : ∀ r, 0 ≤ κ r) (hsum : ∑ r, κ r = 1) (x : ℝ) (hx : 0 ≤ x)
    (b : E → C → ℕ) (e : E) :
    (g.slotSystem κ hκ x hx b).compatibleMass (fun _ => ∅) e = ∑ c, x ^ b e c := by
  simpa [FiniteSystem.compatibleMass, FiniteSystem.Compatible, slotSystem] using
    finiteSlotActivity_sum κ hsum x b e

lemma slotSystem_initial_slack (g : EndpointGeometry V E) (κ : R → ℝ)
    (hκ : ∀ r, 0 ≤ κ r) (hsum : ∑ r, κ r = 1) (x : ℝ) (hx : 0 ≤ x)
    (b : E → C → ℕ) {Δ : ℕ} (hq : 3 * Δ ≤ Fintype.card C)
    (hincidence : ∀ e, (g.slotSystem κ hκ x hx b).edgeDegree e + (∑ c, b e c) + 2 ≤ 2 * Δ)
    (e : E) :
    (Δ : ℝ) + 2 ≤ (g.slotSystem κ hκ x hx b).compatibleMass (fun _ => ∅) e -
      (g.slotSystem κ hκ x hx b).edgeDegree e := by
  rw [slotSystem_compatibleMass_empty g κ hκ hsum]
  have htotal : (Fintype.card C : ℝ) - (∑ c, b e c : ℕ) ≤ ∑ c, x ^ b e c := by
    calc
      (Fintype.card C : ℝ) - (∑ c, b e c : ℕ) = ∑ c, (1 - (b e c : ℝ)) := by simp
      _ ≤ ∑ c, x ^ b e c := Finset.sum_le_sum fun c _ => one_sub_nat_le_pow hx _
  have hq' : (3 : ℝ) * Δ ≤ Fintype.card C := by exact_mod_cast hq
  have hi' : ((g.slotSystem κ hκ x hx b).edgeDegree e : ℝ) +
      (∑ c, b e c : ℕ) + 2 ≤ 2 * Δ := by exact_mod_cast hincidence e
  linarith

theorem slotSystem_bounds (g : EndpointGeometry V E) (κ : R → ℝ)
    (hκ : ∀ r, 0 ≤ κ r) (hsum : ∑ r, κ r = 1) (x : ℝ) (hx : 0 ≤ x)
    (hx1 : x ≤ 1) (b : E → C → ℕ) {Δ : ℕ} (hq : 3 * Δ ≤ Fintype.card C)
    (hdegree : ∀ v, ((g.slotSystem κ hκ x hx b).incident v).card ≤ Δ)
    (hincidence : ∀ e, (g.slotSystem κ hκ x hx b).edgeDegree e + (∑ c, b e c) + 2 ≤ 2 * Δ) :
    (g.slotSystem κ hκ x hx b).Bounds (fun _ => ∅) Δ := by
  refine ⟨?_, g.slotSystem_fibreBound κ hκ hsum hx hx1 b,
    g.slotSystem_initial_slack κ hκ hsum x hx b hq hincidence⟩
  intro v
  simpa only [Finset.card_empty, Nat.add_zero] using hdegree v

end EndpointGeometry
end
end CI2ZF.Appendix.Edge
