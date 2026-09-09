import CI2ZF.Appendix.Edge.Finite.Model
import CI2ZF.Appendix.Edge.Slots.LiftFactorization

/-!
# The actual finite endpoint-slot Gibbs lift

The slot system is a `FiniteSystem`, with one colour and two independently
weighted slots per edge. Its admissibility is exactly distinctness within
each endpoint-colour group. The colour-fibre weights are computed from the
actual hard-label configuration weights.
-/

namespace CI2ZF.Appendix.Edge

open PottsCI
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable
local instance (priority := 2000) (A : Type*) : DecidableEq A := Classical.decEq A
set_option linter.unusedSectionVars false

def endpointSet {V E : Type*} (endpoint : E → Fin 2 → V) (e : E) : Finset V :=
  Finset.univ.image (endpoint e)

structure EndpointGeometry (V E : Type*) where
  endpoint : E → Fin 2 → V
  injective : ∀ e, Function.Injective (endpoint e)
  linear : ∀ e f v w, v ∈ endpointSet endpoint e → v ∈ endpointSet endpoint f →
    w ∈ endpointSet endpoint e → w ∈ endpointSet endpoint f → v ≠ w → e = f

namespace EndpointGeometry

variable {V E C R : Type*} [Fintype V] [Fintype E] [Fintype C] [Fintype R]

def endpoints (g : EndpointGeometry V E) (e : E) : Finset V := endpointSet g.endpoint e

lemma endpoints_card (g : EndpointGeometry V E) (e : E) : (g.endpoints e).card = 2 := by
  rw [endpoints, endpointSet, Finset.card_image_of_injective _ (g.injective e)]
  simp

lemma endpoint_mem (g : EndpointGeometry V E) (e : E) (h : Fin 2) :
    g.endpoint e h ∈ g.endpoints e :=
  Finset.mem_image.mpr ⟨h, Finset.mem_univ h, rfl⟩

def endpointIndex (g : EndpointGeometry V E) (e : E) (v : V) : Fin 2 :=
  Function.invFun (g.endpoint e) v

@[simp] lemma endpointIndex_endpoint (g : EndpointGeometry V E) (e : E) (h : Fin 2) :
    g.endpointIndex e (g.endpoint e h) = h := Function.leftInverse_invFun (g.injective e) h

abbrev SlotState (C R : Type*) := C × (Fin 2 → R)

def finiteSlotActivity (κ : R → ℝ) (x : ℝ) (b : E → C → ℕ)
    (e : E) (a : SlotState C R) : ℝ := x ^ b e a.1 * ∏ h : Fin 2, κ (a.2 h)

def slotSystem (g : EndpointGeometry V E) (κ : R → ℝ) (hκ : ∀ r, 0 ≤ κ r)
    (x : ℝ) (hx : 0 ≤ x) (b : E → C → ℕ) :
    FiniteSystem V E (SlotState C R) (C × R) where
  endpoints := g.endpoints
  endpoints_card := g.endpoints_card
  linear := g.linear
  label e v a := (a.1, a.2 (g.endpointIndex e v))
  activity := finiteSlotActivity κ x b
  activity_nonneg _e a := mul_nonneg (pow_nonneg hx _) (Finset.prod_nonneg fun h _ => hκ (a.2 h))

lemma slotSystem_label_endpoint (g : EndpointGeometry V E) (κ : R → ℝ)
    (hκ : ∀ r, 0 ≤ κ r) (x : ℝ) (hx : 0 ≤ x) (b : E → C → ℕ)
    (e : E) (h : Fin 2) (a : SlotState C R) :
    (g.slotSystem κ hκ x hx b).label e (g.endpoint e h) a = (a.1, a.2 h) := by
  simp [slotSystem]

def slotConfiguration (φ : E → C) (α : E × Fin 2 → R) : E → SlotState C R :=
  fun e => (φ e, fun h => α (e, h))

def slotConfigurationEquiv : ((E → C) × (E × Fin 2 → R)) ≃ (E → SlotState C R) where
  toFun p := slotConfiguration p.1 p.2
  invFun σ := (fun e => (σ e).1, fun p => (σ p.1).2 p.2)
  left_inv _p := rfl
  right_inv _σ := rfl

def incidenceColourKey (g : EndpointGeometry V E) (φ : E → C) (p : E × Fin 2) : V × C :=
  (g.endpoint p.1 p.2, φ p.1)

def colourIncidenceCount (g : EndpointGeometry V E) (φ : E → C) (vc : V × C) : ℕ :=
  Fintype.card {p : E × Fin 2 // g.incidenceColourKey φ p = vc}

/-- Literal hard-label admissibility is precisely within-group injectivity. -/
lemma slotSystem_admissible_empty_iff (g : EndpointGeometry V E) (κ : R → ℝ)
    (hκ : ∀ r, 0 ≤ κ r) (x : ℝ) (hx : 0 ≤ x) (b : E → C → ℕ)
    (φ : E → C) (α : E × Fin 2 → R) :
    (g.slotSystem κ hκ x hx b).Admissible (fun _ => ∅) (slotConfiguration φ α) ↔
      GroupedSlotInjective (g.incidenceColourKey φ) α := by
  rw [groupedSlotInjective_iff]
  constructor
  · intro h p q hkey hslot
    have hv : g.endpoint p.1 p.2 = g.endpoint q.1 q.2 := congrArg Prod.fst hkey
    have hc : φ p.1 = φ q.1 := congrArg Prod.snd hkey
    by_cases he : p.1 = q.1
    · apply Prod.ext he
      apply g.injective p.1
      simpa only [← he] using hv
    · have hpair := h.2 p.1 q.1 he (g.endpoint p.1 p.2)
        (g.endpoint_mem p.1 p.2) (hv ▸ g.endpoint_mem q.1 q.2)
      rw [slotSystem_label_endpoint] at hpair
      have hr : (g.slotSystem κ hκ x hx b).label q.1 (g.endpoint p.1 p.2)
          (slotConfiguration φ α q.1) = (φ q.1, α q) := by
        rw [hv, slotSystem_label_endpoint]
        rfl
      rw [hr] at hpair
      exact False.elim (hpair (Prod.ext hc hslot))
  · intro h
    refine ⟨?_, ?_⟩
    · intro e v _
      simp
    · intro e f hef v hve hvf hlabel
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hve
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hvf
      have hleft : (g.slotSystem κ hκ x hx b).label e v (slotConfiguration φ α e) =
          (φ e, α (e, i)) := by rw [← hi, slotSystem_label_endpoint]; rfl
      have hright : (g.slotSystem κ hκ x hx b).label f v (slotConfiguration φ α f) =
          (φ f, α (f, j)) := by rw [← hj, slotSystem_label_endpoint]; rfl
      rw [hleft, hright] at hlabel
      have hkey : g.incidenceColourKey φ (e, i) = g.incidenceColourKey φ (f, j) :=
        Prod.ext (hi.trans hj.symm) (congrArg Prod.fst hlabel)
      have heq := h (e, i) (f, j) hkey (congrArg Prod.snd hlabel)
      exact hef (congrArg Prod.fst heq)

lemma slotSystem_configurationWeight (g : EndpointGeometry V E) (κ : R → ℝ)
    (hκ : ∀ r, 0 ≤ κ r) (x : ℝ) (hx : 0 ≤ x) (b : E → C → ℕ)
    (φ : E → C) (α : E × Fin 2 → R) :
    (g.slotSystem κ hκ x hx b).configurationWeight (fun _ => ∅) (slotConfiguration φ α) =
      (∏ e, x ^ b e (φ e)) *
        (if GroupedSlotInjective (g.incidenceColourKey φ) α then ∏ p, κ (α p) else 0) := by
  unfold FiniteSystem.configurationWeight
  rw [slotSystem_admissible_empty_iff]
  split_ifs
  · simp only [slotSystem, finiteSlotActivity, slotConfiguration, Finset.prod_mul_distrib]
    rw [Fintype.prod_prod_type]
  · rw [mul_zero]

/-- Exact colour-fibre weight in the actual finite Gibbs system. -/
lemma slotSystem_colour_fibre (g : EndpointGeometry V E) (κ : R → ℝ)
    (hκ : ∀ r, 0 ≤ κ r) (x : ℝ) (hx : 0 ≤ x) (b : E → C → ℕ) (φ : E → C) :
    (∑ α : E × Fin 2 → R,
      (g.slotSystem κ hκ x hx b).configurationWeight (fun _ => ∅) (slotConfiguration φ α)) =
      (∏ e, x ^ b e (φ e)) * ∏ vc, distinctSlotMass κ (g.colourIncidenceCount φ vc) := by
  simp only [slotSystem_configurationWeight, ← Finset.mul_sum]
  change (∏ e, x ^ b e (φ e)) * groupedSlotMass κ (g.incidenceColourKey φ) = _
  rw [groupedSlotMass_factorization]
  rfl

def colourProjection (σ : E → SlotState C R) : E → C := fun e => (σ e).1

def colourFibreWeight (g : EndpointGeometry V E) (κ : R → ℝ) (x : ℝ)
    (b : E → C → ℕ) (φ : E → C) : ℝ :=
  (∏ e, x ^ b e (φ e)) * ∏ vc, distinctSlotMass κ (g.colourIncidenceCount φ vc)

/-- The original lifted partition is exactly the sum of its colour fibres. -/
lemma slotSystem_partition (g : EndpointGeometry V E) (κ : R → ℝ)
    (hκ : ∀ r, 0 ≤ κ r) (x : ℝ) (hx : 0 ≤ x) (b : E → C → ℕ) :
    (g.slotSystem κ hκ x hx b).partition (fun _ => ∅) =
      ∑ φ, g.colourFibreWeight κ x b φ := by
  unfold FiniteSystem.partition
  rw [← (slotConfigurationEquiv (E := E) (C := C) (R := R)).sum_comp
    (fun σ => (g.slotSystem κ hκ x hx b).configurationWeight (fun _ => ∅) σ)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro φ _
  exact g.slotSystem_colour_fibre κ hκ x hx b φ

/-- The colour pushforward of the actual normalized slot Gibbs law has the
computed fibre weight divided by the actual lifted partition. -/
lemma slotSystem_gibbs_colour_weight (g : EndpointGeometry V E) (κ : R → ℝ)
    (hκ : ∀ r, 0 ≤ κ r) (x : ℝ) (hx : 0 ≤ x) (b : E → C → ℕ)
    (hZ : 0 < (g.slotSystem κ hκ x hx b).partition (fun _ => ∅)) (φ : E → C) :
    (CI2ZF.mapLaw ((g.slotSystem κ hκ x hx b).gibbs (fun _ => ∅) hZ) colourProjection).w φ =
      g.colourFibreWeight κ x b φ / (g.slotSystem κ hκ x hx b).partition (fun _ => ∅) := by
  unfold CI2ZF.mapLaw FinDist.bind FinDist.pure
  change (∑ σ : E → SlotState C R,
    ((g.slotSystem κ hκ x hx b).configurationWeight (fun _ => ∅) σ /
      (g.slotSystem κ hκ x hx b).partition (fun _ => ∅)) *
        (if φ = colourProjection σ then 1 else 0)) = _
  rw [← (slotConfigurationEquiv (E := E) (C := C) (R := R)).sum_comp
    (fun σ => ((g.slotSystem κ hκ x hx b).configurationWeight (fun _ => ∅) σ /
      (g.slotSystem κ hκ x hx b).partition (fun _ => ∅)) *
        (if φ = colourProjection σ then 1 else 0)), Fintype.sum_prod_type]
  change (∑ ψ : E → C, ∑ α : E × Fin 2 → R,
    ((g.slotSystem κ hκ x hx b).configurationWeight (fun _ => ∅) (slotConfiguration ψ α) /
      (g.slotSystem κ hκ x hx b).partition (fun _ => ∅)) *
        (if φ = ψ then 1 else 0)) = _
  rw [Finset.sum_eq_single φ]
  · simp only [if_true, mul_one, ← Finset.sum_div]
    rw [slotSystem_colour_fibre]
    rfl
  · intro ψ _ hψ
    simp only [if_neg (Ne.symm hψ), mul_zero, Finset.sum_const_zero]
  · intro hφ
    exact False.elim (hφ (Finset.mem_univ φ))

end EndpointGeometry
end
end CI2ZF.Appendix.Edge
