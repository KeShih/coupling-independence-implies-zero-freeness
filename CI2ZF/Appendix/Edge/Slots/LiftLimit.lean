import CI2ZF.Appendix.Edge.Slots.Lift
import CI2ZF.Appendix.Edge.Slots.Approximation

/-!
# Convergence of the actual finite-slot Gibbs laws

The number of slots is shifted by the number of endpoint incidences. Every
colour fibre is consequently positive. The normalized colour pushforwards
converge pointwise to the finite Potts law with endpoint collision factors.
-/

namespace CI2ZF.Appendix.Edge

open PottsCI Filter
open scoped BigOperators Topology

noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) (A : Type*) : DecidableEq A := Classical.decEq A
set_option linter.unusedSectionVars false

lemma distinctSlotMass_decidable_eq {R : Type*} [Fintype R]
    (d d' : DecidableEq R) (κ : R → ℝ) (k : ℕ) :
    @distinctSlotMass R _ d κ k = @distinctSlotMass R _ d' κ k := by
  have hd : d = d' := Subsingleton.elim _ _
  rw [hd]

lemma classicalApproxSlotMoment (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (n k : ℕ) :
    distinctSlotMass (finiteApproxSlotWeights x hx hx1 n) k =
      ((n + 1).descFactorial k : ℝ) / ((n : ℝ) + 1) ^ k * x ^ k.choose 2 := by
  rw [distinctSlotMass_decidable_eq _ (instDecidableEqFin _)]
  exact finiteApproxSlotWeights_moment x hx hx1 n k

lemma classicalApproxSlotMoment_tendsto (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (k : ℕ) :
    Tendsto (fun n => distinctSlotMass (finiteApproxSlotWeights x hx hx1 n) k)
      atTop (𝓝 (x ^ k.choose 2)) := by
  simp only [classicalApproxSlotMoment]
  simpa only [one_mul] using (tendsto_descFactorial_ratio k).mul_const (x ^ k.choose 2)

namespace EndpointGeometry

variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]

def targetColourWeight (g : EndpointGeometry V E) (x : ℝ) (b : E → C → ℕ)
    (φ : E → C) : ℝ :=
  (∏ e, x ^ b e (φ e)) * ∏ vc, x ^ (g.colourIncidenceCount φ vc).choose 2

def targetColourPartition (g : EndpointGeometry V E) (x : ℝ) (b : E → C → ℕ) : ℝ :=
  ∑ φ, g.targetColourWeight x b φ

lemma targetColourWeight_pos (g : EndpointGeometry V E) {x : ℝ} (hx : 0 < x)
    (b : E → C → ℕ) (φ : E → C) : 0 < g.targetColourWeight x b φ := by
  exact mul_pos (Finset.prod_pos fun _ _ => pow_pos hx _)
    (Finset.prod_pos fun _ _ => pow_pos hx _)

lemma targetColourPartition_pos [Nonempty C] (g : EndpointGeometry V E) {x : ℝ}
    (hx : 0 < x) (b : E → C → ℕ) : 0 < g.targetColourPartition x b := by
  exact Finset.sum_pos (fun _ _ => g.targetColourWeight_pos hx b _) Finset.univ_nonempty

def targetColourLaw [Nonempty C] (g : EndpointGeometry V E) (x : ℝ) (hx : 0 < x)
    (b : E → C → ℕ) : FinDist (E → C) where
  w φ := g.targetColourWeight x b φ / g.targetColourPartition x b
  nonneg φ := div_nonneg (g.targetColourWeight_pos hx b φ).le
    (g.targetColourPartition_pos hx b).le
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self (g.targetColourPartition_pos hx b).ne'

lemma colourFibreWeight_tendsto (g : EndpointGeometry V E) (x : ℝ) (hx : 0 < x)
    (hx1 : x < 1) (b : E → C → ℕ) (φ : E → C) :
    Tendsto (fun n => g.colourFibreWeight (finiteApproxSlotWeights x hx hx1 n) x b φ)
      atTop (𝓝 (g.targetColourWeight x b φ)) := by
  apply Tendsto.const_mul
  exact tendsto_finsetProd _ fun vc _ =>
    classicalApproxSlotMoment_tendsto x hx hx1 (g.colourIncidenceCount φ vc)

lemma colourIncidenceCount_le (g : EndpointGeometry V E) (φ : E → C) (vc : V × C) :
    g.colourIncidenceCount φ vc ≤ Fintype.card (E × Fin 2) :=
  Fintype.card_subtype_le _

def approxSlotIndex (n : ℕ) : ℕ := n + Fintype.card (E × Fin 2)

def approxSlotSystem (g : EndpointGeometry V E) (x : ℝ) (hx : 0 < x)
    (hx1 : x < 1) (b : E → C → ℕ) (n : ℕ) :=
  g.slotSystem (finiteApproxSlotWeights x hx hx1 (approxSlotIndex (E := E) n))
    (fun r => (finiteApproxSlotWeights_pos x hx hx1 _ r).le) x hx.le b

lemma approxSlotMoment_pos (g : EndpointGeometry V E) (x : ℝ) (hx : 0 < x)
    (hx1 : x < 1) (φ : E → C) (vc : V × C) (n : ℕ) :
    0 < distinctSlotMass (finiteApproxSlotWeights x hx hx1 (approxSlotIndex (E := E) n))
      (g.colourIncidenceCount φ vc) := by
  rw [classicalApproxSlotMoment]
  apply mul_pos _ (pow_pos hx _)
  apply div_pos _ (pow_pos (by positivity) _)
  exact_mod_cast Nat.descFactorial_pos.mpr
    ((g.colourIncidenceCount_le φ vc).trans
      (Nat.le_succ_of_le (Nat.le_add_left _ _)))

lemma approxSlotColourFibre_pos (g : EndpointGeometry V E) (x : ℝ) (hx : 0 < x)
    (hx1 : x < 1) (b : E → C → ℕ) (φ : E → C) (n : ℕ) :
    0 < g.colourFibreWeight
      (finiteApproxSlotWeights x hx hx1 (approxSlotIndex (E := E) n)) x b φ := by
  exact mul_pos (Finset.prod_pos fun _ _ => pow_pos hx _)
    (Finset.prod_pos fun vc _ => g.approxSlotMoment_pos x hx hx1 φ vc n)

lemma approxSlotSystem_partition_pos [Nonempty C] (g : EndpointGeometry V E)
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (b : E → C → ℕ) (n : ℕ) :
    0 < (g.approxSlotSystem x hx hx1 b n).partition (fun _ => ∅) := by
  rw [approxSlotSystem, slotSystem_partition]
  exact Finset.sum_pos (fun φ _ => g.approxSlotColourFibre_pos x hx hx1 b φ n)
    Finset.univ_nonempty

def approxSlotGibbs [Nonempty C] (g : EndpointGeometry V E)
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (b : E → C → ℕ) (n : ℕ) :=
  (g.approxSlotSystem x hx hx1 b n).gibbs (fun _ => ∅)
    (g.approxSlotSystem_partition_pos x hx hx1 b n)

def approxColourLaw [Nonempty C] (g : EndpointGeometry V E)
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (b : E → C → ℕ) (n : ℕ) : FinDist (E → C) :=
  CI2ZF.mapLaw (g.approxSlotGibbs x hx hx1 b n) colourProjection

lemma approxColourLaw_weight [Nonempty C] (g : EndpointGeometry V E)
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (b : E → C → ℕ) (n : ℕ) (φ : E → C) :
    (g.approxColourLaw x hx hx1 b n).w φ =
      g.colourFibreWeight (finiteApproxSlotWeights x hx hx1 (approxSlotIndex (E := E) n)) x b φ /
        (g.approxSlotSystem x hx hx1 b n).partition (fun _ => ∅) := by
  exact g.slotSystem_gibbs_colour_weight _ _ _ _ _ _ _

lemma approxSlotSystem_partition_tendsto (g : EndpointGeometry V E)
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (b : E → C → ℕ) :
    Tendsto (fun n => (g.approxSlotSystem x hx hx1 b n).partition (fun _ => ∅))
      atTop (𝓝 (g.targetColourPartition x b)) := by
  simp only [approxSlotSystem, slotSystem_partition, targetColourPartition]
  exact tendsto_finsetSum _ fun φ _ =>
    (g.colourFibreWeight_tendsto x hx hx1 b φ).comp
      (tendsto_add_atTop_nat (Fintype.card (E × Fin 2)))

/-- Pointwise convergence holds for the colour pushforwards of the literal
hard-label Gibbs measures, with no abstract replacement of their weights. -/
theorem approxColourLaw_tendsto [Nonempty C] (g : EndpointGeometry V E)
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (b : E → C → ℕ) (φ : E → C) :
    Tendsto (fun n => (g.approxColourLaw x hx hx1 b n).w φ)
      atTop (𝓝 ((g.targetColourLaw x hx b).w φ)) := by
  simp only [approxColourLaw_weight, targetColourLaw]
  apply Tendsto.div _ (g.approxSlotSystem_partition_tendsto x hx hx1 b)
    (g.targetColourPartition_pos hx b).ne'
  exact (g.colourFibreWeight_tendsto x hx hx1 b φ).comp
    (tendsto_add_atTop_nat (Fintype.card (E × Fin 2)))

end EndpointGeometry
end
end CI2ZF.Appendix.Edge
