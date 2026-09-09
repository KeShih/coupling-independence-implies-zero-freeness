import CI2ZF.Appendix.BBR.Messages

/-! The BBR differential estimate is proved directly from the explicit
Jacobian blocks, Euclidean projection, and the elementary occupancy
inequality. It is not imported as a tree-decay or coupling hypothesis. -/
namespace CI2ZF.Appendix.BBR
open scoped BigOperators
open Finset Set PottsCI
open CI2ZF.Appendix.Girth
noncomputable section
set_option linter.unusedSectionVars false

variable {C D : Type*} [Fintype C] [Fintype D] [Nonempty C]

def innerSum (y z : C → ℝ) : ℝ := ∑ c, y c * z c
def projection (y z : C → ℝ) (c : C) : ℝ :=
  z c - y c * innerSum y z / squareMass y

def pointWeightSquare (x : ℝ) (y : C → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun c => squareMass y / excludedMass x y c ^ 2)

def jacobianBlock (x : ℝ) (Y y z : C → ℝ) (c : C) : ℝ :=
  Y c * (x - 1) * y c / excludedMass x y c * projection y z c

theorem squareMass_nonneg (y : C → ℝ) : 0 ≤ squareMass y := Finset.sum_nonneg fun _ _ => sq_nonneg _
theorem coordinate_sq_le_mass (y : C → ℝ) (c : C) : y c ^ 2 ≤ squareMass y :=
  Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ c)

theorem excludedMass_bounds {x : ℝ} (_hx : 0 < x) (hx1 : x ≤ 1)
    (y : C → ℝ) (c : C) :
    x * squareMass y ≤ excludedMass x y c ∧ excludedMass x y c ≤ squareMass y := by
  have h0 := mul_nonneg (sub_nonneg.mpr hx1) (sq_nonneg (y c))
  have h1 := mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr (coordinate_sq_le_mass y c))
  unfold excludedMass
  constructor <;> nlinarith

theorem excludedMass_pos {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (y : C → ℝ) (hS : 0 < squareMass y) (c : C) : 0 < excludedMass x y c :=
  (mul_pos hx hS).trans_le (excludedMass_bounds hx hx1 y c).1

theorem pointWeightSquare_nonneg (x : ℝ) (y : C → ℝ) : 0 ≤ pointWeightSquare x y := by
  obtain ⟨c⟩ := ‹Nonempty C›
  exact (div_nonneg (squareMass_nonneg y) (sq_nonneg (excludedMass x y c))).trans
    (Finset.le_sup' (fun c => squareMass y / excludedMass x y c ^ 2) (Finset.mem_univ c))

theorem ratio_le_pointWeightSquare (x : ℝ) (y : C → ℝ) (c : C) :
    squareMass y / excludedMass x y c ^ 2 ≤ pointWeightSquare x y :=
  Finset.le_sup' (fun c => squareMass y / excludedMass x y c ^ 2) (Finset.mem_univ c)

theorem projection_energy (y z : C → ℝ) (hS : 0 < squareMass y) :
    squareMass (projection y z) = squareMass z - innerSum y z ^ 2 / squareMass y := by
  unfold squareMass projection
  simp only [sub_sq, div_pow, mul_pow, mul_div_assoc, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  have hcross : (∑ c, 2 * z c * (y c * (innerSum y z / squareMass y))) =
      2 * innerSum y z ^ 2 / squareMass y := by
    calc
      _ = (∑ c, y c * z c) * (2 * (innerSum y z / squareMass y)) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => by ring
      _ = _ := by unfold innerSum; ring
  rw [hcross]
  change squareMass z - 2 * innerSum y z ^ 2 / squareMass y +
    squareMass y * (innerSum y z ^ 2 / squareMass y ^ 2) =
      squareMass z - innerSum y z ^ 2 / squareMass y
  field_simp [hS.ne']
  ring

theorem projection_energy_le (y z : C → ℝ) (hS : 0 < squareMass y) :
    squareMass (projection y z) ≤ squareMass z := by
  rw [projection_energy y z hS]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) hS.le)

def localRoot (x : ℝ) (B : C → ℝ) (R : D → C → ℝ) (c : C) : ℝ :=
  B c * ∏ i, localFactor x (R i) c

theorem localRoot_square {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (B : C → ℝ) (R : D → C → ℝ) (hS : ∀ i, 0 < squareMass (R i)) (c : C) :
    localRoot x B R c ^ 2 = B c ^ 2 *
      ∏ i, (1 - (1 - x) * (R i c ^ 2 / squareMass (R i))) := by
  unfold localRoot localFactor
  rw [mul_pow, ← Finset.prod_pow]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [Real.sq_sqrt (div_nonneg (excludedMass_pos hx hx1 (R i) (hS i) c).le (hS i).le)]
  unfold excludedMass
  field_simp [(hS i).ne']

theorem localRoot_occupancy {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (B : C → ℝ) (hB : ∀ c, B c ^ 2 ≤ 1) (R : D → C → ℝ)
    (hS : ∀ i, 0 < squareMass (R i)) (c : C) :
    (∑ i, localRoot x B R c ^ 2 * (1 - x) ^ 2 * R i c ^ 2 / squareMass (R i)) ≤
      (1 - x) / Real.exp 1 := by
  let t : D → ℝ := fun i => (1 - x) * (R i c ^ 2 / squareMass (R i))
  have ht (i : D) : 0 ≤ t i ∧ t i ≤ 1 := by
    have hp : R i c ^ 2 / squareMass (R i) ≤ 1 := (div_le_one (hS i)).2 (coordinate_sq_le_mass _ _)
    have hp0 := div_nonneg (sq_nonneg (R i c)) (hS i).le
    refine ⟨mul_nonneg (by linarith) hp0, ?_⟩
    have hh := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hx1)
    dsimp [t]
    nlinarith
  have ho := occupancy_numerator_le t ht
  have hprod : 0 ≤ ∏ i, (1 - t i) := Finset.prod_nonneg fun i _ => sub_nonneg.mpr (ht i).2
  have hsum : 0 ≤ ∑ i, t i := Finset.sum_nonneg fun i _ => (ht i).1
  have hid : (∑ i, localRoot x B R c ^ 2 * (1 - x) ^ 2 * R i c ^ 2 / squareMass (R i)) =
      (1 - x) * (B c ^ 2 * ((∑ i, t i) * ∏ i, (1 - t i))) := by
    rw [localRoot_square hx hx1 B R hS c]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [t]
    ring
  rw [hid]
  have hb := mul_le_mul_of_nonneg_right (hB c) (mul_nonneg hsum hprod)
  have h := mul_le_mul_of_nonneg_left ((by simpa using hb : B c ^ 2 * ((∑ i, t i) * ∏ i, (1 - t i)) ≤
    (∑ i, t i) * ∏ i, (1 - t i)).trans ho) (sub_nonneg.mpr hx1)
  simpa only [Real.exp_neg, div_eq_mul_inv] using h

/-- Differential contraction, including zero free children and arbitrary
Euclidean perturbations. The blocks are the explicit Jacobian formula. -/
theorem differential_contraction {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (B : C → ℝ) (hB : ∀ c, B c ^ 2 ≤ 1) (R z : D → C → ℝ)
    (hS : ∀ i, 0 < squareMass (R i)) :
    squareMass (fun c => ∑ i, jacobianBlock x (localRoot x B R) (R i) (z i) c) ≤
      ∑ i, ((1 - x) / Real.exp 1 * pointWeightSquare x (R i)) * squareMass (z i) := by
  let Y := localRoot x B R
  have hcoord (c : C) : (∑ i, jacobianBlock x Y (R i) (z i) c) ^ 2 ≤
      (1 - x) / Real.exp 1 * ∑ i, pointWeightSquare x (R i) * projection (R i) (z i) c ^ 2 := by
    let f : D → ℝ := fun i => Y c ^ 2 * (1 - x) ^ 2 * R i c ^ 2 / squareMass (R i)
    let g : D → ℝ := fun i => squareMass (R i) / excludedMass x (R i) c ^ 2 * projection (R i) (z i) c ^ 2
    have hf (i : D) : 0 ≤ f i := div_nonneg (by positivity) (hS i).le
    have hg (i : D) : 0 ≤ g i := mul_nonneg (div_nonneg (hS i).le (sq_nonneg _)) (sq_nonneg _)
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := (Finset.univ : Finset D))
      (fun i _ => hf i) (fun i _ => hg i)
      (f := f) (g := g) (r := fun i => jacobianBlock x Y (R i) (z i) c)
      (fun i _ => by
        dsimp [f, g, jacobianBlock]
        apply le_of_eq
        field_simp [(hS i).ne', (excludedMass_pos hx hx1 (R i) (hS i) c).ne']
        ring)
    have hfbound : ∑ i, f i ≤ (1 - x) / Real.exp 1 := localRoot_occupancy hx hx1 B hB R hS c
    have hgbound : ∑ i, g i ≤ ∑ i, pointWeightSquare x (R i) * projection (R i) (z i) c ^ 2 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (ratio_le_pointWeightSquare x (R i) c) (sq_nonneg _)
    exact hcs.trans (mul_le_mul hfbound hgbound (Finset.sum_nonneg fun i _ => hg i)
      (div_nonneg (sub_nonneg.mpr hx1) (Real.exp_pos _).le))
  calc
    _ ≤ ∑ c, ((1 - x) / Real.exp 1 * ∑ i, pointWeightSquare x (R i) * projection (R i) (z i) c ^ 2) :=
      Finset.sum_le_sum fun c _ => hcoord c
    _ = ∑ i, ((1 - x) / Real.exp 1 * pointWeightSquare x (R i)) * squareMass (projection (R i) (z i)) := by
      simp only [Finset.mul_sum, mul_assoc, squareMass]
      exact Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (projection_energy_le (R i) (z i) (hS i))
      (mul_nonneg (div_nonneg (sub_nonneg.mpr hx1) (Real.exp_pos _).le) (pointWeightSquare_nonneg _ _))

end
end CI2ZF.Appendix.BBR
