import ZeroFreeness.Coupling.CLMM.Transfer
import ZeroFreeness.Coupling.BBR.Parameters

/-!
# Square-root cavity messages with their finite Gibbs semantics

The numerator retains the root unary factor. The denominator is the
partition function after deleting the root. These exact conventions are
essential for the BBR differential and influence calculations.
-/
namespace ZeroFreeness.Appendix
open scoped BigOperators
open Finset Set PottsCI
open ZeroFreeness.Appendix.Girth
noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

namespace BBR
def squareMass (y : C → ℝ) : ℝ := ∑ c, y c ^ 2
def excludedMass (x : ℝ) (y : C → ℝ) (c : C) : ℝ := squareMass y - (1 - x) * y c ^ 2
def localFactor (x : ℝ) (y : C → ℝ) (c : C) : ℝ := Real.sqrt (excludedMass x y c / squareMass y)

end BBR
namespace Girth.CavityTree
open BBR

def deletedRootPartition (x : ℝ) : CavityTree C → ℝ
  | .node _ _ child => ∏ i, (child i).partition x

def ratioSquare (x : ℝ) : CavityTree C → C → ℝ
  | .node _ b child => fun c => x ^ b c * ∏ i, (1 - (1 - x) * (child i).probability x c)

def message (x : ℝ) (t : CavityTree C) (c : C) : ℝ := Real.sqrt (t.ratioSquare x c)

theorem deletedRootPartition_pos {x : ℝ} (hx : 0 < x) (t : CavityTree C) :
    0 < t.deletedRootPartition x := by
  cases t with
  | node d b child => exact Finset.prod_pos fun i _ => (child i).partition_pos hx

/-- The unnormalized restricted contribution retains its unary scalar. -/
theorem rootWeight_eq_deleted_mul {x : ℝ} (hx : 0 < x) (t : CavityTree C) (c : C) :
    t.rootWeight x c = t.deletedRootPartition x * t.ratioSquare x c := by
  cases t with
  | node d b child =>
    rw [Girth.CavityTree.rootWeight_node]
    have hp (i : Fin d) :
        (child i).partition x - (1 - x) * (child i).rootWeight x c =
          (child i).partition x * (1 - (1 - x) * (child i).probability x c) := by
      rw [(child i).probability_eq_gibbs hx c]
      field_simp [(child i).partition_pos hx |>.ne']
    simp_rw [hp]
    rw [Finset.prod_mul_distrib]
    unfold deletedRootPartition ratioSquare
    ring

theorem ratioSquare_eq_partition_ratio {x : ℝ} (hx : 0 < x) (t : CavityTree C) (c : C) :
    t.ratioSquare x c = t.rootWeight x c / t.deletedRootPartition x := by
  rw [t.rootWeight_eq_deleted_mul hx c]
  field_simp [t.deletedRootPartition_pos hx |>.ne']

theorem ratioSquare_pos {x : ℝ} (hx : 0 < x) (t : CavityTree C) (c : C) :
    0 < t.ratioSquare x c := by
  rw [t.ratioSquare_eq_partition_ratio hx c]
  exact div_pos (t.rootWeight_pos hx c) (t.deletedRootPartition_pos hx)

theorem message_pos {x : ℝ} (hx : 0 < x) (t : CavityTree C) (c : C) :
    0 < t.message x c := Real.sqrt_pos.2 (t.ratioSquare_pos hx c)

theorem message_sq {x : ℝ} (hx : 0 < x) (t : CavityTree C) (c : C) :
    t.message x c ^ 2 = t.ratioSquare x c := Real.sq_sqrt (t.ratioSquare_pos hx c).le

theorem squareMass_pos {x : ℝ} (hx : 0 < x) (t : CavityTree C) :
    0 < squareMass (t.message x) :=
  Finset.sum_pos (fun c _ => sq_pos_of_pos (t.message_pos hx c)) Finset.univ_nonempty

theorem partition_eq_deleted_mul_mass {x : ℝ} (hx : 0 < x) (t : CavityTree C) :
    t.partition x = t.deletedRootPartition x * squareMass (t.message x) := by
  rw [← t.sum_rootWeight x, squareMass, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [t.message_sq hx c, t.rootWeight_eq_deleted_mul hx c]

/-- The actual marginal is the normalized square of the message. -/
theorem probability_eq_square {x : ℝ} (hx : 0 < x) (t : CavityTree C) (c : C) :
    t.probability x c = t.message x c ^ 2 / squareMass (t.message x) := by
  rw [t.probability_eq_gibbs hx c, t.rootWeight_eq_deleted_mul hx c,
    t.partition_eq_deleted_mul_mass hx, t.message_sq hx c]
  exact mul_div_mul_left _ _ (t.deletedRootPartition_pos hx).ne'

theorem probability_mem {x : ℝ} (hx : 0 < x) (t : CavityTree C) (c : C) :
    t.probability x c ∈ Icc (0 : ℝ) 1 :=
  ⟨(t.probabilityLaw x hx).nonneg c, (t.probabilityLaw x hx).le_one c⟩

theorem edgeFactor_mem {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (t : CavityTree C) (c : C) :
    1 - (1 - x) * t.probability x c ∈ Icc x 1 := by
  have hp := t.probability_mem hx c
  have h0 := mul_nonneg (sub_nonneg.mpr hx1) hp.1
  have h1 := mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hp.2)
  constructor <;> nlinarith

theorem ratioSquare_bounds {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (t : CavityTree C) (c : C) :
    x ^ (t.degree + ∑ c, t.boundary c) ≤ t.ratioSquare x c ∧ t.ratioSquare x c ≤ 1 := by
  cases t with
  | node d b child =>
    have hprod : x ^ d ≤ ∏ i, (1 - (1 - x) * (child i).probability x c) := by
      have hp := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin d)))
        (fun _ _ => hx.le) (fun i _ => ((child i).edgeFactor_mem hx hx1 c).1)
      simpa using hp
    have hprod1 : (∏ i, (1 - (1 - x) * (child i).probability x c)) ≤ 1 :=
      Finset.prod_le_one (fun i _ => hx.le.trans ((child i).edgeFactor_mem hx hx1 c).1)
        (fun i _ => ((child i).edgeFactor_mem hx hx1 c).2)
    have hbc : b c ≤ ∑ a, b a := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    have hpow := pow_le_pow_of_le_one hx.le hx1 hbc
    refine ⟨?_, ?_⟩
    · change x ^ (d + ∑ a, b a) ≤ x ^ b c * _
      rw [pow_add, mul_comm (x ^ d)]
      exact mul_le_mul hpow hprod (pow_nonneg hx.le _) (pow_nonneg hx.le _)
    · exact (mul_le_mul_of_nonneg_left hprod1 (pow_nonneg hx.le _)).trans
        (by simpa using (pow_le_one₀ (n := b c) hx.le hx1))

theorem message_bounds {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (t : CavityTree C) (c : C) :
    Real.sqrt (x ^ (t.degree + ∑ c, t.boundary c)) ≤ t.message x c ∧ t.message x c ≤ 1 := by
  have h := t.ratioSquare_bounds hx hx1 c
  refine ⟨Real.sqrt_le_sqrt h.1, ?_⟩
  simpa only [Real.sqrt_one, message] using Real.sqrt_le_sqrt h.2

theorem localFactor_eq {x : ℝ} (hx : 0 < x) (t : CavityTree C) (c : C) :
    localFactor x (t.message x) c = Real.sqrt (1 - (1 - x) * t.probability x c) := by
  rw [t.probability_eq_square hx c]
  unfold localFactor excludedMass
  congr 1
  field_simp [t.squareMass_pos hx |>.ne']

/-- The exact square-root recursion with the pinned-leaf unary factors. -/
theorem message_node {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (d : ℕ) (b : C → ℕ) (child : Fin d → CavityTree C) (c : C) :
    (CavityTree.node d b child).message x c =
      Real.sqrt (x ^ b c) * ∏ i, localFactor x ((child i).message x) c := by
  simp_rw [localFactor_eq hx]
  unfold message ratioSquare
  rw [Real.sqrt_mul (pow_nonneg hx.le _), Real.sqrt_prod]
  exact fun i _ => hx.le.trans ((child i).edgeFactor_mem hx hx1 c).1

end Girth.CavityTree
end
end ZeroFreeness.Appendix
