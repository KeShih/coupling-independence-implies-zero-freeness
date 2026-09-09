import CI2ZF.Appendix.Girth.Spectral.SchurLinear
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The Schur correction of a genuine orthogonal projection. The inverse
of the degree-zero block is constructed from its compression bound. -/
namespace CI2ZF.Appendix.Girth.Schur
open scoped InnerProductSpace
noncomputable section
variable (F E : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The four literal blocks of a self-adjoint idempotent operator. -/
structure ProjectionBlocks where
  T : F →ₗ[ℝ] F
  B : E →ₗ[ℝ] F
  Bt : F →ₗ[ℝ] E
  D : E →ₗ[ℝ] E
  T_symmetric : Symmetric T
  D_symmetric : Symmetric D
  adjoint : ∀ x y, ⟪B x, y⟫_ℝ = ⟪x, Bt y⟫_ℝ
  zero_idem : ∀ x, T (T x) + B (Bt x) = T x
  off_idem : ∀ x, T (B x) + B (D x) = B x
  off_idem' : ∀ x, Bt (T x) + D (Bt x) = Bt x
  plus_idem : ∀ x, Bt (B x) + D (D x) = D x

namespace ProjectionBlocks
variable {F E} (P : ProjectionBlocks F E)

def A : F →ₗ[ℝ] F := LinearMap.id - P.T

lemma A_apply (x : F) : P.A x = x - P.T x := rfl

lemma A_symmetric : Symmetric P.A := by
  intro x y
  simp only [A_apply, inner_sub_left, inner_sub_right]
  rw [P.T_symmetric x y]

lemma A_energy (x : F) : energy P.A x = ‖x‖ ^ 2 - energy P.T x := by
  simp only [energy, A_apply, inner_sub_right, real_inner_self_eq_norm_sq]

lemma A_coercive {r : ℝ} (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) (x : F) :
    (1 - r) * ‖x‖ ^ 2 ≤ energy P.A x := by
  rw [P.A_energy]
  linarith [hT x]

lemma A_positive {r : ℝ} (hr : r < 1) (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) :
    Positive P.A := by
  intro x
  exact (mul_nonneg (by linarith : 0 ≤ 1 - r) (sq_nonneg _)).trans (P.A_coercive hT x)

lemma A_injective {r : ℝ} (hr : r < 1) (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) :
    Function.Injective P.A := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hh := P.A_coercive hT x
  have he : energy P.A x = 0 := by simp only [energy, hx, inner_zero_right]
  rw [he] at hh
  have hn : ‖x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x‖]
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg x])

variable [FiniteDimensional ℝ F]

/-- The inverse is obtained from injectivity on the actual finite zero block. -/
def R {r : ℝ} (hr : r < 1) (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) : F →ₗ[ℝ] F :=
  (LinearEquiv.ofInjectiveEndo P.A (P.A_injective hr hT)).symm.toLinearMap

lemma A_R {r : ℝ} (hr : r < 1) (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) (x : F) :
    P.A (P.R hr hT x) = x :=
  (LinearEquiv.ofInjectiveEndo P.A (P.A_injective hr hT)).apply_symm_apply x

lemma R_A {r : ℝ} (hr : r < 1) (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) (x : F) :
    P.R hr hT (P.A x) = x :=
  (LinearEquiv.ofInjectiveEndo P.A (P.A_injective hr hT)).symm_apply_apply x

lemma R_symmetric {r : ℝ} (hr : r < 1) (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) :
    Symmetric (P.R hr hT) := by
  intro x y
  calc
    _ = ⟪P.R hr hT x, P.A (P.R hr hT y)⟫_ℝ := by rw [P.A_R]
    _ = ⟪P.A (P.R hr hT x), P.R hr hT y⟫_ℝ := (P.A_symmetric _ _).symm
    _ = _ := by rw [P.A_R]

lemma R_positive {r : ℝ} (hr : r < 1) (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) :
    Positive (P.R hr hT) := by
  intro x
  have hh := P.A_positive hr hT (P.R hr hT x)
  simpa only [energy, P.A_R, real_inner_comm (P.R hr hT x) x] using hh

/-- The literal positive-sector Schur correction. -/
def C {r : ℝ} (hr : r < 1) (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) : E →ₗ[ℝ] E :=
  P.Bt.comp ((P.R hr hT).comp P.B)

def H {r : ℝ} (hr : r < 1) (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) : E →ₗ[ℝ] E :=
  LinearMap.id - P.D - P.C hr hT

lemma C_apply {r : ℝ} (hr : r < 1) (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) (x : E) :
    P.C hr hT x = P.Bt (P.R hr hT (P.B x)) := rfl

lemma H_apply {r : ℝ} (hr : r < 1) (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) (x : E) :
    P.H hr hT x = x - P.D x - P.C hr hT x := rfl

lemma C_factor {r : ℝ} (hr : r < 1) (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) (x : E) :
    energy (P.C hr hT) x = ⟪P.B x, P.R hr hT (P.B x)⟫_ℝ := by
  exact (P.adjoint x (P.R hr hT (P.B x))).symm

lemma C_symmetric {r : ℝ} (hr : r < 1) (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) :
    Symmetric (P.C hr hT) := by
  intro x y
  simp only [C_apply]
  rw [real_inner_comm, ← P.adjoint, ← P.R_symmetric hr hT, real_inner_comm, P.adjoint]

lemma C_positive {r : ℝ} (hr : r < 1) (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) :
    Positive (P.C hr hT) := by
  intro x
  rw [P.C_factor]
  exact P.R_positive hr hT (P.B x)

omit [FiniteDimensional ℝ F] in
lemma A_B (x : E) : P.A (P.B x) = P.B (P.D x) := by
  rw [A_apply]
  have hh := P.off_idem x
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hh.symm)

omit [FiniteDimensional ℝ F] in
lemma D_Bt (x : F) : P.D (P.Bt x) = P.Bt (P.A x) := by
  rw [A_apply, map_sub]
  have hh := P.off_idem' x
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hh)

omit [FiniteDimensional ℝ F] in
lemma B_Bt (x : F) : P.B (P.Bt x) = P.A (P.T x) := by
  rw [A_apply]
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using P.zero_idem x)

lemma T_R {r : ℝ} (hr : r < 1) (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) (x : F) :
    P.T (P.R hr hT x) = P.R hr hT x - x := by
  have hh := P.A_R hr hT x
  rw [A_apply] at hh
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (sub_eq_iff_eq_add.mp hh).symm)

lemma C_D {r : ℝ} (hr : r < 1) (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) (x : E) :
    P.C hr hT (P.D x) = P.Bt (P.B x) := by
  rw [C_apply, ← P.A_B, P.R_A]

lemma D_C {r : ℝ} (hr : r < 1) (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) (x : E) :
    P.D (P.C hr hT x) = P.Bt (P.B x) := by
  rw [C_apply, P.D_Bt, P.A_R]

lemma C_C {r : ℝ} (hr : r < 1) (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) (x : E) :
    P.C hr hT (P.C hr hT x) = P.C hr hT x - P.Bt (P.B x) := by
  simp only [C_apply]
  rw [P.B_Bt, P.R_A, P.T_R, map_sub]

lemma H_symmetric {r : ℝ} (hr : r < 1) (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) :
    Symmetric (P.H hr hT) := by
  intro x y
  simp only [H_apply, inner_sub_left, inner_sub_right]
  rw [P.D_symmetric x y, P.C_symmetric hr hT x y]

/-- The Schur complement is an exact orthogonal projection. -/
theorem H_projection {r : ℝ} (hr : r < 1) (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) :
    Projection (P.H hr hT) := by
  refine ⟨P.H_symmetric hr hT, ?_⟩
  intro x
  simp only [H_apply, map_sub, P.D_C hr hT, P.C_D hr hT, P.C_C hr hT]
  have hh := P.plus_idem x
  have he : P.D (P.D x) = P.D x - P.Bt (P.B x) :=
    eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hh)
  rw [he]
  abel

lemma H_add_C {r : ℝ} (hr : r < 1) (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) :
    P.H hr hT + P.C hr hT = LinearMap.id - P.D := by
  unfold H
  abel

/-- A vector fixed by the original projection has no Schur-complement
component in its positive-sector coordinate. -/
theorem H_eq_zero_of_fixed {r : ℝ} (hr : r < 1) (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2)
    (x : F) (a : E) (hzero : P.T x + P.B a = x) (hplus : P.Bt x + P.D a = a) :
    P.H hr hT a = 0 := by
  have he : P.B a = P.A x := by
    rw [A_apply]
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hzero)
  rw [H_apply, C_apply, he, P.R_A]
  calc
    _ = (P.Bt x + P.D a) - P.D a - P.Bt x :=
      congrArg (fun z => z - P.D a - P.Bt x) hplus.symm
    _ = 0 := by abel

omit [FiniteDimensional ℝ F] in
lemma Bt_norm_sq (x : F) : ‖P.Bt x‖ ^ 2 = energy P.T x - ‖P.T x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← P.adjoint, P.B_Bt, A_apply, inner_sub_left]
  rw [P.T_symmetric (P.T x) x, real_inner_self_eq_norm_sq, real_inner_comm x (P.T x)]
  rfl

omit [FiniteDimensional ℝ F] in
lemma Bt_norm_bound {r : ℝ} (hr : r < 1)
    (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) (x : F) :
    ‖P.Bt x‖ ^ 2 ≤ r * energy P.A x := by
  by_cases hx : x = 0
  · subst x
    simp only [map_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, energy, inner_zero_left, mul_zero, le_refl]
  have hn : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hb := hT x
  have ha : 0 ≤ ‖x‖ ^ 2 - energy P.T x := by
    have hmul := mul_le_mul_of_nonneg_right hr.le (sq_nonneg ‖x‖)
    linarith
  have hp := mul_nonneg (sub_nonneg.mpr hb) ha
  have hc := real_inner_mul_inner_self_le x (P.T x)
  simp only [real_inner_self_eq_norm_sq] at hc
  change energy P.T x * energy P.T x ≤ ‖x‖ ^ 2 * ‖P.T x‖ ^ 2 at hc
  rw [P.Bt_norm_sq, P.A_energy]
  apply (mul_le_mul_iff_right₀ hn).mp
  nlinarith

lemma C_norm_bound {r : ℝ} (hr : r < 1)
    (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) (x : E) :
    ‖P.C hr hT x‖ ^ 2 ≤ r * energy (P.C hr hT) x := by
  have hh := P.Bt_norm_bound hr hT (P.R hr hT (P.B x))
  have he : energy P.A (P.R hr hT (P.B x)) = energy (P.C hr hT) x := by
    rw [P.C_factor, energy, P.A_R, real_inner_comm]
  rw [he] at hh
  exact hh

/-- The Schur correction inherits the compression bound of P₀₀.
This is derived from the block projection identities and Cauchy--Schwarz. -/
theorem C_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) (x : E) :
    energy (P.C hr hT) x ≤ r * ‖x‖ ^ 2 := by
  have hn := P.C_norm_bound hr hT x
  have hc := real_inner_mul_inner_self_le x (P.C hr hT x)
  simp only [real_inner_self_eq_norm_sq] at hc
  change energy (P.C hr hT) x * energy (P.C hr hT) x ≤
    ‖x‖ ^ 2 * ‖P.C hr hT x‖ ^ 2 at hc
  have hm := mul_le_mul_of_nonneg_left hn (sq_nonneg ‖x‖)
  by_contra! hh
  have he : 0 < energy (P.C hr hT) x := (mul_nonneg hr0 (sq_nonneg _)).trans_lt hh
  nlinarith

lemma R_energy_bound {r : ℝ} (hr : r < 1)
    (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) (x : F) :
    energy (P.R hr hT) x ≤ ‖x‖ ^ 2 / (1 - r) := by
  have hα : 0 < 1 - r := sub_pos.mpr hr
  have he := P.R_positive hr hT x
  have hco := P.A_coercive hT (P.R hr hT x)
  have hid : energy P.A (P.R hr hT x) = energy (P.R hr hT) x := by
    rw [energy, P.A_R, real_inner_comm]
    rfl
  rw [hid] at hco
  have hc := real_inner_mul_inner_self_le x (P.R hr hT x)
  simp only [real_inner_self_eq_norm_sq] at hc
  change energy (P.R hr hT) x * energy (P.R hr hT) x ≤
    ‖x‖ ^ 2 * ‖P.R hr hT x‖ ^ 2 at hc
  have hm := mul_le_mul_of_nonneg_left hc hα.le
  have hm' := mul_le_mul_of_nonneg_left hco (sq_nonneg ‖x‖)
  apply (le_div_iff₀ hα).mpr
  by_contra! hh
  have hpos : 0 < energy (P.R hr hT) x := by nlinarith [sq_nonneg ‖x‖]
  nlinarith

lemma C_le_B_norm {r : ℝ} (hr : r < 1)
    (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) (x : E) :
    energy (P.C hr hT) x ≤ ‖P.B x‖ ^ 2 / (1 - r) := by
  rw [P.C_factor]
  exact P.R_energy_bound hr hT (P.B x)

lemma H_energy {r : ℝ} (hr : r < 1)
    (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) (x : E) :
    energy (P.H hr hT) x = ‖x‖ ^ 2 - energy P.D x - energy (P.C hr hT) x := by
  simp only [energy, H_apply, inner_sub_right, real_inner_self_eq_norm_sq]

lemma H_lower_of_D {r ε : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hT : ∀ x, energy P.T x ≤ r * ‖x‖ ^ 2) (x : E)
    (hD : energy P.D x ≤ ε * ‖x‖ ^ 2) :
    (1 - (r + ε)) * ‖x‖ ^ 2 ≤ energy (P.H hr hT) x := by
  rw [P.H_energy]
  linarith [P.C_le hr0 hr hT x]

section Ambient
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
omit [FiniteDimensional ℝ F]

/-- Extract all four block identities from one actual ambient orthogonal
projection and an adjoint pair of coordinate embeddings. -/
def ofSplit (Q : G →ₗ[ℝ] G) (hQ : Projection Q)
    (i0 : F →ₗ[ℝ] G) (ip : E →ₗ[ℝ] G) (e0 : G →ₗ[ℝ] F) (ep : G →ₗ[ℝ] E)
    (h0 : ∀ z x, ⟪e0 z, x⟫_ℝ = ⟪z, i0 x⟫_ℝ)
    (hp : ∀ z a, ⟪ep z, a⟫_ℝ = ⟪z, ip a⟫_ℝ)
    (hsplit : ∀ z, i0 (e0 z) + ip (ep z) = z) : ProjectionBlocks F E where
  T := e0.comp (Q.comp i0)
  B := e0.comp (Q.comp ip)
  Bt := ep.comp (Q.comp i0)
  D := ep.comp (Q.comp ip)
  T_symmetric := by
    intro x y
    change ⟪e0 (Q (i0 x)), y⟫_ℝ = ⟪x, e0 (Q (i0 y))⟫_ℝ
    rw [h0, hQ.symmetric]
    rw [real_inner_comm (Q (i0 y)) (i0 x), ← h0, real_inner_comm x (e0 (Q (i0 y)))]
  D_symmetric := by
    intro x y
    change ⟪ep (Q (ip x)), y⟫_ℝ = ⟪x, ep (Q (ip y))⟫_ℝ
    rw [hp, hQ.symmetric]
    rw [real_inner_comm (Q (ip y)) (ip x), ← hp, real_inner_comm x (ep (Q (ip y)))]
  adjoint := by
    intro x y
    change ⟪e0 (Q (ip x)), y⟫_ℝ = ⟪x, ep (Q (i0 y))⟫_ℝ
    rw [h0, hQ.symmetric]
    rw [real_inner_comm (Q (i0 y)) (ip x), ← hp, real_inner_comm x (ep (Q (i0 y)))]
  zero_idem := by
    intro x
    change e0 (Q (i0 (e0 (Q (i0 x))))) + e0 (Q (ip (ep (Q (i0 x))))) = e0 (Q (i0 x))
    rw [← map_add, ← map_add, hsplit, hQ.idem]
  off_idem := by
    intro x
    change e0 (Q (i0 (e0 (Q (ip x))))) + e0 (Q (ip (ep (Q (ip x))))) = e0 (Q (ip x))
    rw [← map_add, ← map_add, hsplit, hQ.idem]
  off_idem' := by
    intro x
    change ep (Q (i0 (e0 (Q (i0 x))))) + ep (Q (ip (ep (Q (i0 x))))) = ep (Q (i0 x))
    rw [← map_add, ← map_add, hsplit, hQ.idem]
  plus_idem := by
    intro x
    change ep (Q (i0 (e0 (Q (ip x))))) + ep (Q (ip (ep (Q (ip x))))) = ep (Q (ip x))
    rw [← map_add, ← map_add, hsplit, hQ.idem]

end Ambient

end ProjectionBlocks
end
end CI2ZF.Appendix.Girth.Schur
