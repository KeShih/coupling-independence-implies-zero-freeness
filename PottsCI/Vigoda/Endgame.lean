import PottsCI.PathCoupling

/-!
# The child--middle endgame for the near-Vigoda coupling estimate

This file formalizes only the algebraic endgame of the near-Vigoda argument.
In particular, `hcomponentA` and `hcomponentB` below are explicit hypotheses:
they are the one-step component-coupling estimates for adjacent configurations.
No component coupling, and hence no near-Vigoda parameter region by itself, is
proved in this file.

From those local inputs, path coupling gives contraction for arbitrary starting
laws.  Stationary comparison then bounds each child law against the common
middle law, and the triangle inequality bounds the two child laws.
-/

namespace PottsCI
namespace Vigoda

open FinDist

variable {V : Type*} {C : Type*}
variable [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

private def reverseCoupling {S : Type*} [Fintype S]
    {mu nu : FinDist S} (gamma : FinDist.Coupling mu nu) :
    FinDist.Coupling nu mu where
  w := fun y x => gamma.w x y
  nonneg := fun y x => gamma.nonneg x y
  sum_row := gamma.sum_col
  sum_col := gamma.sum_row

private lemma reverseCoupling_cost {S : Type*} [Fintype S]
    {mu nu : FinDist S} {d : S → S → ℝ}
    (hsymm : ∀ x y, d x y = d y x) (gamma : FinDist.Coupling mu nu) :
    (reverseCoupling gamma).cost d = gamma.cost d := by
  unfold FinDist.Coupling.cost reverseCoupling
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [hsymm y x]

private lemma W_comm_of_comm {S : Type*} [Fintype S]
    {d : S → S → ℝ} (hd : ∀ x y, 0 ≤ d x y)
    (hsymm : ∀ x y, d x y = d y x) (mu nu : FinDist S) :
    W d mu nu = W d nu mu := by
  apply le_antisymm
  · apply le_W
    intro gamma
    calc
      W d mu nu ≤ (reverseCoupling gamma).cost d := W_le_cost hd _
      _ = gamma.cost d := reverseCoupling_cost hsymm gamma
  · apply le_W
    intro gamma
    calc
      W d nu mu ≤ (reverseCoupling gamma).cost d := W_le_cost hd _
      _ = gamma.cost d := reverseCoupling_cost hsymm gamma

/-- A local adjacent-state contraction input, together with rowwise comparison
to a common middle kernel, bounds the stationary child law against the middle
law.  The local input is deliberately a hypothesis: in the Potts application
it is supplied by the one-step Vigoda component coupling. -/
theorem child_middle_of_component_input
    (KChild KMiddle : (V → C) → FinDist (V → C))
    (piChild piMiddle : FinDist (V → C))
    (hpiChild : IsStationary KChild piChild)
    (hpiMiddle : IsStationary KMiddle piMiddle)
    {kappa D : ℝ} (hkappa_pos : 0 < kappa) (hkappa_le_one : kappa ≤ 1)
    (hcomponent : ∀ X Y : V → C, hamCard X Y = 1 →
      W ham (KChild X) (KChild Y) ≤ 1 - kappa)
    (hrow : ∀ X, W ham (KChild X) (KMiddle X) ≤ D) :
    W ham piChild piMiddle ≤ D / kappa := by
  have hcontraction : ∀ alpha beta : FinDist (V → C),
      W ham (alpha.bind KChild) (beta.bind KChild) ≤
        (1 - kappa) * W ham alpha beta := by
    intro alpha beta
    exact W_ham_bind_contract KChild (sub_nonneg.mpr hkappa_le_one)
      hcomponent alpha beta
  have hcomparison := stationary_comparison ham_nonneg ham_triangle
    KChild KMiddle piChild piMiddle hpiChild hpiMiddle
    (sub_nonneg.mpr hkappa_le_one) (by linarith : 1 - kappa < 1)
    hcontraction hrow
  simpa only [sub_sub_cancel] using hcomparison

/-- Applying the child--middle estimate to two children and joining through
the same middle law gives the factor `2`. -/
theorem two_children_of_component_inputs
    (KChildA KChildB KMiddle : (V → C) → FinDist (V → C))
    (piChildA piChildB piMiddle : FinDist (V → C))
    (hpiChildA : IsStationary KChildA piChildA)
    (hpiChildB : IsStationary KChildB piChildB)
    (hpiMiddle : IsStationary KMiddle piMiddle)
    {kappa D : ℝ} (hkappa_pos : 0 < kappa) (hkappa_le_one : kappa ≤ 1)
    (hcomponentA : ∀ X Y : V → C, hamCard X Y = 1 →
      W ham (KChildA X) (KChildA Y) ≤ 1 - kappa)
    (hcomponentB : ∀ X Y : V → C, hamCard X Y = 1 →
      W ham (KChildB X) (KChildB Y) ≤ 1 - kappa)
    (hrowA : ∀ X, W ham (KChildA X) (KMiddle X) ≤ D)
    (hrowB : ∀ X, W ham (KChildB X) (KMiddle X) ≤ D) :
    W ham piChildA piChildB ≤ 2 * D / kappa := by
  have hA : W ham piChildA piMiddle ≤ D / kappa :=
    child_middle_of_component_input KChildA KMiddle piChildA piMiddle
      hpiChildA hpiMiddle hkappa_pos hkappa_le_one hcomponentA hrowA
  have hB : W ham piChildB piMiddle ≤ D / kappa :=
    child_middle_of_component_input KChildB KMiddle piChildB piMiddle
      hpiChildB hpiMiddle hkappa_pos hkappa_le_one hcomponentB hrowB
  have htriangle : W ham piChildA piChildB ≤
      W ham piChildA piMiddle + W ham piMiddle piChildB :=
    W_triangle ham_nonneg ham_nonneg ham_nonneg ham_triangle _ _ _
  have hsymm : W ham piMiddle piChildB = W ham piChildB piMiddle :=
    W_comm_of_comm ham_nonneg ham_comm _ _
  rw [hsymm] at htriangle
  calc
    W ham piChildA piChildB
        ≤ W ham piChildA piMiddle + W ham piChildB piMiddle := htriangle
    _ ≤ D / kappa + D / kappa := add_le_add hA hB
    _ = 2 * D / kappa := by ring

/-! ## The near-Vigoda constants -/

/-- The concrete child--middle algebra after substituting

`kappa = (q - (11/6) * theta * Delta) / (n * q)` and
`D = theta * Delta / (n * q)`.

Here `n` is the positive real scale instantiated by the number of free
vertices.  The component-coupling estimate remains an explicit hypothesis. -/
theorem nearVigoda_child_middle_endgame
    (KChild KMiddle : (V → C) → FinDist (V → C))
    (piChild piMiddle : FinDist (V → C))
    (hpiChild : IsStationary KChild piChild)
    (hpiMiddle : IsStationary KMiddle piMiddle)
    (theta Delta q n : ℝ)
    (htheta : 0 ≤ theta) (hDelta : 0 ≤ Delta)
    (hq : 0 < q) (hn : 1 ≤ n)
    (hgap : 0 < q - (11 / 6 : ℝ) * theta * Delta)
    (hcomponent : ∀ X Y : V → C, hamCard X Y = 1 →
      W ham (KChild X) (KChild Y) ≤
        1 - (q - (11 / 6 : ℝ) * theta * Delta) / (n * q))
    (hrow : ∀ X, W ham (KChild X) (KMiddle X) ≤ theta * Delta / (n * q)) :
    W ham piChild piMiddle ≤
      theta * Delta / (q - (11 / 6 : ℝ) * theta * Delta) := by
  have hn_pos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hnq_pos : 0 < n * q := mul_pos hn_pos hq
  have hpenalty : 0 ≤ (11 / 6 : ℝ) * theta * Delta :=
    mul_nonneg (mul_nonneg (by norm_num) htheta) hDelta
  have hgap_le_q : q - (11 / 6 : ℝ) * theta * Delta ≤ q := by
    linarith
  have hq_le_nq : q ≤ n * q := by
    nlinarith
  have hkappa_le_one :
      (q - (11 / 6 : ℝ) * theta * Delta) / (n * q) ≤ 1 := by
    rw [div_le_one hnq_pos]
    exact hgap_le_q.trans hq_le_nq
  have hbound := child_middle_of_component_input KChild KMiddle piChild piMiddle
    hpiChild hpiMiddle (div_pos hgap hnq_pos) hkappa_le_one hcomponent hrow
  have hnq_ne : n * q ≠ 0 := ne_of_gt hnq_pos
  have hgap_ne : q - (11 / 6 : ℝ) * theta * Delta ≠ 0 := ne_of_gt hgap
  calc
    W ham piChild piMiddle
        ≤ (theta * Delta / (n * q)) /
          ((q - (11 / 6 : ℝ) * theta * Delta) / (n * q)) := hbound
    _ = theta * Delta / (q - (11 / 6 : ℝ) * theta * Delta) := by
      field_simp

/-- The two-child near-Vigoda endgame.  It proves only the implication from
the stated one-step component-coupling hypotheses to coupling independence. -/
theorem nearVigoda_two_children_endgame
    (KChildA KChildB KMiddle : (V → C) → FinDist (V → C))
    (piChildA piChildB piMiddle : FinDist (V → C))
    (hpiChildA : IsStationary KChildA piChildA)
    (hpiChildB : IsStationary KChildB piChildB)
    (hpiMiddle : IsStationary KMiddle piMiddle)
    (theta Delta q n : ℝ)
    (htheta : 0 ≤ theta) (hDelta : 0 ≤ Delta)
    (hq : 0 < q) (hn : 1 ≤ n)
    (hgap : 0 < q - (11 / 6 : ℝ) * theta * Delta)
    (hcomponentA : ∀ X Y : V → C, hamCard X Y = 1 →
      W ham (KChildA X) (KChildA Y) ≤
        1 - (q - (11 / 6 : ℝ) * theta * Delta) / (n * q))
    (hcomponentB : ∀ X Y : V → C, hamCard X Y = 1 →
      W ham (KChildB X) (KChildB Y) ≤
        1 - (q - (11 / 6 : ℝ) * theta * Delta) / (n * q))
    (hrowA : ∀ X, W ham (KChildA X) (KMiddle X) ≤ theta * Delta / (n * q))
    (hrowB : ∀ X, W ham (KChildB X) (KMiddle X) ≤ theta * Delta / (n * q)) :
    W ham piChildA piChildB ≤
      2 * theta * Delta / (q - (11 / 6 : ℝ) * theta * Delta) := by
  have hn_pos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hnq_pos : 0 < n * q := mul_pos hn_pos hq
  have hpenalty : 0 ≤ (11 / 6 : ℝ) * theta * Delta :=
    mul_nonneg (mul_nonneg (by norm_num) htheta) hDelta
  have hgap_le_q : q - (11 / 6 : ℝ) * theta * Delta ≤ q := by
    linarith
  have hq_le_nq : q ≤ n * q := by
    nlinarith
  have hkappa_le_one :
      (q - (11 / 6 : ℝ) * theta * Delta) / (n * q) ≤ 1 := by
    rw [div_le_one hnq_pos]
    exact hgap_le_q.trans hq_le_nq
  have hbound := two_children_of_component_inputs
    KChildA KChildB KMiddle piChildA piChildB piMiddle
    hpiChildA hpiChildB hpiMiddle (div_pos hgap hnq_pos) hkappa_le_one
    hcomponentA hcomponentB hrowA hrowB
  have hnq_ne : n * q ≠ 0 := ne_of_gt hnq_pos
  have hgap_ne : q - (11 / 6 : ℝ) * theta * Delta ≠ 0 := ne_of_gt hgap
  calc
    W ham piChildA piChildB
        ≤ 2 * (theta * Delta / (n * q)) /
          ((q - (11 / 6 : ℝ) * theta * Delta) / (n * q)) := hbound
    _ = 2 * theta * Delta / (q - (11 / 6 : ℝ) * theta * Delta) := by
      field_simp

end Vigoda
end PottsCI
