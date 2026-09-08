import CI2ZF.Appendix.EdgeFiniteStep

/-! Complete coupling-independence bounds for the finite weighted endpoint
slot model. No contraction estimate is assumed: the proof inducts on the
number of free edges using the actual exposure and conditional laws. -/
namespace CI2ZF.Appendix.Edge.FiniteSystem
open PottsCI PottsCI.FinDist Finset FiniteLaw
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V E A L : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype L] [Nonempty A]
local instance (priority := 2000) : DecidableEq V := Classical.decEq V
local instance (priority := 2000) : DecidableEq E := Classical.decEq E
local instance (priority := 2000) : DecidableEq A := Classical.decEq A
local instance (priority := 2000) : DecidableEq L := Classical.decEq L

lemma oneLabelBound_nonneg {d : ℝ} (hd : 1 ≤ d) (n : ℕ) : 0 ≤ oneLabelBound d n := by
  have hp : 0 ≤ (d - 1) / d := div_nonneg (by linarith) (by linarith)
  have hl : (d - 1) / d ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  exact mul_nonneg (div_nonneg (by linarith) (by norm_num))
    (sub_nonneg.mpr (pow_le_one₀ hp hl))

/-- The exact finite-n envelope from the appendix, for genuine Gibbs laws. -/
theorem single_replacement_ci_bound (n : ℕ) (I : FiniteSystem V E A L)
    {Δ : ℕ} (hΔ : 1 ≤ Δ) (hcard : Fintype.card E ≤ n) :
    I.SingleReplacementCI Δ (oneLabelBound Δ n) := by
  induction n generalizing E with
  | zero =>
    intro B v a b ha hb hA hB
    rw [oneLabelBound_zero]
    have hc : Fintype.card E = 0 := Nat.eq_zero_of_le_zero hcard
    apply W_le_bound ham_nonneg
    intro σ τ
    exact (ham_le_card σ τ).trans_eq (by exact_mod_cast hc)
  | succ n ih =>
    have hd : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    rw [oneLabelBound_succ (by linarith : (Δ : ℝ) ≠ 0)]
    apply I.single_replacement_step hΔ (oneLabelBound_nonneg hd n)
    intro e
    have hc : Fintype.card {f : E // f ≠ e} < Fintype.card E :=
      Fintype.card_subtype_lt (p := fun f : E => f ≠ e) (x := e) (by simp)
    apply ih (I.remove e)
    exact Nat.le_of_lt_succ (hc.trans_le hcard)

/-- A single occupied-label replacement has a graph-size-independent cost. -/
theorem single_replacement_ci (I : FiniteSystem V E A L) {Δ : ℕ} (hΔ : 1 ≤ Δ) :
    I.SingleReplacementCI Δ (((Δ : ℝ) - 1) / 2) := by
  intro B v a b ha hb hA hB
  have hh := I.single_replacement_ci_bound (Fintype.card E) hΔ le_rfl B v a b ha hb hA hB
  exact hh.trans (oneLabelBound_le (by exact_mod_cast hΔ) _)

/-- Conditioning an entire edge state changes one label at each endpoint.
The true residual Gibbs laws therefore admit Hamming transport at most Δ−1. -/
theorem root_state_ci (I : FiniteSystem V E A L) {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (B : Boundary V L) (hB : I.Bounds B Δ) (e : E) (a b : A)
    (hac : I.Compatible B e a) (hbc : I.Compatible B e b) :
    W ham (I.pinnedLaw B hB e a) (I.pinnedLaw B hB e b) ≤ (Δ : ℝ) - 1 := by
  obtain ⟨v, w, hvw, he⟩ := Finset.card_eq_two.mp (I.endpoints_card e)
  have hv : v ∈ I.endpoints e := by rw [he]; simp
  have hw : w ∈ I.endpoints e := by rw [he]; simp
  have hPa := I.pinBoundary_pair B e a hvw he
  have hPb := I.pinBoundary_pair B e b hvw he
  have hBa := hB.pin I B e a
  have hBb := hB.pin I B e b
  have hBa' : (I.remove e).Bounds
      (addBoundary (addBoundary B v (I.label e v a)) w (I.label e w a)) Δ := hPa ▸ hBa
  have hBb' : (I.remove e).Bounds
      (addBoundary (addBoundary B v (I.label e v b)) w (I.label e w b)) Δ := hPb ▸ hBb
  have hh := I.W_two_endpoint_replacements e hv hw hvw ((I.remove e).single_replacement_ci hΔ)
    B (I.label e v a) (I.label e v b) (I.label e w a) (I.label e w b)
    (hac v hv) (hbc v hv) (hac w hw) (hbc w hw) hBa' hBb'
  have hcost : W ham (I.pinnedLaw B hB e a) (I.pinnedLaw B hB e b) ≤ 2 * (((Δ : ℝ) - 1) / 2) := by
    simpa only [pinnedLaw, ← hPa, ← hPb] using hh
  calc
    _ ≤ 2 * (((Δ : ℝ) - 1) / 2) := hcost
    _ = _ := by ring

end
end CI2ZF.Appendix.Edge.FiniteSystem
