import CI2ZF.Coupling.CV.SingleBlockerActivation
import CI2ZF.Coupling.CV.DiscountTotal

/-! The actual adjacent CV coupling contracts the geometric metric.
Every component of the drift is discharged by the preceding graph,
activation, finite-certificate and scalar theorems. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
variable {V C : Type*} [Fintype V] [Fintype C] [Nonempty V] [Nonempty C]

def optimizedAdjacentChoices (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ u, u ≠ v → X u = Y u) :
    AdjacentChoices I X Y v hroot hagree :=
  fun ω => optimizedChoice (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree)

lemma adjacent_hamCard_one (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ u, u ≠ v → X u = Y u) : hamCard X Y = 1 := by
  have hh := rootLocal_ham_one
    (activatedSet_rootLocal I X Y (fun _ => false) v (X v) (Y v) rfl rfl hroot hagree)
  change (hamCard X Y : ℝ) = 1 at hh
  exact_mod_cast hh

lemma adjacent_outputScore (I : PinningData V C) (x : ℝ) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ u, u ≠ v → X u = Y u) :
    outputScore I x X Y = vertexScore I x X Y v := by
  unfold outputScore
  rw [Finset.sum_eq_single v]
  · exact if_pos hroot
  · intro u _ huv
    exact if_neg ((fun hn => hn (hagree u huv)))
  · simp

lemma averaged_geometric_cost_le (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ u, u ≠ v → X u = Y u)
    (choice : AdjacentChoices I X Y v hroot hagree) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {Δ : ℕ} (hΔ : 0 < Δ) (hdegree : ∀ u, I.graph.degree u ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C) :
    averagedCost I X Y v hroot hagree choice x hx (geometricMetric I x) ≤
      averagedCost I X Y v hroot hagree choice x hx ham -
        (17 / (200 * Fintype.card C)) * averagedCost I X Y v hroot hagree choice x hx (outputScore I x) := by
  have hp := expectReal_mono (activityCoins I x hx) fun ω =>
    cost_le_cost (adjacentHardCoupling I X Y v hroot hagree choice ω)
      (geometricMetric_path_upper I hx hΔ hdegree hq)
  simp only [coupling_cost_sub, cost_mul_left] at hp
  rw [expectReal_sub, expectReal_mul_const] at hp
  exact hp

lemma averaged_hamming_charge_le (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ u, u ≠ v → X u = Y u)
    (choice : AdjacentChoices I X Y v hroot hagree) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ((Fintype.card V : ℝ) * Fintype.card C) *
        (averagedCost I X Y v hroot hagree choice x hx ham - 1) ≤
      expectReal (activityCoins I x hx) (fun ω => ∑ c,
        hardColourCharge (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree) (choice ω) c) := by
  have hp := expectReal_mono (activityCoins I x hx) fun ω =>
    fullHardCoupling_cost_charge_le
      (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree) (choice ω)
  rw [expectReal_mul_const, expectReal_sub, expectReal_const] at hp
  exact hp

lemma actual_geometric_coefficients (q d θ L : ℝ) (hq : q ≠ 0) (hd : d ≠ 0) :
    gammaGain (q / d) d = (17 / (200 * q)) * (q - d - 2) ∧
    gammaLoss (q / d) d θ (L / d) =
      (17 / (200 * q)) * (q - (81 / 250) * θ * L + 2 + (1 + 81 / 250) * d) := by
  unfold gammaGain gammaLoss
  constructor
  · field_simp
  · field_simp
    ring

/-- The fully assembled metric drift is bounded by the expectation of the
actual corrected colour charges. -/
theorem averaged_geometric_drift_corrected_le
    (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ u, u ≠ v → X u = Y u)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) {Δ : ℕ}
    (hΔ : 0 < Δ) (hdegree : I.DegreeBound Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C)
    {gain loss : ℝ} (hg0 : 0 ≤ gain) (hl0 : 0 ≤ loss)
    (hg : gain = gammaGain ((Fintype.card C : ℝ) / Δ) Δ)
    (hl : loss = gammaLoss ((Fintype.card C : ℝ) / Δ) Δ (1 - x)
      (lowAvailabilityMass I X Y v x / Δ)) :
    ((Fintype.card V : ℝ) * Fintype.card C) *
      (averagedCost I X Y v hroot hagree (optimizedAdjacentChoices I X Y v hroot hagree)
        x hx (geometricMetric I x) - geometricMetric I x X Y) ≤
      expectReal (activityCoins I x hx) (fun ω =>
        let h := activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree
        ∑ c, correctedHardColourCharge h (optimizedChoice h) gain loss c) := by
  let choice := optimizedAdjacentChoices I X Y v hroot hagree
  let n : ℝ := (Fintype.card V : ℝ) * Fintype.card C
  let w : ℝ := 17 / (200 * Fintype.card C)
  have hn : 0 < n := by dsimp [n]; positivity
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hd : (Δ : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hΔ)
  have hfree (u : V) : I.graph.degree u ≤ Δ :=
    (Nat.le_add_right _ _).trans (hdegree u)
  have hgeom := averaged_geometric_cost_le I X Y v hroot hagree choice x hx hΔ hfree hq
  have hham := averaged_hamming_charge_le I X Y v hroot hagree choice x hx
  have hdist : geometricMetric I x X Y = 1 - w * vertexScore I x X Y v := by
    rw [geometricMetric_adjacent I hx hΔ hfree hq (adjacent_hamCard_one I X Y v hroot hagree)]
    unfold edgeLength
    rw [adjacent_outputScore I x X Y v hroot hagree]
  have hdiscount := expected_discount_decrease_le I X Y v hroot hagree choice
    (physicalLowColours I X Y v) (by intro c hc; exact (Finset.mem_filter.mp hc).2) x hx Δ hdegree
  change vertexScore I x X Y v - averagedCost I X Y v hroot hagree choice x hx (outputScore I x) ≤
    (((Fintype.card C : ℝ) - (81 / 250) * (1 - x) * lowAvailabilityMass I X Y v x +
      2 + (1 + 81 / 250) * Δ) * vertexScore I x X Y v -
      ((Fintype.card C : ℝ) - Δ - 2) * singleBlockerTotal I x X Y v) / n at hdiscount
  obtain ⟨hg', hl'⟩ := actual_geometric_coefficients (Fintype.card C : ℝ) (Δ : ℝ) (1 - x)
    (lowAvailabilityMass I X Y v x) (by positivity) hd
  rw [← hg] at hg'
  rw [← hl] at hl'
  have hdisc := mul_le_mul_of_nonneg_left ((le_div_iff₀ hn).mp hdiscount) hw
  change w * ((vertexScore I x X Y v - averagedCost I X Y v hroot hagree choice x hx (outputScore I x)) * n) ≤ _ at hdisc
  have hdisc' : n * w *
      (vertexScore I x X Y v - averagedCost I X Y v hroot hagree choice x hx (outputScore I x)) ≤
      loss * vertexScore I x X Y v - gain * singleBlockerTotal I x X Y v := by
    rw [hg', hl']
    dsimp [w] at hdisc ⊢
    convert hdisc using 1 <;> ring
  have hLoss := mul_le_mul_of_nonneg_left
    (inputScore_le_expected_colourLoss I X Y v hroot hagree x hx) hl0
  have hGain := mul_le_mul_of_nonneg_left
    (expected_colourGain_le_singleBlockerTotal I X Y v hroot hagree x hx) hg0
  have hgeom' := mul_le_mul_of_nonneg_left hgeom hn.le
  change n * averagedCost I X Y v hroot hagree choice x hx (geometricMetric I x) ≤
    n * (averagedCost I X Y v hroot hagree choice x hx ham -
      w * averagedCost I X Y v hroot hagree choice x hx (outputScore I x)) at hgeom'
  change n * _ ≤ _ at hham
  have he := congrArg (expectReal (activityCoins I x hx))
    (funext fun ω => sum_correctedHardColourCharge
      (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree) (choice ω) gain loss)
  simp only [expectReal_sub, expectReal_add, expectReal_mul_const] at he
  change n * (averagedCost I X Y v hroot hagree choice x hx (geometricMetric I x) -
    geometricMetric I x X Y) ≤ _
  change expectReal (activityCoins I x hx) (fun ω =>
    ∑ c, correctedHardColourCharge
      (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree) (choice ω) gain loss c) = _ at he
  change n * (averagedCost I X Y v hroot hagree choice x hx (geometricMetric I x) -
    geometricMetric I x X Y) ≤ expectReal (activityCoins I x hx) (fun ω =>
      ∑ c, correctedHardColourCharge
        (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree) (choice ω) gain loss c)
  rw [hdist, he]
  change averagedCost I X Y v hroot hagree choice x hx (geometricMetric I x) ≤
    averagedCost I X Y v hroot hagree choice x hx ham -
      w * averagedCost I X Y v hroot hagree choice x hx (outputScore I x) at hgeom
  nlinarith

/-- Adjacent states have the explicit negative geometric drift claimed in
Appendix CV, after averaging the fully constructed hard couplings. -/
theorem averaged_geometric_drift_le
    (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ u, u ≠ v → X u = Y u)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) {Δ : ℕ}
    (hΔ : 125 ≤ Δ) (hdegree : I.DegreeBound Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C) :
    averagedCost I X Y v hroot hagree (optimizedAdjacentChoices I X Y v hroot hagree)
      x hx (geometricMetric I x) ≤ geometricMetric I x X Y -
        gap * Δ / ((Fintype.card V : ℝ) * Fintype.card C) := by
  let q : ℝ := Fintype.card C
  let d : ℝ := Δ
  let L : ℝ := lowAvailabilityMass I X Y v x
  let ρ : ℝ := q / d
  let θ : ℝ := 1 - x
  let φ : ℝ := L / d
  let gain : ℝ := gammaGain ρ d
  let loss : ℝ := gammaLoss ρ d θ φ
  have hd125 : 125 ≤ d := by dsimp [d]; exact_mod_cast hΔ
  have hd : 0 < d := by linarith
  have hn : 0 < (Fintype.card V : ℝ) * Fintype.card C := by positivity
  have hr : 1809 / 1000 ≤ ρ := by
    apply (le_div_iff₀ hd).mpr
    exact hq
  have hθ : θ ∈ Set.Icc (0 : ℝ) 1 := ⟨by dsimp [θ]; linarith [hx.2], by dsimp [θ]; linarith [hx.1]⟩
  have hφ : φ ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (lowAvailabilityMass_nonneg I X Y v hx.1) hd.le
    · apply (div_le_one hd).mpr
      exact (lowAvailabilityMass_le_degree I X Y v hx).trans
        (by dsimp [d]; exact_mod_cast ((Nat.le_add_right _ _).trans (hdegree v) : I.graph.degree v ≤ Δ))
  obtain ⟨hg, _, hl0, hl⟩ := geometric_coefficients_box hr hd125 hθ hφ
  have hactual := averaged_geometric_drift_corrected_le I X Y v hroot hagree x hx
    (by omega : 0 < Δ) hdegree hq (by change 0 ≤ gammaGain ρ d; linarith) hl0
    (gain := gain) (loss := loss) rfl rfl
  have henv := expected_correctedHardCharge_envelope I X Y v hroot hagree x hx hdegree hg hl
  change expectReal (activityCoins I x hx) (fun ω =>
      let h := activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree
      ∑ c, correctedHardColourCharge h (optimizedChoice h) gain loss c) ≤
    -q + θ * low gain loss * L + bulk * (d - L) at henv
  have hscalar := mul_le_mul_of_nonneg_left (scalar_closure hr hd125 hθ hφ) hd.le
  have hid : d * (-ρ + bulk * (1 - φ) + θ * φ * low gain loss) =
      -q + θ * low gain loss * L + bulk * (d - L) := by
    dsimp [ρ, φ]
    field_simp
    ring
  change d * (-ρ + bulk * (1 - φ) + θ * φ * low gain loss) ≤ d * -gap at hscalar
  rw [hid] at hscalar
  have hb := hactual.trans (henv.trans hscalar)
  have hf :
      averagedCost I X Y v hroot hagree (optimizedAdjacentChoices I X Y v hroot hagree)
        x hx (geometricMetric I x) - geometricMetric I x X Y ≤
      -(gap * Δ) / ((Fintype.card V : ℝ) * Fintype.card C) := by
    apply (le_div_iff₀ hn).mpr
    dsimp [d] at hb
    nlinarith
  rw [neg_div] at hf
  linarith

/-- The concrete adjacent common-coin coupling contracts by the exact
factor used in the CV path-coupling argument. -/
theorem averaged_geometric_contract
    (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ u, u ≠ v → X u = Y u)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) {Δ : ℕ}
    (hΔ : 125 ≤ Δ) (hdegree : I.DegreeBound Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C) :
    averagedCost I X Y v hroot hagree (optimizedAdjacentChoices I X Y v hroot hagree)
      x hx (geometricMetric I x) ≤
      (1 - gap * Δ / ((Fintype.card V : ℝ) * Fintype.card C)) * geometricMetric I x X Y := by
  have hd := averaged_geometric_drift_le I X Y v hroot hagree x hx hΔ hdegree hq
  have hfree (u : V) : I.graph.degree u ≤ Δ :=
    (Nat.le_add_right _ _).trans (hdegree u)
  have hupper := (geometricMetric_comparison I hx (by omega : 0 < Δ) hfree hq X Y).2
  have hham : ham X Y = 1 := by
    change (hamCard X Y : ℝ) = 1
    rw [adjacent_hamCard_one I X Y v hroot hagree]
    norm_num
  rw [hham] at hupper
  have hδ : 0 ≤ gap * Δ / ((Fintype.card V : ℝ) * Fintype.card C) := by
    unfold gap
    positivity
  nlinarith

end
end CI2ZF.Appendix.CV
