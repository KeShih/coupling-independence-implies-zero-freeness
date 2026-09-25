import ZeroFreeness.Coupling.Vigoda.RegularColourCharge
import ZeroFreeness.Coupling.Vigoda.VigodaFlexibleFormula

/-! The actual two-neighbour regular-colour case and the complete regular
colour charge bound. -/
namespace ZeroFreeness.RegularColourCharge
open Finset PottsCI PottsCI.Vigoda RootComponentGeometry VigodaArithmetic
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [Fintype C]

lemma perColourCharge_le_familyCosts {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (hN : (rootNeighbours FX X v c).Nonempty) :
    perColourCharge h hca hcb ≤ rootCharge FX X v c + rootCharge FY Y v c +
      familyResidualCost FX X v c + familyResidualCost FY Y v c := by
  have hsaving : 0 ≤ ∑ i, IncidenceMatching.atIncidence (componentOf FX X v c)
      (oppositeComponentOf h hca hcb) (fun S => residual FX X v c S)
      (fun S => residual FY Y v c S) i := by
    exact sum_nonneg fun i _ => IncidenceMatching.atIncidence_nonneg _ _ _ _
      (residual_nonneg FX X v c (by rwa [h.X_root]))
      (residual_nonneg FY Y v c (by rwa [h.Y_root])) i
  simp only [perColourCharge, if_pos hN, offRootCharge, familyResidualCost]
  linarith

lemma perColourCharge_le_two_shared_left {FX FY : HardListInstance V C} {X Y : V → C}
    {v u w : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (huw : u ≠ w)
    (hN : rootNeighbours FX X v c = {u, w})
    (hST : offRootComponent FX X v (X v) c u = offRootComponent FX X v (X v) c w) :
    perColourCharge h hca hcb ≤ 8 / 3 := by
  have hNY : rootNeighbours FY Y v c = {u, w} := by rwa [← h.rootNeighbours_eq hca hcb]
  have hleft := familyResidualCost_le_half_of_shared FX X v u w c
    (by rwa [h.X_root]) huw hN hST
  have hroot := rootCharge_le_sixth_two_neighbours FY Y v u w c (by rwa [h.Y_root]) hNY
  have hright := familyResidualCost_le_two FY Y v u w c hNY
  have htotal := perColourCharge_le_familyCosts h hca hcb (by rw [hN]; exact insert_nonempty _ _)
  linarith

lemma perColourCharge_le_two_shared_right {FX FY : HardListInstance V C} {X Y : V → C}
    {v u w : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (huw : u ≠ w)
    (hN : rootNeighbours FX X v c = {u, w})
    (hST : offRootComponent FY Y v (Y v) c u = offRootComponent FY Y v (Y v) c w) :
    perColourCharge h hca hcb ≤ 8 / 3 := by
  have hNY : rootNeighbours FY Y v c = {u, w} := by rwa [← h.rootNeighbours_eq hca hcb]
  have hright := familyResidualCost_le_half_of_shared FY Y v u w c
    (by rwa [h.Y_root]) huw hNY hST
  have hroot := rootCharge_le_sixth_two_neighbours FX X v u w c (by rwa [h.X_root]) hN
  have hleft := familyResidualCost_le_two FX X v u w c hN
  have htotal := perColourCharge_le_familyCosts h hca hcb (by rw [hN]; exact insert_nonempty _ _)
  linarith

def feasibleBool (F : HardListInstance V C) (X : V → C) (v : V) (c : C) (S : Finset V) : Bool :=
  decide (flipAllowed F S (flipConfiguration X S (X v) c))

def picksFirst (F : HardListInstance V C) (X : V → C) (v u : V) (c : C) : Bool :=
  decide (largestPiece F X v c = offRootComponent F X v (X v) c u)

theorem two_piece_formulas (F : HardListInstance V C) (X : V → C) (v u w : V) (c : C)
    (hc : c ≠ X v) (hav : c ∈ F.list v) (hN : rootNeighbours F X v c = {u, w})
    (hST : offRootComponent F X v (X v) c u ≠ offRootComponent F X v (X v) c w) :
    let S := offRootComponent F X v (X v) c u
    let T := offRootComponent F X v (X v) c w
    let f := feasibleBool F X v c S
    let g := feasibleBool F X v c T
    let p := picksFirst F X v u c
    (if p then T.card ≤ S.card else S.card ≤ T.card) ∧
    rootCharge F X v c = flexibleRootCost S.card T.card f g p ∧
    residual F X v c S = flexibleFirstResidual S.card T.card f g p ∧
    residual F X v c T = flexibleSecondResidual S.card T.card f g p := by
  dsimp only
  let S := offRootComponent F X v (X v) c u
  let T := offRootComponent F X v (X v) c w
  have hF : rootFamily F X v c = {S, T} := by simp [rootFamily, hN, S, T]
  have hn : (rootNeighbours F X v c).Nonempty := by rw [hN]; exact insert_nonempty _ _
  have hS : S ∈ rootFamily F X v c := by rw [hF]; simp
  have hT : T ∈ rootFamily F X v c := by rw [hF]; simp
  have hsize : (flipSet F.graph X v c).card = 1 + S.card + T.card :=
    root_flipSet_card_two_neighbours F X v u w c hc hN hST
  have hrate : rootRate F X v c = familyRootRate S.card T.card
      (feasibleBool F X v c S) (feasibleBool F X v c T) := by
    unfold rootRate familyRootRate feasibleBool
    rw [root_flipAllowed_iff F X v c hc, hF]
    simp [hav, hsize, Bool.and_eq_true]
  have hmax := largestPiece_mem F X v c hn
  rw [hF, mem_insert, mem_singleton] at hmax
  by_cases hp : largestPiece F X v c = S
  · have hge := largestPiece_max F X v c hn T hT
    rw [hp] at hge
    have hTne : T ≠ largestPiece F X v c := by rw [hp]; exact hST.symm
    have hpB : picksFirst F X v u c = true := by simp [picksFirst, hp, S]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [picksFirst, S, hp] using hge
    · unfold rootCharge flexibleRootCost
      rw [hsize, hp, hrate]
      simp only [picksFirst, show largestPiece F X v c = offRootComponent F X v (X v) c u from hp,
        decide_true, ↓reduceIte]
      push_cast
      ring
    · change residual F X v c S = flexibleFirstResidual S.card T.card
        (feasibleBool F X v c S) (feasibleBool F X v c T) (picksFirst F X v u c)
      unfold residual flexibleFirstResidual
      rw [if_pos hp.symm, hpB, hrate]
      simp [pieceRate, feasibleBool]
    · change residual F X v c T = flexibleSecondResidual S.card T.card
        (feasibleBool F X v c S) (feasibleBool F X v c T) (picksFirst F X v u c)
      unfold residual flexibleSecondResidual
      rw [if_neg hTne, hpB]
      simp [pieceRate, feasibleBool]
  · have hpT : largestPiece F X v c = T := hmax.resolve_left hp
    have hge := largestPiece_max F X v c hn S hS
    rw [hpT] at hge
    have hSne : S ≠ largestPiece F X v c := by rw [hpT]; exact hST
    have hpB : picksFirst F X v u c = false := by
      change decide (largestPiece F X v c = S) = false
      simp [hp]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [picksFirst, S, hp] using hge
    · unfold rootCharge flexibleRootCost
      rw [hsize, hpT, hrate]
      simp only [picksFirst, show ¬largestPiece F X v c = offRootComponent F X v (X v) c u from hp,
        decide_false, Bool.false_eq_true, ↓reduceIte]
      push_cast
      ring
    · change residual F X v c S = flexibleFirstResidual S.card T.card
        (feasibleBool F X v c S) (feasibleBool F X v c T) (picksFirst F X v u c)
      unfold residual flexibleFirstResidual
      rw [if_neg hSne, hpB]
      simp [pieceRate, feasibleBool]
    · change residual F X v c T = flexibleSecondResidual S.card T.card
        (feasibleBool F X v c S) (feasibleBool F X v c T) (picksFirst F X v u c)
      unfold residual flexibleSecondResidual
      rw [if_pos hpT.symm, hpB, hrate]
      simp [pieceRate, feasibleBool]

omit [Fintype C] in
lemma componentOf_injective_two (F : HardListInstance V C) (X : V → C)
    (v u w : V) (c : C) (hN : rootNeighbours F X v c = {u, w})
    (hST : offRootComponent F X v (X v) c u ≠ offRootComponent F X v (X v) c w) :
    Function.Injective (componentOf F X v c) := by
  intro i j hij
  apply Subtype.ext
  have hi : i.val = u ∨ i.val = w := by simpa [hN] using i.property
  have hj : j.val = u ∨ j.val = w := by simpa [hN] using j.property
  have hc := congrArg Subtype.val hij
  change offRootComponent F X v (X v) c i.val = offRootComponent F X v (X v) c j.val at hc
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact hi.trans hj.symm
  · exact (hST (by simpa [hi, hj] using hc)).elim
  · exact (hST (by simpa [hi, hj] using hc.symm)).elim
  · exact hi.trans hj.symm

omit [Fintype V] [Fintype C] in
lemma incidence_count_eq_one_of_injective {I A : Type*} [Fintype I] [DecidableEq A]
    (f : I → A) (hf : Function.Injective f) (i : I) :
    IncidenceMatching.count f (f i) = 1 := by
  simp only [IncidenceMatching.count, hf.eq_iff]
  apply card_eq_one.mpr
  refine ⟨i, ?_⟩
  ext j
  simp

theorem offRootCharge_two_distinct {FX FY : HardListInstance V C} {X Y : V → C}
    {v u w : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (huw : u ≠ w)
    (hN : rootNeighbours FX X v c = {u, w})
    (hAX : offRootComponent FX X v (X v) c u ≠ offRootComponent FX X v (X v) c w)
    (hBY : offRootComponent FY Y v (Y v) c u ≠ offRootComponent FY Y v (Y v) c w) :
    let A₁ := offRootComponent FX X v (X v) c u
    let A₂ := offRootComponent FX X v (X v) c w
    let B₁ := offRootComponent FY Y v (Y v) c u
    let B₂ := offRootComponent FY Y v (Y v) c w
    offRootCharge h hca hcb =
      pairCharge A₁.card B₁.card (residual FX X v c A₁) (residual FY Y v c B₁) +
      pairCharge A₂.card B₂.card (residual FX X v c A₂) (residual FY Y v c B₂) := by
  dsimp only
  have hNY : rootNeighbours FY Y v c = {u, w} := by rwa [← h.rootNeighbours_eq hca hcb]
  have hcountA := incidence_count_eq_one_of_injective (componentOf FX X v c)
    (componentOf_injective_two FX X v u w c hN hAX)
  have hcountB := incidence_count_eq_one_of_injective (oppositeComponentOf h hca hcb)
    ((componentOf_injective_two FY Y v u w c hNY hBY).comp
      (rootIncidenceEquiv h hca hcb).injective)
  unfold offRootCharge
  rw [IncidenceMatching.charge_as_incidence_sum _ _
    (componentOf_surjective FX X v c) (oppositeComponentOf_surjective h hca hcb)]
  simp only [IncidenceMatching.atIncidence, IncidenceMatching.share,
    hcountA, hcountB, Nat.cast_one, div_one]
  let H (z : V) := pairCharge
    (offRootComponent FX X v (X v) c z).card (offRootComponent FY Y v (Y v) c z).card
    (residual FX X v c (offRootComponent FX X v (X v) c z))
    (residual FY Y v c (offRootComponent FY Y v (Y v) c z))
  change (∑ i : RootIncidence FX X v c, H i.val) = H u + H w
  rw [← Finset.sum_subtype (F := inferInstance) (rootNeighbours FX X v c)
    (fun _ => Iff.rfl) H, hN, sum_pair huw]

theorem perColourCharge_le_two_distinct {FX FY : HardListInstance V C} {X Y : V → C}
    {v u w : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (hav : c ∈ FX.list v) (huw : u ≠ w)
    (hN : rootNeighbours FX X v c = {u, w})
    (hAX : offRootComponent FX X v (X v) c u ≠ offRootComponent FX X v (X v) c w)
    (hBY : offRootComponent FY Y v (Y v) c u ≠ offRootComponent FY Y v (Y v) c w) :
    perColourCharge h hca hcb ≤ 8 / 3 := by
  have hNY : rootNeighbours FY Y v c = {u, w} := by rwa [← h.rootNeighbours_eq hca hcb]
  have hX := two_piece_formulas FX X v u w c (by rwa [h.X_root]) hav hN hAX
  have hY := two_piece_formulas FY Y v u w c (by rwa [h.Y_root])
    ((h.root_list_regular_iff c hca hcb).mp hav) hNY hBY
  dsimp only at hX hY
  have hpos (F : HardListInstance V C) (Z : V → C) (z : V) :
      1 ≤ (offRootComponent F Z v (Z v) c z).card :=
    card_pos.mpr ⟨z, self_mem_offRootComponent F Z v z (Z v) c⟩
  have hbound := flexibleFormula_le
    (offRootComponent FX X v (X v) c u).card (offRootComponent FX X v (X v) c w).card
    (offRootComponent FY Y v (Y v) c u).card (offRootComponent FY Y v (Y v) c w).card
    (hpos FX X u) (hpos FX X w) (hpos FY Y u) (hpos FY Y w)
    (feasibleBool FX X v c (offRootComponent FX X v (X v) c u))
    (feasibleBool FX X v c (offRootComponent FX X v (X v) c w))
    (feasibleBool FY Y v c (offRootComponent FY Y v (Y v) c u))
    (feasibleBool FY Y v c (offRootComponent FY Y v (Y v) c w))
    (picksFirst FX X v u c) (picksFirst FY Y v u c) hX.1 hY.1
  unfold flexibleFormula at hbound
  have hNne : (rootNeighbours FX X v c).Nonempty := by rw [hN]; exact insert_nonempty _ _
  rw [perColourCharge, if_pos hNne, offRootCharge_two_distinct h hca hcb huw hN hAX hBY,
    hX.2.1, hY.2.1, hX.2.2.1, hX.2.2.2, hY.2.2.1, hY.2.2.2]
  linarith

theorem perColourCharge_le_of_two {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (hav : c ∈ FX.list v) (hm : (rootNeighbours FX X v c).card = 2) :
    perColourCharge h hca hcb ≤ 8 / 3 := by
  obtain ⟨u, w, huw, hN⟩ := card_eq_two.mp hm
  by_cases hAX : offRootComponent FX X v (X v) c u = offRootComponent FX X v (X v) c w
  · exact perColourCharge_le_two_shared_left h hca hcb huw hN hAX
  · by_cases hBY : offRootComponent FY Y v (Y v) c u = offRootComponent FY Y v (Y v) c w
    · exact perColourCharge_le_two_shared_right h hca hcb huw hN hBY
    · exact perColourCharge_le_two_distinct h hca hcb hav huw hN hAX hBY

/-- The complete regular-colour charge bound for actual root-local graph
components, including empty, blocked, exceptional, and high-multiplicity
cases. Its hypotheses do not include a local numerical charge inequality. -/
theorem perColourCharge_le {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) :
    perColourCharge h hca hcb ≤ (11 / 6 : ℝ) * (rootNeighbours FX X v c).card -
      if c ∈ FX.list v then 1 else 0 := by
  by_cases hav : c ∈ FX.list v
  · rw [if_pos hav]
    by_cases hzero : (rootNeighbours FX X v c).card = 0
    · have hn : ¬ (rootNeighbours FX X v c).Nonempty := by
        simpa only [card_eq_zero, not_nonempty_iff_eq_empty] using hzero
      simp [perColourCharge, hn, hav, hzero]
    · by_cases hone : (rootNeighbours FX X v c).card = 1
      · have hb := perColourCharge_le_of_one h hca hcb hav hone
        norm_num [hone]
        exact hb
      · by_cases htwo : (rootNeighbours FX X v c).card = 2
        · have hb := perColourCharge_le_of_two h hca hcb hav htwo
          norm_num [htwo]
          exact hb
        · simpa only [if_pos hav] using perColourCharge_le_of_three_le h hca hcb (by omega)
  · simpa only [if_neg hav, sub_zero] using perColourCharge_le_of_unavailable h hca hcb hav

end
end ZeroFreeness.RegularColourCharge
