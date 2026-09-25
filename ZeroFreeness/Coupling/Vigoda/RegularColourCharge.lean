import ZeroFreeness.Coupling.Vigoda.RootComponentGeometry

/-! Actual regular-colour charges from root-local graph components. -/
namespace ZeroFreeness.RegularColourCharge

open Finset PottsCI PottsCI.Vigoda RootComponentGeometry VigodaArithmetic
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V C : Type*} [Fintype V] [Fintype C]

def selectedRepresentative (F : HardListInstance V C) (X : V → C) (v : V) (c : C) : V :=
  if h : (rootNeighbours F X v c).Nonempty then
    Classical.choose ((rootNeighbours F X v c).exists_max_image
      (fun u => (offRootComponent F X v (X v) c u).card) h)
  else v

def largestPiece (F : HardListInstance V C) (X : V → C) (v : V) (c : C) : Finset V :=
  offRootComponent F X v (X v) c (selectedRepresentative F X v c)

omit [Fintype C] in
lemma selectedRepresentative_mem (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hN : (rootNeighbours F X v c).Nonempty) :
    selectedRepresentative F X v c ∈ rootNeighbours F X v c := by
  simp only [selectedRepresentative, dif_pos hN]
  exact (Classical.choose_spec ((rootNeighbours F X v c).exists_max_image
    (fun u => (offRootComponent F X v (X v) c u).card) hN)).1

omit [Fintype C] in
lemma largestPiece_mem (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hN : (rootNeighbours F X v c).Nonempty) : largestPiece F X v c ∈ rootFamily F X v c :=
  mem_image.mpr ⟨_, selectedRepresentative_mem F X v c hN, rfl⟩

omit [Fintype C] in
lemma largestPiece_max (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hN : (rootNeighbours F X v c).Nonempty) (S : Finset V)
    (hS : S ∈ rootFamily F X v c) : S.card ≤ (largestPiece F X v c).card := by
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hS
  simp only [largestPiece, selectedRepresentative, dif_pos hN]
  exact (Classical.choose_spec ((rootNeighbours F X v c).exists_max_image
    (fun u => (offRootComponent F X v (X v) c u).card) hN)).2 u hu

def pieceRate (F : HardListInstance V C) (X : V → C) (v : V) (c : C) (S : Finset V) : ℝ :=
  if flipAllowed F S (flipConfiguration X S (X v) c) then vigodaMass S.card else 0

def rootRate (F : HardListInstance V C) (X : V → C) (v : V) (c : C) : ℝ :=
  if flipAllowed F (flipSet F.graph X v c)
    (flipConfiguration X (flipSet F.graph X v c) (X v) c)
  then vigodaMass (flipSet F.graph X v c).card else 0

def residual (F : HardListInstance V C) (X : V → C) (v : V) (c : C) (S : Finset V) : ℝ :=
  pieceRate F X v c S - if S = largestPiece F X v c then rootRate F X v c else 0

def rootCharge (F : HardListInstance V C) (X : V → C) (v : V) (c : C) : ℝ :=
  ((flipSet F.graph X v c).card - (largestPiece F X v c).card - 1 : ℝ) * rootRate F X v c

omit [Fintype V] [Fintype C] in
lemma pieceRate_nonneg (F : HardListInstance V C) (X : V → C) (v : V) (c : C) (S : Finset V) :
    0 ≤ pieceRate F X v c S := by
  unfold pieceRate
  split_ifs
  · exact vigodaMass_nonneg _
  · exact le_rfl

omit [Fintype V] [Fintype C] in
lemma pieceRate_le_profile (F : HardListInstance V C) (X : V → C) (v : V) (c : C) (S : Finset V) :
    pieceRate F X v c S ≤ vigodaMass S.card := by
  unfold pieceRate
  split_ifs
  · exact le_rfl
  · exact vigodaMass_nonneg _

omit [Fintype C] in
lemma rootRate_nonneg (F : HardListInstance V C) (X : V → C) (v : V) (c : C) :
    0 ≤ rootRate F X v c := by
  unfold rootRate
  split_ifs
  · exact vigodaMass_nonneg _
  · exact le_rfl

lemma rootRate_le_pieceRate (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hc : c ≠ X v) (S : Finset V) (hS : S ∈ rootFamily F X v c) :
    rootRate F X v c ≤ pieceRate F X v c S := by
  unfold rootRate
  split_ifs with hroot
  · have hp := ((root_flipAllowed_iff F X v c hc).mp hroot).2 S hS
    rw [pieceRate, if_pos hp]
    exact profile_antitone _ _ (card_pos.mpr (rootFamily_nonempty_component hS))
      (card_le_card (root_piece_subset_root hc hS))
  · exact pieceRate_nonneg F X v c S

lemma residual_nonneg (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hc : c ≠ X v) (S : RootPiece F X v c) : 0 ≤ residual F X v c S := by
  unfold residual
  split_ifs
  · exact sub_nonneg.mpr (rootRate_le_pieceRate F X v c hc S S.property)
  · simpa using pieceRate_nonneg F X v c S

omit [Fintype C] in
lemma residual_le_profile (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (S : Finset V) : residual F X v c S ≤ vigodaMass S.card := by
  have hr := rootRate_nonneg F X v c
  have hp := pieceRate_le_profile F X v c S
  unfold residual
  split_ifs <;> linarith

lemma rootRate_zero_of_unavailable (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hc : c ∉ F.list v) : rootRate F X v c = 0 := by
  unfold rootRate
  rw [if_neg]
  intro hallowed
  apply hc
  simpa using hallowed v self_mem_flipSet

omit [Fintype C] in
lemma rootCharge_le_four_twenty_firsts (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hN : (rootNeighbours F X v c).Nonempty) : rootCharge F X v c ≤ 4 / 21 := by
  have hSpos : 1 ≤ (largestPiece F X v c).card :=
    card_pos.mpr (rootFamily_nonempty_component (largestPiece_mem F X v c hN))
  have hSposR : (1 : ℝ) ≤ (largestPiece F X v c).card := by exact_mod_cast hSpos
  unfold rootCharge rootRate
  split_ifs
  · have hp := vigodaMass_nonneg (flipSet F.graph X v c).card
    have hb := vigoda_central_bound (flipSet F.graph X v c).card
    nlinarith
  · norm_num

def offRootCharge {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) : ℝ :=
  (∑ S : RootPiece FX X v c, (S.val.card : ℝ) * residual FX X v c S) +
  (∑ S : RootPiece FY Y v c, (S.val.card : ℝ) * residual FY Y v c S) -
  ∑ i, IncidenceMatching.atIncidence (componentOf FX X v c) (oppositeComponentOf h hca hcb)
    (fun S => residual FX X v c S) (fun S => residual FY Y v c S) i

def perColourCharge {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) : ℝ :=
  if (rootNeighbours FX X v c).Nonempty then
    rootCharge FX X v c + rootCharge FY Y v c + offRootCharge h hca hcb
  else -(if c ∈ FX.list v then 1 else 0)

lemma offRootCharge_le_four_thirds {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) :
    offRootCharge h hca hcb ≤ (4 / 3 : ℝ) * (rootNeighbours FX X v c).card := by
  exact actual_incidence_charge_le_four_thirds h hca hcb _ _
    (residual_nonneg FX X v c (by rwa [h.X_root]))
    (residual_nonneg FY Y v c (by rwa [h.Y_root]))
    (fun S => residual_le_profile FX X v c S)
    (fun S => residual_le_profile FY Y v c S)

theorem perColourCharge_le_of_three_le {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (hm : 3 ≤ (rootNeighbours FX X v c).card) :
    perColourCharge h hca hcb ≤ (11 / 6 : ℝ) * (rootNeighbours FX X v c).card -
      if c ∈ FX.list v then 1 else 0 := by
  have hNX : (rootNeighbours FX X v c).Nonempty := card_pos.mp (by omega)
  have hNY : (rootNeighbours FY Y v c).Nonempty := by rwa [← h.rootNeighbours_eq hca hcb]
  rw [perColourCharge, if_pos hNX]
  have hRX := rootCharge_le_four_twenty_firsts FX X v c hNX
  have hRY := rootCharge_le_four_twenty_firsts FY Y v c hNY
  have hO := offRootCharge_le_four_thirds h hca hcb
  have hnum := regular_high_multiplicity_arithmetic _ hm
  split_ifs <;> linarith

theorem perColourCharge_le_of_unavailable {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (hc : c ∉ FX.list v) :
    perColourCharge h hca hcb ≤ (11 / 6 : ℝ) * (rootNeighbours FX X v c).card := by
  have hcY : c ∉ FY.list v := fun hcY => hc ((h.root_list_regular_iff c hca hcb).mpr hcY)
  unfold perColourCharge
  split_ifs with hN
  · have hO := offRootCharge_le_four_thirds h hca hcb
    simp only [rootCharge, rootRate_zero_of_unavailable FX X v c hc,
      rootRate_zero_of_unavailable FY Y v c hcY, mul_zero, zero_add]
    have hm : (0 : ℝ) ≤ (rootNeighbours FX X v c).card := Nat.cast_nonneg _
    linarith
  · norm_num [hc]

omit [Fintype C] in
lemma largestPiece_single_neighbour (F : HardListInstance V C) (X : V → C)
    (v u : V) (c : C) (hN : rootNeighbours F X v c = {u}) :
    largestPiece F X v c = offRootComponent F X v (X v) c u := by
  have hm := selectedRepresentative_mem F X v c (by rw [hN]; exact singleton_nonempty _)
  have hu : selectedRepresentative F X v c = u := by simpa [hN] using hm
  simp only [largestPiece, hu]

lemma rootCharge_zero_single_neighbour (F : HardListInstance V C) (X : V → C)
    (v u : V) (c : C) (hc : c ≠ X v) (hN : rootNeighbours F X v c = {u}) :
    rootCharge F X v c = 0 := by
  unfold rootCharge
  rw [root_flipSet_card_single_neighbour F X v u c hc hN,
    largestPiece_single_neighbour F X v u c hN]
  push_cast
  ring

lemma residual_le_diff_single_neighbour (F : HardListInstance V C) (X : V → C)
    (v u : V) (c : C) (hc : c ≠ X v) (hav : c ∈ F.list v)
    (hN : rootNeighbours F X v c = {u}) (S : RootPiece F X v c) :
    residual F X v c S ≤ profileDiff S.val.card := by
  have hS : S.val = offRootComponent F X v (X v) c u := by
    have hm := S.property
    simpa [rootFamily, hN] using hm
  have hroot : flipAllowed F (flipSet F.graph X v c)
      (flipConfiguration X (flipSet F.graph X v c) (X v) c) ↔
      flipAllowed F S.val (flipConfiguration X S.val (X v) c) := by
    rw [root_flipAllowed_iff F X v c hc]
    simp [rootFamily, hN, hav, hS]
  have hsize : (flipSet F.graph X v c).card = S.val.card + 1 := by
    rw [root_flipSet_card_single_neighbour F X v u c hc hN, hS]
    omega
  have hlargest : S.val = largestPiece F X v c := by
    rw [largestPiece_single_neighbour F X v u c hN]
    exact hS
  unfold residual pieceRate rootRate
  rw [if_pos hlargest, hroot, hsize]
  split_ifs
  · exact le_rfl
  · simpa using profileDiff_nonneg S.val.card
      (card_pos.mpr (rootFamily_nonempty_component S.property))

omit [Fintype V] [Fintype C] in
lemma incidence_count_eq_one {I A : Type*} [Fintype I] [DecidableEq A] (hcard : Fintype.card I = 1)
    (f : I → A) (i : I) : IncidenceMatching.count f (f i) = 1 := by
  have hpos := IncidenceMatching.count_pos f i
  have hle : IncidenceMatching.count f (f i) ≤ Fintype.card I :=
    card_le_card (filter_subset _ _)
  omega

theorem perColourCharge_le_of_one {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (hav : c ∈ FX.list v) (hm : (rootNeighbours FX X v c).card = 1) :
    perColourCharge h hca hcb ≤ 5 / 6 := by
  obtain ⟨u, hNX⟩ := card_eq_one.mp hm
  have hNY : rootNeighbours FY Y v c = {u} := by rwa [← h.rootNeighbours_eq hca hcb]
  have hcX : c ≠ X v := by rwa [h.X_root]
  have hcY : c ≠ Y v := by rwa [h.Y_root]
  have havY := (h.root_list_regular_iff c hca hcb).mp hav
  have hn : (rootNeighbours FX X v c).Nonempty := by rw [hNX]; exact singleton_nonempty _
  rw [perColourCharge, if_pos hn, rootCharge_zero_single_neighbour FX X v u c hcX hNX,
    rootCharge_zero_single_neighbour FY Y v u c hcY hNY, zero_add, zero_add]
  unfold offRootCharge
  rw [IncidenceMatching.charge_as_incidence_sum _ _
    (componentOf_surjective FX X v c) (oppositeComponentOf_surjective h hca hcb)]
  have hcardI : Fintype.card (RootIncidence FX X v c) = 1 := by simpa using hm
  have hcountA := incidence_count_eq_one hcardI (componentOf FX X v c)
  have hcountB := incidence_count_eq_one hcardI (oppositeComponentOf h hca hcb)
  calc
    _ ≤ ∑ _ : RootIncidence FX X v c, (5 / 6 : ℝ) := by
      apply sum_le_sum
      intro i _
      simp only [IncidenceMatching.atIncidence, IncidenceMatching.share,
        hcountA i, hcountB i, Nat.cast_one, div_one]
      exact one_neighbour_box _ _
        (card_pos.mpr (rootFamily_nonempty_component (componentOf FX X v c i).property))
        (card_pos.mpr (rootFamily_nonempty_component (oppositeComponentOf h hca hcb i).property))
        _ _ (residual_nonneg FX X v c hcX _)
        (residual_le_diff_single_neighbour FX X v u c hcX hav hNX _)
        (residual_nonneg FY Y v c hcY _)
        (residual_le_diff_single_neighbour FY Y v u c hcY havY hNY _)
    _ = 5 / 6 := by simp [hm]

omit [Fintype C] in
lemma largestPiece_of_family_singleton (F : HardListInstance V C) (X : V → C)
    (v : V) (c : C) (hN : (rootNeighbours F X v c).Nonempty)
    (S : Finset V) (hF : rootFamily F X v c = {S}) : largestPiece F X v c = S := by
  simpa [hF] using largestPiece_mem F X v c hN

lemma rootCharge_zero_of_family_singleton (F : HardListInstance V C) (X : V → C)
    (v : V) (c : C) (hc : c ≠ X v) (hN : (rootNeighbours F X v c).Nonempty)
    (S : Finset V) (hF : rootFamily F X v c = {S}) : rootCharge F X v c = 0 := by
  unfold rootCharge
  rw [root_flipSet_card F X v c hc, hF, sum_singleton,
    largestPiece_of_family_singleton F X v c hN S hF]
  push_cast
  ring

lemma rootCharge_le_sixth_two_neighbours (F : HardListInstance V C) (X : V → C)
    (v u w : V) (c : C) (hc : c ≠ X v) (hN : rootNeighbours F X v c = {u, w}) :
    rootCharge F X v c ≤ 1 / 6 := by
  have hn : (rootNeighbours F X v c).Nonempty := by rw [hN]; exact insert_nonempty _ _
  let S := offRootComponent F X v (X v) c u
  let T := offRootComponent F X v (X v) c w
  have hF : rootFamily F X v c = {S, T} := by simp [rootFamily, hN, S, T]
  by_cases hST : S = T
  · have hF' : rootFamily F X v c = {S} := by simpa [hST] using hF
    rw [rootCharge_zero_of_family_singleton F X v c hc hn S hF']
    norm_num
  · have hS : S ∈ rootFamily F X v c := by rw [hF]; simp
    have hT : T ∈ rootFamily F X v c := by rw [hF]; simp
    have hSpos := card_pos.mpr (rootFamily_nonempty_component hS)
    have hTpos := card_pos.mpr (rootFamily_nonempty_component hT)
    have hsize : (flipSet F.graph X v c).card = 1 + S.card + T.card :=
      root_flipSet_card_two_neighbours F X v u w c hc hN hST
    have hmax := largestPiece_mem F X v c hn
    rw [hF, mem_insert, mem_singleton] at hmax
    have hmin := min_size_root_bound S.card T.card hSpos hTpos
    unfold rootCharge rootRate
    split_ifs
    · rw [hsize]
      push_cast
      rcases hmax with hmax | hmax
      · have hm := largestPiece_max F X v c hn T hT
        rw [hmax] at hm ⊢
        rw [Nat.min_eq_right hm] at hmin
        nlinarith
      · have hm := largestPiece_max F X v c hn S hS
        rw [hmax] at hm ⊢
        rw [Nat.min_eq_left hm] at hmin
        nlinarith
    · norm_num

def familyResidualCost (F : HardListInstance V C) (X : V → C) (v : V) (c : C) : ℝ :=
  ∑ S : RootPiece F X v c, (S.val.card : ℝ) * residual F X v c S

omit [Fintype C] in
lemma familyResidualCost_le_two (F : HardListInstance V C) (X : V → C)
    (v u w : V) (c : C) (hN : rootNeighbours F X v c = {u, w}) :
    familyResidualCost F X v c ≤ 2 := by
  have hcard : Fintype.card (RootPiece F X v c) ≤ 2 := by
    simp only [Fintype.card_coe, rootFamily]
    have hncard : (rootNeighbours F X v c).card ≤ 2 := by
      rw [hN]
      exact (card_insert_le _ _).trans (by simp)
    exact card_image_le.trans hncard
  calc
    _ ≤ ∑ _ : RootPiece F X v c, (1 : ℝ) := by
      apply sum_le_sum
      intro S _
      exact (mul_le_mul_of_nonneg_left (residual_le_profile F X v c S)
        (Nat.cast_nonneg _)).trans (vigoda_branch_bound S.val.card)
    _ ≤ 2 := by
      simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
      exact_mod_cast hcard

lemma familyResidualCost_le_half_of_shared (F : HardListInstance V C) (X : V → C)
    (v u w : V) (c : C) (hc : c ≠ X v) (huw : u ≠ w)
    (hN : rootNeighbours F X v c = {u, w})
    (hST : offRootComponent F X v (X v) c u = offRootComponent F X v (X v) c w) :
    rootCharge F X v c = 0 ∧ familyResidualCost F X v c ≤ 1 / 2 := by
  let S := offRootComponent F X v (X v) c u
  have hF : rootFamily F X v c = {S} := by simp [rootFamily, hN, hST, S]
  have hn : (rootNeighbours F X v c).Nonempty := by rw [hN]; exact insert_nonempty _ _
  constructor
  · exact rootCharge_zero_of_family_singleton F X v c hc hn S hF
  · have hu : u ∈ rootNeighbours F X v c := by rw [hN]; simp
    have hw : w ∈ rootNeighbours F X v c := by rw [hN]; simp
    have hwS : w ∈ S := by
      change w ∈ offRootComponent F X v (X v) c u
      rw [hST]
      exact self_mem_offRootComponent F X v w (X v) c
    have hsize : 3 ≤ S.card := shared_component_card_ge_three hc.symm
      (mem_rootNeighbours.mp hu).2 (mem_rootNeighbours.mp hw).2 huw hwS
    unfold familyResidualCost
    rw [← Finset.sum_subtype (F := inferInstance) (rootFamily F X v c) (fun _ => Iff.rfl)
      (fun T : Finset V => (T.card : ℝ) * residual F X v c T),
      hF, sum_singleton]
    exact (mul_le_mul_of_nonneg_left (residual_le_profile F X v c S)
      (Nat.cast_nonneg _)).trans (profile_large_component_bound S.card hsize)

end
end ZeroFreeness.RegularColourCharge
