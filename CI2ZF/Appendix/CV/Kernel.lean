import PottsCI.Vigoda.ComponentCoupling
import CI2ZF.Appendix.CV.Arithmetic

/-! The actual CV hard and soft flip kernels. The profile changes the accepted
transition probabilities; detailed balance is proved again using the common
component involution, and soft stationarity follows from the active-fibre theorem. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [Fintype C]

/-- Acceptance probability for a nontrivial proposal. -/
noncomputable def acceptanceProbability (F : HardListInstance V C)
    (X : V → C) (u : V) (c : C) : ℝ :=
  if flipAllowed F (flipSet F.graph X u c)
      (flipConfiguration X (flipSet F.graph X u c) (X u) c) then
    mass (flipSet F.graph X u c).card / (flipSet F.graph X u c).card
  else 0

omit [Fintype C] in
lemma acceptanceProbability_nonneg (F : HardListInstance V C)
    (X : V → C) (u : V) (c : C) : 0 ≤ acceptanceProbability F X u c := by
  unfold acceptanceProbability
  split
  · exact div_nonneg (mass_nonneg _) (Nat.cast_nonneg _)
  · exact le_rfl

lemma acceptanceProbability_le_one (F : HardListInstance V C)
    (X : V → C) (u : V) (c : C) : acceptanceProbability F X u c ≤ 1 := by
  unfold acceptanceProbability
  split
  · have hcard : (1 : ℝ) ≤ (flipSet F.graph X u c).card := by
      exact_mod_cast flipSet_card_pos (G := F.graph) (X := X) (u := u) (c := c)
    rw [div_le_one (by positivity)]
    exact (mass_le_one _).trans hcard
  · exact zero_le_one

/-- Outcome law for one proposal `(u,c)`. -/
noncomputable def proposalDistribution (F : HardListInstance V C)
    (X : V → C) (u : V) (c : C) : FinDist (V → C) :=
  if c = X u then FinDist.pure X
  else twoPoint (flipConfiguration X (flipSet F.graph X u c) (X u) c) X
    (acceptanceProbability F X u c)
    (acceptanceProbability_nonneg F X u c)
    (acceptanceProbability_le_one F X u c)

/-- One hard Carlson--Vigoda step. -/
noncomputable def hardStep [Nonempty V] [Nonempty C]
    (F : HardListInstance V C) (X : V → C) : FinDist (V → C) :=
  (FinDist.uniform (V × C)).bind fun p => proposalDistribution F X p.1 p.2

/-! ## Reversibility and stationarity of the hard transition -/

/-- A proposal with the wrong target colour at the proposal vertex cannot
move `X` to a distinct colouring `Y`. -/
lemma proposalDistribution_eq_zero {F : HardListInstance V C} {X Y : V → C}
    (hXY : X ≠ Y) (u : V) (c : C) (hc : c ≠ Y u) :
    (proposalDistribution F X u c).w Y = 0 := by
  unfold proposalDistribution
  split
  · simp [FinDist.pure, Ne.symm hXY]
  · rw [twoPoint_w]
    simp only [if_neg (show Y ≠ X from fun h => hXY h.symm), add_zero]
    rw [if_neg]
    intro hYflip
    apply hc
    have hroot := flipConfiguration_at_start
      (G := F.graph) (X := X) (u := u) (c := c)
    rw [← hYflip] at hroot
    exact hroot.symm

/-- The matched proposal from a proper colouring has the same transition
mass as its reverse proposal. -/
lemma proposalDistribution_reversible {F : HardListInstance V C} {X Y : V → C}
    (hX : F.IsProper X) (hY : F.IsProper Y) (hXY : X ≠ Y) (u : V) :
    (proposalDistribution F X u (Y u)).w Y =
      (proposalDistribution F Y u (X u)).w X := by
  by_cases hu : X u = Y u
  · unfold proposalDistribution
    rw [if_pos hu.symm, if_pos hu]
    simp [FinDist.pure, hXY, Ne.symm hXY]
  · have huY : Y u ≠ X u := fun h => hu h.symm
    unfold proposalDistribution
    rw [if_neg huY, if_neg hu, twoPoint_w, twoPoint_w]
    simp only [if_neg (show Y ≠ X from fun h => hXY h.symm),
      if_neg (show X ≠ Y from hXY), add_zero]
    by_cases hflip :
        Y = flipConfiguration X (flipSet F.graph X u (Y u)) (X u) (Y u)
    · obtain ⟨hset, hconf⟩ := flip_involutive hX (u := u) (c := Y u) huY
      rw [← hflip] at hset hconf
      unfold acceptanceProbability
      rw [hset, hconf, ← hflip]
      have hAllowedY : flipAllowed F (flipSet F.graph X u (Y u)) Y :=
        fun w _ => hY.2 w
      have hAllowedX : flipAllowed F (flipSet F.graph X u (Y u)) X :=
        fun w _ => hX.2 w
      simp [hAllowedY, hAllowedX]
    · have hflip' :
          X ≠ flipConfiguration Y (flipSet F.graph Y u (X u)) (Y u) (X u) := by
        intro hflip'
        apply hflip
        obtain ⟨hset, hconf⟩ := flip_involutive hY (u := u) (c := X u) hu
        rw [← hflip'] at hset hconf
        rw [hset]
        exact hconf.symm
      simp [hflip, hflip']

lemma hardStep_w [Nonempty V] [Nonempty C]
    (F : HardListInstance V C) (X Y : V → C) :
    (hardStep F X).w Y = ∑ p : V × C,
      ((Fintype.card (V × C) : ℝ))⁻¹ *
        (proposalDistribution F X p.1 p.2).w Y := rfl

/-- Starting from a proper colouring, the hard transition stays in the
proper fibre. -/
lemma hardStep_support [Nonempty V] [Nonempty C]
    {F : HardListInstance V C} {X Y : V → C}
    (hX : F.IsProper X) (hY : ¬F.IsProper Y) : (hardStep F X).w Y = 0 := by
  rw [hardStep_w]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [mul_eq_zero]
  right
  obtain ⟨u, c⟩ := p
  have hXY : X ≠ Y := fun h => hY (h ▸ hX)
  unfold proposalDistribution
  split
  · simp [FinDist.pure, Ne.symm hXY]
  · rename_i hcx
    rw [twoPoint_w]
    simp only [if_neg (show Y ≠ X from fun h => hXY h.symm), add_zero]
    by_cases hYflip :
        Y = flipConfiguration X (flipSet F.graph X u c) (X u) c
    · rw [if_pos hYflip]
      unfold acceptanceProbability
      rw [if_neg]
      intro hAllowed
      exact hY (hYflip ▸ flip_preserves_proper hX hcx hAllowed)
    · rw [if_neg hYflip]

/-- Detailed balance of the hard Carlson--Vigoda transition on proper list-colourings.
-/
theorem hardStep_reversible [Nonempty V] [Nonempty C]
    {F : HardListInstance V C} {X Y : V → C}
    (hX : F.IsProper X) (hY : F.IsProper Y) :
    (hardStep F X).w Y = (hardStep F Y).w X := by
  rcases eq_or_ne X Y with rfl | hXY
  · rfl
  · rw [hardStep_w, hardStep_w, Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hleft :
        ∑ c : C, ((Fintype.card (V × C) : ℝ))⁻¹ *
            (proposalDistribution F X u c).w Y =
          ((Fintype.card (V × C) : ℝ))⁻¹ *
            (proposalDistribution F X u (Y u)).w Y := by
      refine Finset.sum_eq_single (Y u) (fun c _ hc => ?_)
        (fun h => absurd (Finset.mem_univ _) h)
      rw [proposalDistribution_eq_zero hXY u c hc, mul_zero]
    have hright :
        ∑ c : C, ((Fintype.card (V × C) : ℝ))⁻¹ *
            (proposalDistribution F Y u c).w X =
          ((Fintype.card (V × C) : ℝ))⁻¹ *
            (proposalDistribution F Y u (X u)).w X := by
      refine Finset.sum_eq_single (X u) (fun c _ hc => ?_)
        (fun h => absurd (Finset.mem_univ _) h)
      rw [proposalDistribution_eq_zero hXY.symm u c hc, mul_zero]
    rw [hleft, hright, proposalDistribution_reversible hX hY hXY u]

/-- The hard Carlson--Vigoda transition preserves the uniform hard-fibre law. -/
theorem hardStep_stationary [Nonempty V] [Nonempty C]
    (F : HardListInstance V C) (hne : ∃ X : V → C, F.IsProper X) :
    FinDist.IsStationary (hardStep F) (uniformProperFibre F hne) := by
  apply FinDist.ext
  funext Y
  simp only [FinDist.bind_w]
  by_cases hY : F.IsProper Y
  · have hterm : ∀ X : V → C,
        (uniformProperFibre F hne).w X * (hardStep F X).w Y =
          (uniformProperFibre F hne).w X * (hardStep F Y).w X := by
      intro X
      by_cases hX : F.IsProper X
      · rw [hardStep_reversible hX hY]
      · rw [uniformProperFibre_w, if_neg hX, zero_mul, zero_mul]
    rw [Finset.sum_congr rfl fun X _ => hterm X]
    have hsum :
        ∑ X : V → C, (uniformProperFibre F hne).w X * (hardStep F Y).w X =
          (((Finset.univ.filter fun Z : V → C => F.IsProper Z).card : ℝ))⁻¹ := by
      simp only [uniformProperFibre_w, ite_mul, zero_mul]
      rw [← Finset.sum_filter]
      rw [← Finset.mul_sum]
      have hfull :
          ∑ X ∈ Finset.univ.filter (fun Z : V → C => F.IsProper Z),
              (hardStep F Y).w X = ∑ X : V → C, (hardStep F Y).w X := by
        refine Finset.sum_subset (Finset.filter_subset _ _) ?_
        intro X _ hX
        apply hardStep_support hY
        intro hp
        exact hX (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
      rw [hfull, FinDist.sum_one, mul_one]
    rw [hsum, uniformProperFibre_w, if_pos hY]
  · have hterm : ∀ X : V → C,
        (uniformProperFibre F hne).w X * (hardStep F X).w Y = 0 := by
      intro X
      by_cases hX : F.IsProper X
      · rw [hardStep_support hX hY, mul_zero]
      · rw [uniformProperFibre_w, if_neg hX, zero_mul]
    rw [Finset.sum_eq_zero fun X _ => hterm X,
      uniformProperFibre_w, if_neg hY]

/-- Package the concrete hard Carlson--Vigoda transition as the abstract hard-fibre
kernel consumed by `PinningData.softKernel`.  The sole bridge assumption says
that the supplied list instance represents exactly the inequalities selected
by the active set; there is no dynamical hypothesis left to prove. -/
noncomputable def hardFibreKernelOfListInstance [Nonempty V] [Nonempty C]
    (I : PinningData V C) (A : Finset (PinningData.Constraint I))
    (F : HardListInstance V C)
    (hrep : ∀ X : V → C, F.IsProper X ↔ I.ActiveCompatible X A) :
    PinningData.HardFibreKernel I A where
  kernel := hardStep F
  supported := by
    intro X Y hX hY
    apply hardStep_support ((hrep X).mpr hX)
    exact fun h => hY ((hrep Y).mp h)
  stationary := by
    intro hne
    have hproper : ∃ X : V → C, F.IsProper X := by
      obtain ⟨X, hX⟩ := hne
      exact ⟨X, (hrep X).mpr (Finset.mem_filter.mp hX).2⟩
    have hstat := hardStep_stationary F hproper
    have hfibres :
        I.uniformHardFibre A hne = uniformProperFibre F hproper := by
      apply FinDist.ext
      funext X
      rw [I.uniformHardFibre_w, uniformProperFibre_w]
      have hcard : (I.compatibleColorings A).card =
          (Finset.univ.filter fun Y : V → C => F.IsProper Y).card := by
        congr 1
        ext Y
        simp [PinningData.compatibleColorings, hrep Y]
      rw [hcard]
      exact if_congr (hrep X).symm rfl rfl
    rw [hfibres]
    exact hstat

/-- Concrete CV transition on an active constraint fibre. -/
noncomputable def activeCVHardFibreKernel [Nonempty V] [Nonempty C]
    (I : PinningData V C) (A : Finset (PinningData.Constraint I)) :
    PinningData.HardFibreKernel I A :=
  hardFibreKernelOfListInstance I A (activeHardListInstance I A)
    (activeHardListInstance_isProper_iff I A)

/-- The soft CV kernel of Appendix cv-1809 at interior activities. -/
noncomputable def softCVKernel [Nonempty V] [Nonempty C]
    (I : PinningData V C) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    (V → C) → FinDist (V → C) :=
  I.softKernel x hx0 hx1 fun A => activeCVHardFibreKernel I A

/-- Stationarity for the actual CV update, with no stationarity hypothesis. -/
theorem softCVKernel_stationary [Nonempty V] [Nonempty C]
    (I : PinningData V C) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    FinDist.IsStationary (softCVKernel I x hx0 hx1)
      (I.gibbs x hx0.le (I.partition_pos_of_parameter_pos hx0)) :=
  I.softKernel_stationary x hx0 hx1 fun A => activeCVHardFibreKernel I A

end CI2ZF.Appendix.CV
