import CI2ZF.Coupling.Vigoda.PottsCITheorem
import CI2ZF.Coupling.Vigoda.SoftFlipBoundary
import CI2ZF.Coupling.Vigoda.HardFlipTotal
import CI2ZF.Coupling.CV.Kernel

/-!
# Soft flip kernels for an arbitrary flip profile and `x ∈ (0,1]`

This file formalizes main-text `def:flip`, `def:soft-kernel`,
`lem:soft-stationary`, `lem:boundary-sensitivity` and `lem:soft-contraction`
(Definitions 4.5-4.6, Lemmas 4.7, 4.9, 4.11), and companion Lemmas 3.4 and 3.6.

* `def:flip`: `profileStep` / `flipKernel` is the hard list-flip transition
  `Φ_F^ρ` for an arbitrary profile `ρ` (identity kernel on an empty vertex set).
* `def:soft-kernel`: `softFlipKernel P I x` is `K_{x,ρ}^{G,τ}` for every
  `x ∈ (0,1]` (the library kernels require `x < 1`).
* `lem:soft-stationary`: stationarity, reversibility (detailed balance) and,
  when `ρ₁ > 0`, irreducibility on the full colouring space.
* `lem:boundary-sensitivity`: the one-edge bound `(1-x) R_ρ /(m q)`, the hard
  one-deletion bound `R_ρ/(m q)`, and the `k`-fold versions for arbitrary
  labelled free–pinned edges (repeated vertices, mixed colours) and arbitrary
  list deletions.
* `lem:soft-contraction`: for the Vigoda profile, an adjacent coupling with
  `n q (E Ham - 1) ≤ (11/6) t Δ - q`, the Wasserstein form, and the
  all-pairs contraction by `1 - κ_x / n`, all for `x ∈ (0,1]`.

Bridges identify the Vigoda and CV instances with the library kernels
`PottsCI.Vigoda.hardStep`, `softVigodaKernel`, `softVigodaKernelWithEmpty`,
`CI2ZF.Appendix.CV.hardStep` and `softCVKernel` on their common domain.
-/

namespace CI2ZF.Potts

open PottsCI PottsCI.FinDist PottsCI.Vigoda CI2ZF CI2ZF.Potts
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false

/-! ## Flip profiles -/

/-- A flip profile `ρ = (ρ_s)_{s ≥ 1}` with `0 ≤ ρ_s ≤ 1` for every `s ≥ 1`.
The value at `s = 0` is unconstrained and never used (components are
nonempty). -/
structure FlipProfile where
  ρ : ℕ → ℝ
  nonneg : ∀ s, 1 ≤ s → 0 ≤ ρ s
  le_one : ∀ s, 1 ≤ s → ρ s ≤ 1

namespace FlipProfile

/-- `R_ρ = sup_{s ≥ 1} s ρ_s`, as a real supremum. -/
def R (P : FlipProfile) : ℝ := ⨆ s : ℕ, ((s + 1 : ℕ) : ℝ) * P.ρ (s + 1)

/-- `R_ρ < ∞`. -/
def RFinite (P : FlipProfile) : Prop :=
  BddAbove (Set.range fun s : ℕ => ((s + 1 : ℕ) : ℝ) * P.ρ (s + 1))

lemma le_R (P : FlipProfile) (hP : P.RFinite) {s : ℕ} (hs : 1 ≤ s) :
    (s : ℝ) * P.ρ s ≤ P.R := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  exact le_ciSup (f := fun s : ℕ => ((s + 1 : ℕ) : ℝ) * P.ρ (s + 1)) hP k

lemma R_nonneg (P : FlipProfile) (hP : P.RFinite) : 0 ≤ P.R := by
  have h := P.le_R hP (s := 1) le_rfl
  have h1 := P.nonneg 1 le_rfl
  simp only [Nat.cast_one, one_mul] at h
  linarith

/-- Any bound on `s ρ_s` for `s ≥ 1` bounds `R_ρ`. -/
lemma R_le (P : FlipProfile) {B : ℝ} (hB : ∀ s : ℕ, 1 ≤ s → (s : ℝ) * P.ρ s ≤ B) :
    P.R ≤ B :=
  ciSup_le fun k => hB (k + 1) (by omega)

lemma RFinite_of_bound (P : FlipProfile) {B : ℝ}
    (hB : ∀ s : ℕ, 1 ≤ s → (s : ℝ) * P.ρ s ≤ B) : P.RFinite :=
  ⟨B, by rintro _ ⟨k, rfl⟩; exact hB (k + 1) (by omega)⟩

/-- The profile value used for the bound `s ρ_s ≤ R_ρ` at every `s ≥ 1`. -/
lemma mul_le_R (P : FlipProfile) (hP : P.RFinite) :
    ∀ s : ℕ, 1 ≤ s → (s : ℝ) * P.ρ s ≤ P.R := fun _ hs => P.le_R hP hs

end FlipProfile

/-- Vigoda's profile `p` of `eq:flip-params`. -/
def vigodaProfile : FlipProfile where
  ρ := vigodaMass
  nonneg s _ := vigodaMass_nonneg s
  le_one s _ := vigodaMass_le_one s

/-- The Carlson–Vigoda profile `P` of `eq:cv-params`. -/
def cvProfile : FlipProfile where
  ρ := CI2ZF.Appendix.CV.mass
  nonneg s _ := CI2ZF.Appendix.CV.mass_nonneg s
  le_one s _ := CI2ZF.Appendix.CV.mass_le_one s

theorem vigodaProfile_R : vigodaProfile.R = 1 := by
  apply le_antisymm
  · exact vigodaProfile.R_le fun (s : ℕ) _ => vigoda_branch_bound s
  · have h := vigodaProfile.le_R (vigodaProfile.RFinite_of_bound
      fun (s : ℕ) _ => vigoda_branch_bound s) (s := 1) le_rfl
    simpa [vigodaProfile, vigodaMass] using h

theorem vigodaProfile_RFinite : vigodaProfile.RFinite :=
  vigodaProfile.RFinite_of_bound fun (s : ℕ) _ => vigoda_branch_bound s

theorem cvProfile_R : cvProfile.R = 1 := by
  apply le_antisymm
  · exact cvProfile.R_le fun (s : ℕ) _ => CI2ZF.Appendix.CV.size_mass_le_one s
  · have h := cvProfile.le_R (cvProfile.RFinite_of_bound
      fun (s : ℕ) _ => CI2ZF.Appendix.CV.size_mass_le_one s) (s := 1) le_rfl
    simpa [cvProfile, CI2ZF.Appendix.CV.mass] using h

theorem cvProfile_RFinite : cvProfile.RFinite :=
  cvProfile.RFinite_of_bound fun (s : ℕ) _ => CI2ZF.Appendix.CV.size_mass_le_one s

variable {V C : Type*} [Fintype V] [Fintype C]

/-! ## The hard list-flip transition `Φ_F^ρ` (`def:flip`) -/

/-- Acceptance probability `ρ_s / s` of a feasible swap of a component of size
`s`; zero for an infeasible swap. -/
def profileAcceptance (P : FlipProfile) (F : HardListInstance V C)
    (X : V → C) (u : V) (c : C) : ℝ :=
  if flipAllowed F (flipSet F.graph X u c)
      (flipConfiguration X (flipSet F.graph X u c) (X u) c) then
    P.ρ (flipSet F.graph X u c).card / (flipSet F.graph X u c).card
  else 0

lemma profileAcceptance_nonneg (P : FlipProfile) (F : HardListInstance V C)
    (X : V → C) (u : V) (c : C) : 0 ≤ profileAcceptance P F X u c := by
  unfold profileAcceptance
  split
  · exact div_nonneg (P.nonneg _ (flipSet_card_pos (G := F.graph) (X := X) (u := u) (c := c)))
      (Nat.cast_nonneg _)
  · exact le_rfl

lemma profileAcceptance_le_one (P : FlipProfile) (F : HardListInstance V C)
    (X : V → C) (u : V) (c : C) : profileAcceptance P F X u c ≤ 1 := by
  unfold profileAcceptance
  split
  · have hpos := flipSet_card_pos (G := F.graph) (X := X) (u := u) (c := c)
    have hcard : (1 : ℝ) ≤ (flipSet F.graph X u c).card := by exact_mod_cast hpos
    rw [div_le_one (by positivity)]
    exact (P.le_one _ hpos).trans hcard
  · exact zero_le_one

/-- Outcome law of one proposal `(u,c)`: hold if `c = X_u`, otherwise swap the
`{X_u,c}`-component of `u` with probability `ρ_s/s` if the swap respects the
lists, and hold otherwise. -/
def profileProposal (P : FlipProfile) (F : HardListInstance V C)
    (X : V → C) (u : V) (c : C) : FinDist (V → C) :=
  if c = X u then FinDist.pure X
  else twoPoint (flipConfiguration X (flipSet F.graph X u c) (X u) c) X
    (profileAcceptance P F X u c)
    (profileAcceptance_nonneg P F X u c)
    (profileAcceptance_le_one P F X u c)

/-- One step of `Φ_F^ρ` on a nonempty vertex set: `(u,c)` uniform in `W × [q]`. -/
def profileStep [Nonempty V] [Nonempty C] (P : FlipProfile)
    (F : HardListInstance V C) (X : V → C) : FinDist (V → C) :=
  (FinDist.uniform (V × C)).bind fun p => profileProposal P F X p.1 p.2

/-- `Φ_F^ρ` exactly as in `def:flip`, including the identity kernel on an
empty vertex set. -/
def flipKernel [Nonempty C] (P : FlipProfile) (F : HardListInstance V C)
    (X : V → C) : FinDist (V → C) :=
  if h : Nonempty V then @profileStep V C _ _ h _ P F X else FinDist.pure X

@[simp] lemma flipKernel_of_nonempty [Nonempty V] [Nonempty C] (P : FlipProfile)
    (F : HardListInstance V C) (X : V → C) : flipKernel P F X = profileStep P F X := by
  unfold flipKernel
  exact dif_pos (inferInstance : Nonempty V)

lemma flipKernel_of_isEmpty [IsEmpty V] [Nonempty C] (P : FlipProfile)
    (F : HardListInstance V C) (X : V → C) : flipKernel P F X = FinDist.pure X := by
  unfold flipKernel
  exact dif_neg (not_nonempty_iff.mpr inferInstance)

/-! ### Bridges to the library's Vigoda and CV hard kernels -/

theorem profileStep_vigoda [Nonempty V] [Nonempty C] (F : HardListInstance V C)
    (X : V → C) : profileStep vigodaProfile F X = PottsCI.Vigoda.hardStep F X := rfl

theorem profileStep_cv [Nonempty V] [Nonempty C] (F : HardListInstance V C)
    (X : V → C) : profileStep cvProfile F X = CI2ZF.Appendix.CV.hardStep F X := rfl

theorem flipKernel_vigoda [Nonempty C] (F : HardListInstance V C) (X : V → C) :
    flipKernel vigodaProfile F X = hardStepWithEmpty F X := rfl

/-! ### Reversibility and stationarity of `Φ_F^ρ` -/

lemma profileProposal_eq_zero (P : FlipProfile) {F : HardListInstance V C}
    {X Y : V → C} (hXY : X ≠ Y) (u : V) (c : C) (hc : c ≠ Y u) :
    (profileProposal P F X u c).w Y = 0 := by
  unfold profileProposal
  split
  · simp [FinDist.pure, Ne.symm hXY]
  · rw [twoPoint_w]
    simp only [if_neg (show Y ≠ X from fun h => hXY h.symm), add_zero]
    rw [if_neg]
    intro hYflip
    apply hc
    have hroot := flipConfiguration_at_start (G := F.graph) (X := X) (u := u) (c := c)
    rw [← hYflip] at hroot
    exact hroot.symm

lemma profileProposal_reversible (P : FlipProfile) {F : HardListInstance V C}
    {X Y : V → C} (hX : F.IsProper X) (hY : F.IsProper Y) (hXY : X ≠ Y) (u : V) :
    (profileProposal P F X u (Y u)).w Y = (profileProposal P F Y u (X u)).w X := by
  by_cases hu : X u = Y u
  · unfold profileProposal
    rw [if_pos hu.symm, if_pos hu]
    simp [FinDist.pure, hXY, Ne.symm hXY]
  · have huY : Y u ≠ X u := fun h => hu h.symm
    unfold profileProposal
    rw [if_neg huY, if_neg hu, twoPoint_w, twoPoint_w]
    simp only [if_neg (show Y ≠ X from fun h => hXY h.symm),
      if_neg (show X ≠ Y from hXY), add_zero]
    by_cases hflip : Y = flipConfiguration X (flipSet F.graph X u (Y u)) (X u) (Y u)
    · obtain ⟨hset, hconf⟩ := flip_involutive hX (u := u) (c := Y u) huY
      rw [← hflip] at hset hconf
      unfold profileAcceptance
      rw [hset, hconf, ← hflip]
      have hAllowedY : flipAllowed F (flipSet F.graph X u (Y u)) Y := fun w _ => hY.2 w
      have hAllowedX : flipAllowed F (flipSet F.graph X u (Y u)) X := fun w _ => hX.2 w
      simp [hAllowedY, hAllowedX]
    · have hflip' : X ≠ flipConfiguration Y (flipSet F.graph Y u (X u)) (Y u) (X u) := by
        intro hflip'
        apply hflip
        obtain ⟨hset, hconf⟩ := flip_involutive hY (u := u) (c := X u) hu
        rw [← hflip'] at hset hconf
        rw [hset]
        exact hconf.symm
      simp [hflip, hflip']

lemma profileStep_w [Nonempty V] [Nonempty C] (P : FlipProfile)
    (F : HardListInstance V C) (X Y : V → C) :
    (profileStep P F X).w Y = ∑ p : V × C,
      ((Fintype.card (V × C) : ℝ))⁻¹ * (profileProposal P F X p.1 p.2).w Y := rfl

lemma profileStep_support [Nonempty V] [Nonempty C] (P : FlipProfile)
    {F : HardListInstance V C} {X Y : V → C}
    (hX : F.IsProper X) (hY : ¬F.IsProper Y) : (profileStep P F X).w Y = 0 := by
  rw [profileStep_w]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [mul_eq_zero]
  right
  obtain ⟨u, c⟩ := p
  have hXY : X ≠ Y := fun h => hY (h ▸ hX)
  unfold profileProposal
  split
  · simp [FinDist.pure, Ne.symm hXY]
  · rename_i hcx
    rw [twoPoint_w]
    simp only [if_neg (show Y ≠ X from fun h => hXY h.symm), add_zero]
    by_cases hYflip : Y = flipConfiguration X (flipSet F.graph X u c) (X u) c
    · rw [if_pos hYflip]
      unfold profileAcceptance
      rw [if_neg]
      intro hAllowed
      exact hY (hYflip ▸ flip_preserves_proper hX hcx hAllowed)
    · rw [if_neg hYflip]

/-- Detailed balance of `Φ_F^ρ` for the uniform law on proper list-colourings. -/
theorem profileStep_reversible [Nonempty V] [Nonempty C] (P : FlipProfile)
    {F : HardListInstance V C} {X Y : V → C} (hX : F.IsProper X) (hY : F.IsProper Y) :
    (profileStep P F X).w Y = (profileStep P F Y).w X := by
  rcases eq_or_ne X Y with rfl | hXY
  · rfl
  · rw [profileStep_w, profileStep_w, Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hleft : ∑ c : C, ((Fintype.card (V × C) : ℝ))⁻¹ *
          (profileProposal P F X u c).w Y =
        ((Fintype.card (V × C) : ℝ))⁻¹ * (profileProposal P F X u (Y u)).w Y := by
      refine Finset.sum_eq_single (Y u) (fun c _ hc => ?_)
        (fun h => absurd (Finset.mem_univ _) h)
      rw [profileProposal_eq_zero P hXY u c hc, mul_zero]
    have hright : ∑ c : C, ((Fintype.card (V × C) : ℝ))⁻¹ *
          (profileProposal P F Y u c).w X =
        ((Fintype.card (V × C) : ℝ))⁻¹ * (profileProposal P F Y u (X u)).w X := by
      refine Finset.sum_eq_single (X u) (fun c _ hc => ?_)
        (fun h => absurd (Finset.mem_univ _) h)
      rw [profileProposal_eq_zero P hXY.symm u c hc, mul_zero]
    rw [hleft, hright, profileProposal_reversible P hX hY hXY u]

lemma flipKernel_support [Nonempty C] (P : FlipProfile)
    {F : HardListInstance V C} {X Y : V → C}
    (hX : F.IsProper X) (hY : ¬F.IsProper Y) : (flipKernel P F X).w Y = 0 := by
  by_cases h : Nonempty V
  · rw [flipKernel_of_nonempty]
    exact profileStep_support P hX hY
  · have hXY : Y ≠ X := fun e => hY (e ▸ hX)
    rw [flipKernel, dif_neg h]
    simp [FinDist.pure, hXY]

/-- Detailed balance of `Φ_F^ρ` on proper list-colourings, including the empty
vertex set. -/
theorem flipKernel_reversible [Nonempty C] (P : FlipProfile)
    {F : HardListInstance V C} {X Y : V → C} (hX : F.IsProper X) (hY : F.IsProper Y) :
    (flipKernel P F X).w Y = (flipKernel P F Y).w X := by
  by_cases h : Nonempty V
  · rw [flipKernel_of_nonempty, flipKernel_of_nonempty]
    exact profileStep_reversible P hX hY
  · have : IsEmpty V := not_nonempty_iff.mp h
    have hXY : X = Y := Subsingleton.elim X Y
    subst hXY
    rfl

/-- `Φ_F^ρ` preserves the uniform law on the proper list-colourings. -/
theorem flipKernel_stationary [Nonempty C] (P : FlipProfile)
    (F : HardListInstance V C) (hne : ∃ X : V → C, F.IsProper X) :
    FinDist.IsStationary (flipKernel P F) (uniformProperFibre F hne) := by
  apply FinDist.ext
  funext Y
  simp only [FinDist.bind_w]
  by_cases hY : F.IsProper Y
  · have hterm : ∀ X : V → C,
        (uniformProperFibre F hne).w X * (flipKernel P F X).w Y =
          (uniformProperFibre F hne).w X * (flipKernel P F Y).w X := by
      intro X
      by_cases hX : F.IsProper X
      · rw [flipKernel_reversible P hX hY]
      · rw [uniformProperFibre_w, if_neg hX, zero_mul, zero_mul]
    rw [Finset.sum_congr rfl fun X _ => hterm X]
    have hsum : ∑ X : V → C, (uniformProperFibre F hne).w X * (flipKernel P F Y).w X =
        (((Finset.univ.filter fun Z : V → C => F.IsProper Z).card : ℝ))⁻¹ := by
      simp only [uniformProperFibre_w, ite_mul, zero_mul]
      rw [← Finset.sum_filter, ← Finset.mul_sum]
      have hfull : ∑ X ∈ Finset.univ.filter (fun Z : V → C => F.IsProper Z),
            (flipKernel P F Y).w X = ∑ X : V → C, (flipKernel P F Y).w X := by
        refine Finset.sum_subset (Finset.filter_subset _ _) ?_
        intro X _ hX
        apply flipKernel_support P hY
        intro hp
        exact hX (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
      rw [hfull, FinDist.sum_one, mul_one]
    rw [hsum, uniformProperFibre_w, if_pos hY]
  · have hterm : ∀ X : V → C,
        (uniformProperFibre F hne).w X * (flipKernel P F X).w Y = 0 := by
      intro X
      by_cases hX : F.IsProper X
      · rw [flipKernel_support P hX hY, mul_zero]
      · rw [uniformProperFibre_w, if_neg hX, zero_mul]
    rw [Finset.sum_eq_zero fun X _ => hterm X, uniformProperFibre_w, if_neg hY]

/-! ## The soft flip kernel `K_{x,ρ}` for `x ∈ (0,1]` (`def:soft-kernel`) -/

namespace Soft

variable (I : PinningData V C)

/-- The conditional law of the active set given the colouring, for every
`x ∈ (0,1]`.  (The library version `activeLawGivenSpin` needs `x < 1`.) -/
def activeLaw (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) (σ : V → C) :
    FinDist (Finset I.Constraint) where
  w := fun A => I.jointActiveWeight x A σ / I.weight x σ
  nonneg := fun A => div_nonneg
    (I.jointActiveWeight_nonneg hx0.le hx1 A σ) (I.weight_pos hx0 σ).le
  sum_one := by
    rw [← Finset.sum_div, I.sum_jointActiveWeight_eq_weight]
    exact div_self (I.weight_pos hx0 σ).ne'

@[simp] lemma activeLaw_w (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) (σ : V → C)
    (A : Finset I.Constraint) :
    (activeLaw I x hx0 hx1 σ).w A = I.jointActiveWeight x A σ / I.weight x σ := rfl

/-- Sample `A` given the colouring, apply the hard kernel of `A`, forget `A`. -/
def softKernelOf (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (H : ∀ A : Finset I.Constraint, PinningData.HardFibreKernel I A) :
    (V → C) → FinDist (V → C) :=
  fun σ => (activeLaw I x hx0 hx1 σ).bind fun A => (H A).kernel σ

@[simp] lemma softKernelOf_w (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (H : ∀ A : Finset I.Constraint, PinningData.HardFibreKernel I A) (σ τ : V → C) :
    (softKernelOf I x hx0 hx1 H σ).w τ =
      ∑ A : Finset I.Constraint,
        I.jointActiveWeight x A σ / I.weight x σ * ((H A).kernel σ).w τ := rfl

/-- On `x < 1` this is exactly the library's `PinningData.softKernel`. -/
theorem softKernelOf_eq_library (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (H : ∀ A : Finset I.Constraint, PinningData.HardFibreKernel I A) :
    softKernelOf I x hx0 hx1.le H = I.softKernel x hx0 hx1 H := rfl

private lemma weighted_hard_step (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (H : ∀ A : Finset I.Constraint, PinningData.HardFibreKernel I A)
    (A : Finset I.Constraint) (τ : V → C) :
    (∑ σ : V → C, I.jointActiveWeight x A σ * ((H A).kernel σ).w τ) =
      I.jointActiveWeight x A τ := by
  by_cases hmass : 0 < I.activeMass x A
  · have hne : (I.compatibleColorings A).Nonempty :=
      I.compatibleColorings_nonempty_of_activeMass_pos hmass
    have hconditional : FinDist.IsStationary (H A).kernel
        (I.spinLawGivenActive x hx0.le hx1 A hmass) := by
      rw [I.spinLawGivenActive_eq_uniformHardFibre hx0.le hx1 A hmass]
      exact (H A).stationary hne
    have hcomponent := congrArg (fun μ : FinDist (V → C) => μ.w τ) hconditional
    have hnormalized : (∑ σ : V → C,
          I.jointActiveWeight x A σ / I.activeMass x A * ((H A).kernel σ).w τ) =
        I.jointActiveWeight x A τ / I.activeMass x A := hcomponent
    calc (∑ σ : V → C, I.jointActiveWeight x A σ * ((H A).kernel σ).w τ) =
          I.activeMass x A * (∑ σ : V → C,
            I.jointActiveWeight x A σ / I.activeMass x A * ((H A).kernel σ).w τ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          field_simp
      _ = I.activeMass x A * (I.jointActiveWeight x A τ / I.activeMass x A) := by
          rw [hnormalized]
      _ = I.jointActiveWeight x A τ := by field_simp
  · have hmass0 : I.activeMass x A = 0 := by
      have hnonneg : 0 ≤ I.activeMass x A :=
        Finset.sum_nonneg fun σ _ => I.jointActiveWeight_nonneg hx0.le hx1 A σ
      linarith
    have hjoint0 : ∀ σ : V → C, I.jointActiveWeight x A σ = 0 := by
      intro σ
      have hle : I.jointActiveWeight x A σ ≤ I.activeMass x A :=
        Finset.single_le_sum (fun ρ _ => I.jointActiveWeight_nonneg hx0.le hx1 A ρ)
          (Finset.mem_univ σ)
      have hnonneg := I.jointActiveWeight_nonneg hx0.le hx1 A σ
      linarith
    simp [hjoint0]

/-- The Gibbs law is stationary for the soft kernel for every `x ∈ (0,1]`. -/
theorem softKernelOf_stationary [Nonempty C] (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (H : ∀ A : Finset I.Constraint, PinningData.HardFibreKernel I A) :
    FinDist.IsStationary (softKernelOf I x hx0 hx1 H)
      (I.gibbs x hx0.le (I.partition_pos_of_parameter_pos hx0)) := by
  apply FinDist.ext
  funext τ
  simp only [FinDist.bind_w, softKernelOf_w]
  let Z := I.partition x
  change (∑ σ : V → C, I.weight x σ / Z * ∑ A : Finset I.Constraint,
      I.jointActiveWeight x A σ / I.weight x σ * ((H A).kernel σ).w τ) = I.weight x τ / Z
  calc (∑ σ : V → C, I.weight x σ / Z * ∑ A : Finset I.Constraint,
        I.jointActiveWeight x A σ / I.weight x σ * ((H A).kernel σ).w τ) =
        ∑ σ : V → C, ∑ A : Finset I.Constraint,
          I.jointActiveWeight x A σ * ((H A).kernel σ).w τ / Z := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun A _ => ?_
        have hw : I.weight x σ ≠ 0 := (I.weight_pos hx0 σ).ne'
        field_simp
    _ = ∑ A : Finset I.Constraint, ∑ σ : V → C,
          I.jointActiveWeight x A σ * ((H A).kernel σ).w τ / Z := Finset.sum_comm
    _ = ∑ A : Finset I.Constraint,
          (∑ σ : V → C, I.jointActiveWeight x A σ * ((H A).kernel σ).w τ) / Z := by
        refine Finset.sum_congr rfl fun A _ => ?_
        rw [Finset.sum_div]
    _ = ∑ A : Finset I.Constraint, I.jointActiveWeight x A τ / Z := by
        refine Finset.sum_congr rfl fun A _ => ?_
        rw [weighted_hard_step I x hx0 hx1 H A τ]
    _ = (∑ A : Finset I.Constraint, I.jointActiveWeight x A τ) / Z := by
        rw [Finset.sum_div]
    _ = I.weight x τ / Z := by rw [I.sum_jointActiveWeight_eq_weight]

end Soft

/-- The hard-fibre kernel `Φ^ρ_{F_A}` of an active set `A`. -/
def flipFibreKernel [Nonempty C] (P : FlipProfile) (I : PinningData V C)
    (A : Finset I.Constraint) : PinningData.HardFibreKernel I A where
  kernel := flipKernel P (activeHardListInstance I A)
  supported := by
    intro X Y hX hY
    apply flipKernel_support P ((activeHardListInstance_isProper_iff I A X).mpr hX)
    exact fun h => hY ((activeHardListInstance_isProper_iff I A Y).mp h)
  stationary := by
    intro hne
    have hproper : ∃ X : V → C, (activeHardListInstance I A).IsProper X := by
      obtain ⟨X, hX⟩ := hne
      exact ⟨X, (activeHardListInstance_isProper_iff I A X).mpr (Finset.mem_filter.mp hX).2⟩
    have hfibres : I.uniformHardFibre A hne =
        uniformProperFibre (activeHardListInstance I A) hproper := by
      apply FinDist.ext
      funext X
      rw [I.uniformHardFibre_w, uniformProperFibre_w]
      have hcard : (I.compatibleColorings A).card =
          (Finset.univ.filter fun Y : V → C => (activeHardListInstance I A).IsProper Y).card := by
        congr 1
        ext Y
        simp [PinningData.compatibleColorings, activeHardListInstance_isProper_iff I A Y]
      rw [hcard]
      exact if_congr (activeHardListInstance_isProper_iff I A X).symm rfl rfl
    rw [hfibres]
    exact flipKernel_stationary P _ hproper

/-- **`def:soft-kernel`.**  The soft flip kernel `K_{x,ρ}^{G,τ}` for an
arbitrary profile `ρ` and every `x ∈ (0,1]`: sample the active constraints
given the current colouring, apply `Φ^ρ_{F_A}`, and forget `A`. -/
def softFlipKernel [Nonempty C] (P : FlipProfile) (I : PinningData V C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) : (V → C) → FinDist (V → C) :=
  Soft.softKernelOf I x hx0 hx1 fun A => flipFibreKernel P I A

@[simp] lemma softFlipKernel_w [Nonempty C] (P : FlipProfile) (I : PinningData V C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) (σ τ : V → C) :
    (softFlipKernel P I x hx0 hx1 σ).w τ = ∑ A : Finset I.Constraint,
      I.jointActiveWeight x A σ / I.weight x σ *
        (flipKernel P (activeHardListInstance I A) σ).w τ := rfl

/-! ### Bridges to the library soft kernels on `0 < x < 1` -/

theorem softFlipKernel_vigoda [Nonempty V] [Nonempty C] (I : PinningData V C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    softFlipKernel vigodaProfile I x hx0 hx1.le = softVigodaKernel I x hx0 hx1 := by
  funext σ
  apply FinDist.ext
  funext τ
  rw [softFlipKernel_w]
  simp only [flipKernel_of_nonempty, profileStep_vigoda]
  rfl

theorem softFlipKernel_vigoda_withEmpty [Nonempty C] (I : PinningData V C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    softFlipKernel vigodaProfile I x hx0 hx1.le = softVigodaKernelWithEmpty I x hx0 hx1 := by
  by_cases h : Nonempty V
  · rw [softVigodaKernelWithEmpty_of_nonempty]
    exact softFlipKernel_vigoda I x hx0 hx1
  · have : IsEmpty V := not_nonempty_iff.mp h
    rw [softVigodaKernelWithEmpty_of_empty]
    funext σ
    apply FinDist.ext
    funext τ
    have hστ : τ = σ := Subsingleton.elim τ σ
    subst hστ
    have hs := (softFlipKernel vigodaProfile I x hx0 hx1.le τ).sum_one
    rw [Fintype.sum_subsingleton _ τ] at hs
    rw [hs]
    simp [FinDist.pure]

theorem softFlipKernel_cv [Nonempty V] [Nonempty C] (I : PinningData V C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    softFlipKernel cvProfile I x hx0 hx1.le = CI2ZF.Appendix.CV.softCVKernel I x hx0 hx1 := by
  funext σ
  apply FinDist.ext
  funext τ
  rw [softFlipKernel_w]
  simp only [flipKernel_of_nonempty, profileStep_cv]
  rfl

/-! ## `lem:soft-stationary`: stationarity, reversibility, irreducibility -/

/-- Detailed balance of a kernel with respect to a law. -/
def IsReversible {S : Type*} [Fintype S] (K : S → FinDist S) (π : FinDist S) : Prop :=
  ∀ σ τ, π.w σ * (K σ).w τ = π.w τ * (K τ).w σ

/-- Detailed balance implies stationarity. -/
theorem IsReversible.isStationary {S : Type*} [Fintype S] {K : S → FinDist S}
    {π : FinDist S} (h : IsReversible K π) : FinDist.IsStationary K π := by
  apply FinDist.ext
  funext τ
  simp only [FinDist.bind_w]
  calc ∑ σ, π.w σ * (K σ).w τ = ∑ σ, π.w τ * (K τ).w σ :=
        Finset.sum_congr rfl fun σ _ => h σ τ
    _ = π.w τ := by rw [← Finset.mul_sum, FinDist.sum_one, mul_one]

/-- `n`-step kernel (`K^0` is the identity kernel). -/
def kernelPow {S : Type*} [Fintype S] (K : S → FinDist S) : ℕ → S → FinDist S
  | 0 => fun σ => @FinDist.pure S _ (Classical.decEq S) σ
  | n + 1 => fun σ => (kernelPow K n σ).bind K

/-- Irreducibility: every state reaches every state with positive probability
in some number of steps. -/
def IsIrreducible {S : Type*} [Fintype S] (K : S → FinDist S) : Prop :=
  ∀ σ τ, ∃ n, 0 < (kernelPow K n σ).w τ

lemma kernelPow_pos_of_reflTransGen {S : Type*} [Fintype S]
    (K : S → FinDist S) {σ τ : S}
    (h : Relation.ReflTransGen (fun a b => 0 < (K a).w b) σ τ) :
    ∃ n, 0 < (kernelPow K n σ).w τ := by
  induction h with
  | refl => exact ⟨0, by simp [kernelPow, FinDist.pure]⟩
  | tail _ hstep ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 1, ?_⟩
      rename_i b c _
      change 0 < ∑ z, (kernelPow K n σ).w z * (K z).w c
      exact lt_of_lt_of_le (mul_pos hn hstep)
        (Finset.single_le_sum (f := fun z => (kernelPow K n σ).w z * (K z).w c)
          (fun z _ => mul_nonneg ((kernelPow K n σ).nonneg z) ((K z).nonneg c))
          (Finset.mem_univ b))

section Stationary

variable [Nonempty C] (P : FlipProfile) (I : PinningData V C)

/-- **`lem:soft-stationary`, stationarity.**  For every profile and every
`x ∈ (0,1]`, the Gibbs law is stationary for `K_{x,ρ}`. -/
theorem softFlipKernel_stationary (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    FinDist.IsStationary (softFlipKernel P I x hx0 hx1)
      (I.gibbs x hx0.le (I.partition_pos_of_parameter_pos hx0)) :=
  Soft.softKernelOf_stationary I x hx0 hx1 _

private lemma joint_flip_symm (x : ℝ) (A : Finset I.Constraint) (σ τ : V → C) :
    I.jointActiveWeight x A σ * (flipKernel P (activeHardListInstance I A) σ).w τ =
      I.jointActiveWeight x A τ * (flipKernel P (activeHardListInstance I A) τ).w σ := by
  have hσ := activeHardListInstance_isProper_iff I A σ
  have hτ := activeHardListInstance_isProper_iff I A τ
  by_cases hσA : I.ActiveCompatible σ A <;> by_cases hτA : I.ActiveCompatible τ A
  · rw [I.jointActiveWeight_eq_of_compatible (x := x) hσA hτA,
      flipKernel_reversible P (hσ.mpr hσA) (hτ.mpr hτA)]
  · rw [flipKernel_support P (hσ.mpr hσA) (fun h => hτA (hτ.mp h)),
      show I.jointActiveWeight x A τ = 0 by simp [PinningData.jointActiveWeight, hτA]]
    ring
  · rw [flipKernel_support P (hτ.mpr hτA) (fun h => hσA (hσ.mp h)),
      show I.jointActiveWeight x A σ = 0 by simp [PinningData.jointActiveWeight, hσA]]
    ring
  · rw [PinningData.jointActiveWeight, if_neg hσA, PinningData.jointActiveWeight, if_neg hτA]
    ring

/-- **`lem:soft-stationary`, reversibility.**  For every profile and every
`x ∈ (0,1]`, `K_{x,ρ}` satisfies detailed balance with respect to the Gibbs
law. -/
theorem softFlipKernel_reversible (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    IsReversible (softFlipKernel P I x hx0 hx1)
      (I.gibbs x hx0.le (I.partition_pos_of_parameter_pos hx0)) := by
  intro σ τ
  have hσ : I.weight x σ ≠ 0 := (I.weight_pos hx0 σ).ne'
  have hτ : I.weight x τ ≠ 0 := (I.weight_pos hx0 τ).ne'
  have key : ∀ ξ η : V → C, I.weight x ξ ≠ 0 →
      (I.gibbs x hx0.le (I.partition_pos_of_parameter_pos hx0)).w ξ *
        (softFlipKernel P I x hx0 hx1 ξ).w η =
      (∑ A : Finset I.Constraint, I.jointActiveWeight x A ξ *
        (flipKernel P (activeHardListInstance I A) ξ).w η) / I.partition x := by
    intro ξ η hξ
    change I.weight x ξ / I.partition x * _ = _
    rw [softFlipKernel_w, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun A _ => ?_
    field_simp
  rw [key σ τ hσ, key τ σ hτ]
  congr 1
  exact Finset.sum_congr rfl fun A _ => joint_flip_symm P I x A σ τ

/-- On the empty active set, a proposal `(u,c)` with `c ≠ σ_u` recolours the
single vertex `u` with probability `ρ₁`. -/
private lemma empty_active_step_pos [Nonempty V] (hρ : 0 < P.ρ 1) (σ : V → C) (u : V)
    (c : C) (hc : c ≠ σ u) :
    0 < (flipKernel P (activeHardListInstance I ∅) σ).w (Function.update σ u c) := by
  set F := activeHardListInstance I ∅ with hF
  have hnoadj : ∀ a b : V, ¬ F.graph.Adj a b := by
    rintro a b ⟨e, he, _⟩
    simp at he
  have hset : flipSet F.graph σ u c = {u} := by
    ext w
    simp only [mem_flipSet, Finset.mem_singleton]
    constructor
    · intro h
      induction h with
      | refl => rfl
      | tail _ hstep _ => exact absurd hstep.1 (hnoadj _ _)
    · rintro rfl
      exact Relation.ReflTransGen.refl
  have hconf : flipConfiguration σ (flipSet F.graph σ u c) (σ u) c = Function.update σ u c := by
    rw [hset]
    funext w
    by_cases hw : w = u
    · subst hw
      simp [flipConfiguration]
    · simp [flipConfiguration, hw]
  have hallowed : flipAllowed F (flipSet F.graph σ u c)
      (flipConfiguration σ (flipSet F.graph σ u c) (σ u) c) := by
    intro w _
    simp [hF, activeHardListInstance, activeList]
  have hacc : profileAcceptance P F σ u c = P.ρ 1 := by
    unfold profileAcceptance
    rw [if_pos hallowed, hset]
    simp
  rw [flipKernel_of_nonempty, profileStep_w]
  have hterm : 0 < ((Fintype.card (V × C) : ℝ))⁻¹ * (profileProposal P F σ u c).w
      (Function.update σ u c) := by
    apply mul_pos (by positivity)
    unfold profileProposal
    rw [if_neg hc, twoPoint_w, ← hconf, if_pos rfl, hacc]
    have : 0 ≤ (if flipConfiguration σ (flipSet F.graph σ u c) (σ u) c = σ then
        1 - P.ρ 1 else 0) := by
      split
      · linarith [P.le_one 1 le_rfl]
      · exact le_rfl
    linarith
  exact lt_of_lt_of_le hterm (Finset.single_le_sum
    (f := fun p : V × C => ((Fintype.card (V × C) : ℝ))⁻¹ *
      (profileProposal P F σ p.1 p.2).w (Function.update σ u c))
    (fun p _ => mul_nonneg (by positivity) ((profileProposal P F σ p.1 p.2).nonneg _))
    (Finset.mem_univ (u, c)))

/-- A single-site recolouring has positive soft-kernel probability when
`ρ₁ > 0`: the empty active set has probability `x^M / w(σ) > 0`. -/
theorem softFlipKernel_update_pos (hρ : 0 < P.ρ 1) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (σ : V → C) (u : V) (c : C) :
    0 < (softFlipKernel P I x hx0 hx1 σ).w (Function.update σ u c) := by
  have : Nonempty V := ⟨u⟩
  by_cases hc : c = σ u
  · -- the target is `σ` itself; use the hold probability of the empty set
    subst hc
    rw [Function.update_eq_self]
    have hpos : 0 < I.jointActiveWeight x ∅ σ / I.weight x σ *
        (flipKernel P (activeHardListInstance I ∅) σ).w σ := by
      apply mul_pos
      · apply div_pos _ (I.weight_pos hx0 σ)
        rw [PinningData.jointActiveWeight, if_pos (by intro k hk; simp at hk),
          PinningData.activeScalar_eq]
        simp only [Finset.card_empty, pow_zero, one_mul, Nat.sub_zero]
        exact pow_pos hx0 _
      · rw [flipKernel_of_nonempty, profileStep_w]
        have hterm : 0 < ((Fintype.card (V × C) : ℝ))⁻¹ *
            (profileProposal P (activeHardListInstance I ∅) σ u (σ u)).w σ := by
          apply mul_pos (by positivity)
          simp [profileProposal, FinDist.pure]
        exact lt_of_lt_of_le hterm (Finset.single_le_sum
          (f := fun p : V × C => ((Fintype.card (V × C) : ℝ))⁻¹ *
            (profileProposal P (activeHardListInstance I ∅) σ p.1 p.2).w σ)
          (fun p _ => mul_nonneg (by positivity) ((profileProposal P _ σ p.1 p.2).nonneg _))
          (Finset.mem_univ (u, σ u)))
    rw [softFlipKernel_w]
    exact lt_of_lt_of_le hpos (Finset.single_le_sum
      (f := fun A : Finset I.Constraint => I.jointActiveWeight x A σ / I.weight x σ *
        (flipKernel P (activeHardListInstance I A) σ).w σ)
      (fun A _ => mul_nonneg (div_nonneg (I.jointActiveWeight_nonneg hx0.le hx1 A σ)
        (I.weight_pos hx0 σ).le) ((flipKernel P _ σ).nonneg _))
      (Finset.mem_univ ∅))
  · have hpos : 0 < I.jointActiveWeight x ∅ σ / I.weight x σ *
        (flipKernel P (activeHardListInstance I ∅) σ).w (Function.update σ u c) := by
      apply mul_pos
      · apply div_pos _ (I.weight_pos hx0 σ)
        rw [PinningData.jointActiveWeight, if_pos (by intro k hk; simp at hk),
          PinningData.activeScalar_eq]
        simp only [Finset.card_empty, pow_zero, one_mul, Nat.sub_zero]
        exact pow_pos hx0 _
      · exact empty_active_step_pos P I hρ σ u c hc
    rw [softFlipKernel_w]
    exact lt_of_lt_of_le hpos (Finset.single_le_sum
      (f := fun A : Finset I.Constraint => I.jointActiveWeight x A σ / I.weight x σ *
        (flipKernel P (activeHardListInstance I A) σ).w (Function.update σ u c))
      (fun A _ => mul_nonneg (div_nonneg (I.jointActiveWeight_nonneg hx0.le hx1 A σ)
        (I.weight_pos hx0 σ).le) ((flipKernel P _ σ).nonneg _))
      (Finset.mem_univ ∅))

/-- **`lem:soft-stationary`, irreducibility.**  If `ρ₁ > 0`, then for every
`x ∈ (0,1]` the soft kernel is irreducible on the full colouring space
`[q]^{V^τ}`. -/
theorem softFlipKernel_irreducible (hρ : 0 < P.ρ 1) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    IsIrreducible (softFlipKernel P I x hx0 hx1) := by
  classical
  intro σ τ
  apply kernelPow_pos_of_reflTransGen
  have main : ∀ k : ℕ, ∀ ξ : V → C, hamCard ξ τ = k →
      Relation.ReflTransGen (fun a b => 0 < (softFlipKernel P I x hx0 hx1 a).w b) ξ τ := by
    intro k
    induction k with
    | zero =>
        intro ξ h
        rw [hamCard_eq_zero h]
    | succ k ih =>
        intro ξ h
        obtain ⟨z, hz1, hzk⟩ := exists_intermediate h
        obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hz1
        have hzupd : z = Function.update ξ u (z u) := by
          funext w
          by_cases hw : w = u
          · subst hw; simp
          · rw [Function.update_of_ne hw]
            by_contra hne
            have hm : w ∈ Finset.univ.filter (fun v => ξ v ≠ z v) := by
              simp [Ne.symm hne]
            rw [hu] at hm
            exact hw (Finset.mem_singleton.mp hm)
        refine Relation.ReflTransGen.head ?_ (ih z hzk)
        rw [hzupd]
        exact softFlipKernel_update_pos P I hρ x hx0 hx1 ξ u (z u)
  exact main _ σ rfl

/-- **`lem:soft-stationary`, the paper's statement.**  For every profile `ρ` and
every `x ∈ (0,1]`, `K_{x,ρ}^{G,τ}` is reversible with stationary law
`μ^τ_{G,x}`; if `ρ₁ > 0` it is irreducible on `[q]^{V^τ}`. -/
theorem lem_soft_stationary (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    IsReversible (softFlipKernel P I x hx0 hx1)
        (I.gibbs x hx0.le (I.partition_pos_of_parameter_pos hx0)) ∧
      FinDist.IsStationary (softFlipKernel P I x hx0 hx1)
        (I.gibbs x hx0.le (I.partition_pos_of_parameter_pos hx0)) ∧
      (0 < P.ρ 1 → IsIrreducible (softFlipKernel P I x hx0 hx1)) :=
  ⟨softFlipKernel_reversible P I x hx0 hx1, softFlipKernel_stationary P I x hx0 hx1,
    fun hρ => softFlipKernel_irreducible P I hρ x hx0 hx1⟩

end Stationary

/-! ## Common coins for every `x ∈ (0,1]` -/

lemma coinParam {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : 1 - x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨by linarith, by linarith⟩

omit [Fintype C] in
lemma activation_coordinate_weight_le (I : PinningData V C) (X : V → C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) (A : Finset I.Constraint) (k : I.Constraint) :
    (mapLaw (bernoulliLaw (1 - x) (coinParam hx0 hx1))
      (fun b => b && decide (I.constraintSatisfied X k))).w (decide (k ∈ A)) =
      (if k ∈ A then I.activationFactor x X k else x) / I.constraintFactor x X k := by
  by_cases hs : I.constraintSatisfied X k <;> by_cases ha : k ∈ A <;>
    simp [mapLaw, FinDist.bind_w, FinDist.pure, bernoulliLaw,
      PinningData.activationFactor, PinningData.constraintFactor, hs, ha, hx0.ne']

/-- Independent Bernoulli(`1-x`) coins, restricted to the satisfied
constraints, have the conditional active-set law, for every `x ∈ (0,1]`. -/
theorem activatedSet_law_le (I : PinningData V C) (X : V → C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    mapLaw (commonCoinLaw (K := I.Constraint) (1 - x) (coinParam hx0 hx1))
      (activatedSet I X) = Soft.activeLaw I x hx0 hx1 X := by
  let ht := coinParam hx0 hx1
  let p := commonCoinLaw (K := I.Constraint) (1 - x) ht
  let f : I.Constraint → Bool → Bool := fun k b => b && decide (I.constraintSatisfied X k)
  have hm : mapLaw p (fun ω k => f k (ω k)) =
      productLaw (fun k => mapLaw (bernoulliLaw (1 - x) ht) (f k)) :=
    map_productLaw (fun _ : I.Constraint => bernoulliLaw (1 - x) ht) f
  have hcomp : mapLaw p (activatedSet I X) =
      mapLaw (productLaw (fun k => mapLaw (bernoulliLaw (1 - x) ht) (f k)))
        bitsEquivFinset := by
    calc _ = mapLaw (mapLaw p (fun ω k => f k (ω k))) bitsEquivFinset :=
          (mapLaw_comp p (fun ω k => f k (ω k)) bitsEquivFinset).symm
      _ = _ := congrArg (fun law : FinDist (I.Constraint → Bool) =>
          mapLaw law bitsEquivFinset) hm
  change mapLaw p (activatedSet I X) = _
  rw [hcomp]
  apply FinDist.ext
  funext A
  rw [mapLaw_equiv_w]
  change (∏ k : I.Constraint, (mapLaw (bernoulliLaw (1 - x) ht)
    (fun b => b && decide (I.constraintSatisfied X k))).w (decide (k ∈ A))) = _
  simp_rw [activation_coordinate_weight_le I X x hx0 hx1 A]
  rw [Finset.prod_div_distrib, ← I.weight_eq_constraintProduct]
  have hn : (∏ k : I.Constraint, if k ∈ A then I.activationFactor x X k else x) =
      I.activeSetWeight x X A := by
    simp [PinningData.activeSetWeight, Finset.prod_ite, Finset.filter_not]
  rw [hn, I.activeSetWeight_eq_jointActiveWeight]
  rfl

/-- The soft flip kernel is the common-coin mixture of the hard flip kernels,
for every `x ∈ (0,1]`. -/
theorem softFlipKernel_eq_coin_mixture [Nonempty C] (P : FlipProfile)
    (I : PinningData V C) (X : V → C) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    softFlipKernel P I x hx0 hx1 X =
      (commonCoinLaw (K := I.Constraint) (1 - x) (coinParam hx0 hx1)).bind
        (fun ω => flipKernel P (activeHardListInstance I (activatedSet I X ω)) X) := by
  change (Soft.activeLaw I x hx0 hx1 X).bind
    (fun A => flipKernel P (activeHardListInstance I A) X) = _
  rw [← activatedSet_law_le I X x hx0 hx1]
  exact mapLaw_bind _ _ _

/-! ## `lem:boundary-sensitivity`: hard list deletions -/

section HardDeletion

variable (P : FlipProfile)

lemma profileProposal_delete_eq_of_root_ne (F : HardListInstance V C)
    (X : V → C) (r : V) (a : C) (u : V) (c : C)
    (hroot : flipConfiguration X (flipSet F.graph X u c) (X u) c r ≠ a) :
    profileProposal P (deleteListColour F r a) X u c = profileProposal P F X u c := by
  unfold profileProposal
  split
  · rfl
  · congr 1
    unfold profileAcceptance
    simp only [deleteListColour_graph, flipAllowed_deleteListColour_iff]
    have hi : (r ∈ flipSet F.graph X u c →
        flipConfiguration X (flipSet F.graph X u c) (X u) c r ≠ a) := fun _ => hroot
    exact if_congr ⟨And.left, fun h => ⟨h, hi⟩⟩ rfl rfl

lemma profileProposal_delete_eq_pure_of_root_eq (F : HardListInstance V C)
    (X : V → C) (r : V) (a : C) (u : V) (c : C) (hra : X r ≠ a)
    (hroot : flipConfiguration X (flipSet F.graph X u c) (X u) c r = a) :
    profileProposal P (deleteListColour F r a) X u c = FinDist.pure X := by
  unfold profileProposal
  split
  · rfl
  · have hr : r ∈ flipSet F.graph X u c := by
      by_contra hn
      rw [flipConfiguration_of_not_mem hn] at hroot
      exact hra hroot
    have hbad : ¬ flipAllowed (deleteListColour F r a) (flipSet F.graph X u c)
        (flipConfiguration X (flipSet F.graph X u c) (X u) c) := by
      intro h
      exact ((flipAllowed_deleteListColour_iff F r a _ _).mp h).2 hr hroot
    have hp : profileAcceptance P (deleteListColour F r a) X u c = 0 := by
      unfold profileAcceptance
      exact if_neg hbad
    apply FinDist.ext
    funext Y
    rw [twoPoint_w, hp]
    simp [FinDist.pure]
    exact ite_self 0

lemma profileProposal_W_pure_le (F : HardListInstance V C) (X : V → C) (u : V) (c : C) :
    FinDist.W ham (profileProposal P F X u c) (FinDist.pure X) ≤
      P.ρ (flipSet F.graph X u c).card := by
  have hpos := flipSet_card_pos (G := F.graph) (X := X) (u := u) (c := c)
  unfold profileProposal
  split
  · rw [FinDist.W_self ham_nonneg ham_self]
    exact P.nonneg _ hpos
  · rename_i hc
    apply (FinDist.W_le_cost ham_nonneg (FinDist.Coupling.prod _ (FinDist.pure X))).trans
    rw [twoPoint_pure_cost, ham_flip_eq_card hc]
    unfold profileAcceptance
    split
    · have hs : ((flipSet F.graph X u c).card : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
      rw [div_mul_cancel₀ _ hs]
    · simpa using P.nonneg _ hpos

lemma profileProposal_delete_W_bound (F : HardListInstance V C) (X : V → C)
    (r : V) (a : C) (hra : X r ≠ a) (u : V) (c : C) :
    FinDist.W ham (profileProposal P F X u c)
        (profileProposal P (deleteListColour F r a) X u c) ≤
      if u ∈ flipSet F.graph X r a ∧ c = (if X u = X r then a else X r)
      then P.ρ (flipSet F.graph X r a).card else 0 := by
  by_cases hchange : flipConfiguration X (flipSet F.graph X u c) (X u) c r = a
  · rw [profileProposal_delete_eq_pure_of_root_eq P F X r a u c hra hchange]
    rw [if_pos (affected_proposal_location hra hchange)]
    have hbound := profileProposal_W_pure_le P F X u c
    rw [flipSet_eq_of_changes_root hra hchange] at hbound
    exact hbound
  · rw [profileProposal_delete_eq_of_root_ne P F X r a u c hchange]
    rw [FinDist.W_self ham_nonneg ham_self]
    by_cases hloc : u ∈ flipSet F.graph X r a ∧ c = (if X u = X r then a else X r)
    · rw [if_pos hloc]
      exact P.nonneg _ (flipSet_card_pos (G := F.graph) (X := X) (u := r) (c := a))
    · rw [if_neg hloc]

/-- **Hard one-deletion bound** of `lem:boundary-sensitivity`: for any bound
`R ≥ s ρ_s` (`s ≥ 1`), deleting one colour `a` from the list at `r` moves each
row of `Φ^ρ_F` by at most `R/(m q)`, from every colouring avoiding `a` at `r`
(in particular, every colouring feasible for the smaller list). -/
theorem flipKernel_deleteListColour_W_le [Nonempty V] [Nonempty C] {R : ℝ}
    (hR : ∀ s : ℕ, 1 ≤ s → (s : ℝ) * P.ρ s ≤ R)
    (F : HardListInstance V C) (X : V → C) (r : V) (a : C) (hra : X r ≠ a) :
    FinDist.W ham (flipKernel P F X) (flipKernel P (deleteListColour F r a) X) ≤
      R / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) := by
  rw [flipKernel_of_nonempty, flipKernel_of_nonempty]
  unfold profileStep
  apply (FinDist.W_bind_diag ham_nonneg (FinDist.uniform (V × C)) _ _).trans
  let S := flipSet F.graph X r a
  let k : ℝ := (Fintype.card (V × C) : ℝ)⁻¹
  have hk : 0 ≤ k := by dsimp [k]; positivity
  calc
    _ ≤ ∑ p : V × C, k * (if p.1 ∈ S ∧ p.2 = (if X p.1 = X r then a else X r)
        then P.ρ S.card else 0) := by
      apply Finset.sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_left
        (profileProposal_delete_W_bound P F X r a hra p.1 p.2) hk
    _ = (S.card : ℝ) * (k * P.ρ S.card) := by
      simp_rw [mul_ite, mul_zero]
      exact sum_affected_proposals S (fun u => if X u = X r then a else X r) _
    _ = k * ((S.card : ℝ) * P.ρ S.card) := by ring
    _ ≤ k * R := mul_le_mul_of_nonneg_left
        (hR S.card (flipSet_card_pos (G := F.graph) (X := X) (u := r) (c := a))) hk
    _ = R / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) := by
      simp [k, Fintype.card_prod, Nat.cast_mul, div_eq_inv_mul]

/-- Delete every colour `c` with `(u,c) ∈ D` from the list at `u`. -/
def deleteListColours (F : HardListInstance V C) (D : Finset (V × C)) :
    HardListInstance V C where
  graph := F.graph
  list u := (F.list u).filter fun c => (u, c) ∉ D

lemma deleteListColours_empty (F : HardListInstance V C) : deleteListColours F ∅ = F := by
  cases F
  simp [deleteListColours]

lemma deleteListColours_insert (F : HardListInstance V C) (D : Finset (V × C))
    (p : V × C) :
    deleteListColours F (insert p D) = deleteListColour (deleteListColours F D) p.1 p.2 := by
  unfold deleteListColours deleteListColour
  simp only
  congr 1
  funext u
  ext c
  by_cases hu : u = p.1
  · subst hu
    simp only [if_true, Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨hc, hn⟩
      exact ⟨fun h => hn (Or.inl (by rw [h])), hc, fun h => hn (Or.inr h)⟩
    · rintro ⟨hca, hc, hn⟩
      refine ⟨hc, ?_⟩
      rintro (h | h)
      · exact hca (congrArg Prod.snd h)
      · exact hn h
  · simp only [if_neg hu, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hc, hn⟩
      exact ⟨hc, fun h => hn (Or.inr h)⟩
    · rintro ⟨hc, hn⟩
      refine ⟨hc, ?_⟩
      rintro (h | h)
      · exact hu (congrArg Prod.fst h)
      · exact hn h

/-- **Hard `k`-deletion bound**: deleting the `k = |D|` colours `D` from the
lists moves each row by at most `k R/(m q)`, from every colouring avoiding all
deleted colours. -/
theorem flipKernel_deleteListColours_W_le [Nonempty V] [Nonempty C] {R : ℝ}
    (hR : ∀ s : ℕ, 1 ≤ s → (s : ℝ) * P.ρ s ≤ R)
    (F : HardListInstance V C) (D : Finset (V × C)) (X : V → C)
    (hX : ∀ p ∈ D, X p.1 ≠ p.2) :
    FinDist.W ham (flipKernel P F X) (flipKernel P (deleteListColours F D) X) ≤
      D.card * (R / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ))) := by
  induction D using Finset.induction_on with
  | empty =>
      rw [deleteListColours_empty, FinDist.W_self ham_nonneg ham_self]
      simp
  | @insert p D hp ih =>
      rw [deleteListColours_insert, Finset.card_insert_of_notMem hp]
      have h1 := ih (fun q hq => hX q (Finset.mem_insert_of_mem hq))
      have h2 := flipKernel_deleteListColour_W_le P hR (deleteListColours F D) X p.1 p.2
        (hX p (Finset.mem_insert_self p D))
      calc _ ≤ FinDist.W ham (flipKernel P F X) (flipKernel P (deleteListColours F D) X) +
            FinDist.W ham (flipKernel P (deleteListColours F D) X)
              (flipKernel P (deleteListColour (deleteListColours F D) p.1 p.2) X) :=
            FinDist.W_triangle ham_nonneg ham_nonneg ham_nonneg ham_triangle _ _ _
        _ ≤ _ := add_le_add h1 h2
        _ = _ := by push_cast; ring

/-- **Hard `k`-deletion bound, list form.**  If `F'` has the same graph and
smaller lists, with `k = ∑_u |L_u \ L'_u|` deleted colours, then from every
colouring `X` whose colours surviving in `F` also survive in `F'` (in particular
every `X` feasible for the smaller lists) the rows differ by at most
`k R/(m q)`. -/
theorem flipKernel_sublists_W_le [Nonempty V] [Nonempty C] {R : ℝ}
    (hR : ∀ s : ℕ, 1 ≤ s → (s : ℝ) * P.ρ s ≤ R)
    (F F' : HardListInstance V C) (hgraph : F'.graph = F.graph)
    (hsub : ∀ u, F'.list u ⊆ F.list u) (X : V → C)
    (hX : ∀ u, X u ∈ F.list u → X u ∈ F'.list u) :
    FinDist.W ham (flipKernel P F X) (flipKernel P F' X) ≤
      (∑ u, ((F.list u \ F'.list u).card : ℝ)) *
        (R / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ))) := by
  let D : Finset (V × C) := Finset.univ.filter fun p => p.2 ∈ F.list p.1 \ F'.list p.1
  have hF' : deleteListColours F D = F' := by
    cases F'
    simp only at hgraph hsub
    unfold deleteListColours
    congr 1
    · exact hgraph.symm
    · funext u
      ext c
      simp only [Finset.mem_filter, D, Finset.mem_univ, true_and, Finset.mem_sdiff, not_and,
        not_not]
      constructor
      · rintro ⟨hc, h⟩
        exact h hc
      · intro hc
        exact ⟨hsub u hc, fun _ => hc⟩
  have hcard : (D.card : ℝ) = ∑ u, ((F.list u \ F'.list u).card : ℝ) := by
    have : D.card = ∑ u, (F.list u \ F'.list u).card := by
      rw [Finset.card_filter, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.card_filter]
      congr 1
      ext c
      simp
    exact_mod_cast this
  have hXD : ∀ p ∈ D, X p.1 ≠ p.2 := by
    intro p hp h
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff] at hp
    rw [← h] at hp
    exact hp.2 (hX p.1 hp.1)
  rw [← hcard, ← hF']
  exact flipKernel_deleteListColours_W_le P hR F D X hXD

/-- The hard `k`-deletion bound with the paper's constant `R_ρ`, on colourings
feasible for the smaller lists. -/
theorem flipKernel_sublists_W_le_R [Nonempty V] [Nonempty C] (hP : P.RFinite)
    (F F' : HardListInstance V C) (hgraph : F'.graph = F.graph)
    (hsub : ∀ u, F'.list u ⊆ F.list u) (X : V → C) (hX : F'.IsProper X) :
    FinDist.W ham (flipKernel P F X) (flipKernel P F' X) ≤
      (∑ u, ((F.list u \ F'.list u).card : ℝ)) *
        (P.R / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ))) :=
  flipKernel_sublists_W_le P (P.mul_le_R hP) F F' hgraph hsub X (fun u _ => hX.2 u)

/-- The hard one-deletion bound with the paper's constant `R_ρ`. -/
theorem flipKernel_deleteListColour_W_le_R [Nonempty V] [Nonempty C] (hP : P.RFinite)
    (F : HardListInstance V C) (X : V → C) (r : V) (a : C)
    (hX : (deleteListColour F r a).IsProper X) :
    FinDist.W ham (flipKernel P F X) (flipKernel P (deleteListColour F r a) X) ≤
      P.R / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) :=
  flipKernel_deleteListColour_W_le P (P.mul_le_R hP) F X r a
    ((deleteListColour_proper_iff F r a X).mp hX).2

end HardDeletion

/-! ## `lem:boundary-sensitivity`: soft kernels -/

section SoftBoundary

variable [Nonempty V] [Nonempty C] (P : FlipProfile)

lemma activated_flip_addBoundary_W_le {R : ℝ} (hR : ∀ s : ℕ, 1 ≤ s → (s : ℝ) * P.ρ s ≤ R)
    (I : PinningData V C) (r : V) (a : C) (X : V → C)
    (ω : (addBoundary I r a).Constraint → Bool) :
    W ham
      (flipKernel P (activeHardListInstance I (activatedSet I X
        (fun k => ω (boundaryConstraintEmbedding I r a k)))) X)
      (flipKernel P (activeHardListInstance (addBoundary I r a)
        (activatedSet (addBoundary I r a) X ω)) X) ≤
      if ω (freshBoundaryConstraint I r a) = true then
        R / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) else 0 := by
  have hR0 : 0 ≤ R := by
    have h1 := hR 1 le_rfl
    have h2 := P.nonneg 1 le_rfl
    simp only [Nat.cast_one, one_mul] at h1
    linarith
  rw [activeHardListInstance_addBoundary]
  by_cases h : ω (freshBoundaryConstraint I r a) = true ∧ X r ≠ a
  · rw [if_pos h, if_pos h.1]
    exact flipKernel_deleteListColour_W_le P hR _ X r a h.2
  · rw [if_neg h, W_self ham_nonneg ham_self]
    by_cases hf : ω (freshBoundaryConstraint I r a) = true
    · rw [if_pos hf]
      positivity
    · rw [if_neg hf]

/-- **`lem:boundary-sensitivity`, eq. `(eq:one-boundary-row)`, with any bound
`R ≥ s ρ_s`.**  Adding one labelled free–pinned edge changes each soft row by at
most `(1-x) R/(m q)`, for every profile and every `x ∈ (0,1]`. -/
theorem softFlipKernel_addBoundary_W_le {R : ℝ}
    (hR : ∀ s : ℕ, 1 ≤ s → (s : ℝ) * P.ρ s ≤ R)
    (I : PinningData V C) (r : V) (a : C) (X : V → C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    W ham (softFlipKernel P I x hx0 hx1 X)
      (softFlipKernel P (addBoundary I r a) x hx0 hx1 X) ≤
        (1 - x) * R / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) := by
  let ht := coinParam hx0 hx1
  let p := commonCoinLaw (K := (addBoundary I r a).Constraint) (1 - x) ht
  let restrict := fun (ω : (addBoundary I r a).Constraint → Bool) (k : I.Constraint) =>
    ω (boundaryConstraintEmbedding I r a k)
  have hold : (commonCoinLaw (K := I.Constraint) (1 - x) ht).bind
      (fun ω => flipKernel P (activeHardListInstance I (activatedSet I X ω)) X) =
      p.bind (fun ω => flipKernel P
        (activeHardListInstance I (activatedSet I X (restrict ω))) X) := by
    rw [← map_commonCoinLaw_embedding (boundaryConstraintEmbedding I r a) (1 - x) ht]
    exact mapLaw_bind _ _ _
  rw [softFlipKernel_eq_coin_mixture, softFlipKernel_eq_coin_mixture]
  change W ham ((commonCoinLaw (K := I.Constraint) (1 - x) ht).bind _) (p.bind _) ≤ _
  rw [hold]
  apply (W_bind_diag ham_nonneg p _ _).trans
  calc
    _ ≤ ∑ ω, p.w ω * (if ω (freshBoundaryConstraint I r a) = true then
          R / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) else 0) := by
      apply Finset.sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left
        (activated_flip_addBoundary_W_le P hR I r a X ω) (p.nonneg ω)
    _ = (1 - x) * R / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) := by
      have h := expectReal_product_coordinate
        (fun _ : (addBoundary I r a).Constraint => bernoulliLaw (1 - x) ht)
        (freshBoundaryConstraint I r a)
        (fun b : Bool => if b = true then
          R / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) else 0)
      simp only [expectReal, bernoulliLaw] at h
      change ∑ ω, p.w ω * _ = _ at h
      rw [h]
      simp [mul_div_assoc]

/-- **`lem:boundary-sensitivity`, eq. `(eq:one-boundary-row)`**, with the
paper's constant `R_ρ = sup_{s ≥ 1} s ρ_s < ∞`. -/
theorem softFlipKernel_addBoundary_W_le_R (hP : P.RFinite)
    (I : PinningData V C) (r : V) (a : C) (X : V → C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    W ham (softFlipKernel P I x hx0 hx1 X)
      (softFlipKernel P (addBoundary I r a) x hx0 hx1 X) ≤
        (1 - x) * P.R / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) :=
  softFlipKernel_addBoundary_W_le P (P.mul_le_R hP) I r a X x hx0 hx1

lemma pinningData_ext {I J : PinningData V C} (hgraph : I.graph = J.graph)
    (hcount : I.boundaryCount = J.boundaryCount) : I = J := by
  cases I
  cases J
  simp only at hgraph hcount
  subst hgraph hcount
  rfl

/-- Number of labelled free–pinned edges of `J` in excess of those of `I`. -/
def boundaryExcess (I J : PinningData V C) : ℕ :=
  ∑ u, ∑ c, (J.boundaryCount u c - I.boundaryCount u c)

lemma pinningData_eq_of_excess_zero (I J : PinningData V C) (hgraph : J.graph = I.graph)
    (hle : ∀ u c, I.boundaryCount u c ≤ J.boundaryCount u c)
    (h0 : boundaryExcess I J = 0) : J = I := by
  have hpt : ∀ u c, J.boundaryCount u c = I.boundaryCount u c := by
    intro u c
    have hu := (Finset.sum_eq_zero_iff.mp h0) u (Finset.mem_univ u)
    have huc := (Finset.sum_eq_zero_iff.mp hu) c (Finset.mem_univ c)
    have := hle u c
    omega
  cases I
  cases J
  simp only at hgraph hpt
  subst hgraph
  congr
  funext u c
  exact hpt u c

/-- **`lem:boundary-sensitivity`, `k`-fold soft bound.**  If the plus system has
the same free graph and `k = boundaryExcess I J` additional labelled free–pinned
edges (arbitrary vertices with repetition, arbitrary colours), each soft row
moves by at most `k (1-x) R/(m q)`. -/
theorem softFlipKernel_addBoundaries_W_le {R : ℝ}
    (hR : ∀ s : ℕ, 1 ≤ s → (s : ℝ) * P.ρ s ≤ R)
    (I J : PinningData V C) (hgraph : J.graph = I.graph)
    (hle : ∀ u c, I.boundaryCount u c ≤ J.boundaryCount u c) (X : V → C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    W ham (softFlipKernel P I x hx0 hx1 X) (softFlipKernel P J x hx0 hx1 X) ≤
      boundaryExcess I J *
        ((1 - x) * R / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ))) := by
  set B := (1 - x) * R / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ))
  suffices H : ∀ k : ℕ, ∀ J : PinningData V C, J.graph = I.graph →
      (∀ u c, I.boundaryCount u c ≤ J.boundaryCount u c) → boundaryExcess I J = k →
      W ham (softFlipKernel P I x hx0 hx1 X) (softFlipKernel P J x hx0 hx1 X) ≤ k * B from
    H _ J hgraph hle rfl
  intro k
  induction k with
  | zero =>
      intro J hg hl h0
      rw [pinningData_eq_of_excess_zero I J hg hl h0, W_self ham_nonneg ham_self]
      simp
  | succ k ih =>
      intro J hg hl hk
      obtain ⟨u, c, huc⟩ : ∃ u c, I.boundaryCount u c < J.boundaryCount u c := by
        by_contra hne
        push Not at hne
        have : boundaryExcess I J = 0 := by
          refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun c _ => ?_
          have := hne u c
          omega
        omega
      let J' : PinningData V C :=
        { graph := J.graph
          boundaryCount := fun v b => J.boundaryCount v b - if v = u ∧ b = c then 1 else 0 }
      have hJ : J = addBoundary J' u c := by
        refine pinningData_ext (J := addBoundary J' u c) rfl ?_
        funext v b
        change J.boundaryCount v b =
          (J.boundaryCount v b - if v = u ∧ b = c then 1 else 0) +
            if v = u ∧ b = c then 1 else 0
        by_cases hvb : v = u ∧ b = c
        · obtain ⟨rfl, rfl⟩ := hvb
          simp only [and_self, if_true]
          omega
        · simp [hvb]
      have hg' : J'.graph = I.graph := hg
      have hl' : ∀ v b, I.boundaryCount v b ≤ J'.boundaryCount v b := by
        intro v b
        simp only [J']
        by_cases hvb : v = u ∧ b = c
        · obtain ⟨rfl, rfl⟩ := hvb
          simp only [and_self, if_true]
          omega
        · simp only [hvb, if_false, Nat.sub_zero]
          exact hl v b
      have hk' : boundaryExcess I J' = k := by
        have hpt : ∀ v b, J.boundaryCount v b - I.boundaryCount v b =
            (J'.boundaryCount v b - I.boundaryCount v b) + if v = u ∧ b = c then 1 else 0 := by
          intro v b
          simp only [J']
          by_cases hvb : v = u ∧ b = c
          · obtain ⟨rfl, rfl⟩ := hvb
            simp only [and_self, if_true]
            omega
          · simp [hvb]
        have hsum : boundaryExcess I J = boundaryExcess I J' + 1 := by
          unfold boundaryExcess
          simp_rw [hpt, Finset.sum_add_distrib]
          congr 1
          rw [Finset.sum_eq_single u]
          · simp
          · intro v _ hv
            simp [hv]
          · simp
        omega
      have h1 := ih J' hg' hl' hk'
      have h2 := softFlipKernel_addBoundary_W_le P hR J' u c X x hx0 hx1
      rw [hJ]
      calc _ ≤ W ham (softFlipKernel P I x hx0 hx1 X) (softFlipKernel P J' x hx0 hx1 X) +
            W ham (softFlipKernel P J' x hx0 hx1 X)
              (softFlipKernel P (addBoundary J' u c) x hx0 hx1 X) :=
            W_triangle ham_nonneg ham_nonneg ham_nonneg ham_triangle _ _ _
        _ ≤ k * B + B := add_le_add h1 h2
        _ = ((k + 1 : ℕ) : ℝ) * B := by push_cast; ring

/-- The `k`-fold soft bound with the paper's constant `R_ρ`. -/
theorem softFlipKernel_addBoundaries_W_le_R (hP : P.RFinite)
    (I J : PinningData V C) (hgraph : J.graph = I.graph)
    (hle : ∀ u c, I.boundaryCount u c ≤ J.boundaryCount u c) (X : V → C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    W ham (softFlipKernel P I x hx0 hx1 X) (softFlipKernel P J x hx0 hx1 X) ≤
      boundaryExcess I J *
        ((1 - x) * P.R / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ))) :=
  softFlipKernel_addBoundaries_W_le P (P.mul_le_R hP) I J hgraph hle X x hx0 hx1

/-- **`lem:boundary-sensitivity`, the paper's statement, collected.**  For a
profile with `R_ρ < ∞` and `x ∈ (0,1]`: the one-edge soft bound, the hard
one-deletion bound on colourings feasible for the smaller list, and their
`k`-fold versions (`k` labelled free–pinned edges; `k` deleted colours). -/
theorem lem_boundary_sensitivity (hP : P.RFinite) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    (∀ (I : PinningData V C) (r : V) (a : C) (σ : V → C),
      W ham (softFlipKernel P I x hx0 hx1 σ) (softFlipKernel P (addBoundary I r a) x hx0 hx1 σ) ≤
        (1 - x) * P.R / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ))) ∧
    (∀ (F : HardListInstance V C) (r : V) (a : C) (X : V → C),
      (deleteListColour F r a).IsProper X →
      W ham (flipKernel P F X) (flipKernel P (deleteListColour F r a) X) ≤
        P.R / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ))) ∧
    (∀ (I J : PinningData V C), J.graph = I.graph →
      (∀ u c, I.boundaryCount u c ≤ J.boundaryCount u c) → ∀ σ : V → C,
      W ham (softFlipKernel P I x hx0 hx1 σ) (softFlipKernel P J x hx0 hx1 σ) ≤
        boundaryExcess I J *
          ((1 - x) * P.R / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)))) ∧
    (∀ (F F' : HardListInstance V C), F'.graph = F.graph → (∀ u, F'.list u ⊆ F.list u) →
      ∀ X : V → C, F'.IsProper X →
      W ham (flipKernel P F X) (flipKernel P F' X) ≤
        (∑ u, ((F.list u \ F'.list u).card : ℝ)) *
          (P.R / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)))) :=
  ⟨fun I r a σ => softFlipKernel_addBoundary_W_le_R P hP I r a σ x hx0 hx1,
   fun F r a X hX => flipKernel_deleteListColour_W_le_R P hP F X r a hX,
   fun I J hg hl σ => softFlipKernel_addBoundaries_W_le_R P hP I J hg hl σ x hx0 hx1,
   fun F F' hg hs X hX => flipKernel_sublists_W_le_R P hP F F' hg hs X hX⟩

end SoftBoundary

/-! ## Optimal couplings exist on finite spaces -/

/-- On finite spaces the infimum defining `W` is attained. -/
theorem exists_coupling_cost_eq_W {S T : Type*} [Fintype S] [Fintype T]
    {d : S → T → ℝ} (hd : ∀ x y, 0 ≤ d x y) (μ : FinDist S) (ν : FinDist T) :
    ∃ γ : Coupling μ ν, γ.cost d = W d μ ν := by
  let K : Set (S → T → ℝ) := {w | (∀ x y, 0 ≤ w x y) ∧
    (∀ x, ∑ y, w x y = μ.w x) ∧ (∀ y, ∑ x, w x y = ν.w y)}
  have hclosed : IsClosed K := by
    have h1 : IsClosed {w : S → T → ℝ | ∀ x y, 0 ≤ w x y} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun x => isClosed_iInter fun y =>
        isClosed_le continuous_const ((continuous_apply y).comp (continuous_apply x))
    have h2 : IsClosed {w : S → T → ℝ | ∀ x, ∑ y, w x y = μ.w x} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun x => isClosed_eq
        (continuous_finsetSum _ fun y _ => (continuous_apply y).comp (continuous_apply x))
        continuous_const
    have h3 : IsClosed {w : S → T → ℝ | ∀ y, ∑ x, w x y = ν.w y} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun y => isClosed_eq
        (continuous_finsetSum _ fun x _ => (continuous_apply y).comp (continuous_apply x))
        continuous_const
    exact h1.inter (h2.inter h3)
  have hbox : K ⊆ Set.univ.pi fun _ : S => Set.univ.pi fun _ : T => Set.Icc (0 : ℝ) 1 := by
    rintro w ⟨h0, hrow, _⟩ x - y -
    refine ⟨h0 x y, ?_⟩
    calc w x y ≤ ∑ y', w x y' := Finset.single_le_sum (fun y' _ => h0 x y') (Finset.mem_univ y)
      _ = μ.w x := hrow x
      _ ≤ 1 := μ.le_one x
  have hcompact : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset
      hclosed hbox
  have hne : K.Nonempty := ⟨(Coupling.prod μ ν).w,
    (Coupling.prod μ ν).nonneg, (Coupling.prod μ ν).sum_row, (Coupling.prod μ ν).sum_col⟩
  have hcont : Continuous fun w : S → T → ℝ => ∑ x, ∑ y, w x y * d x y := by
    fun_prop
  obtain ⟨w0, hw0, hmin⟩ := hcompact.exists_isMinOn hne hcont.continuousOn
  let γ0 : Coupling μ ν := ⟨w0, hw0.1, hw0.2.1, hw0.2.2⟩
  refine ⟨γ0, le_antisymm ?_ (W_le_cost hd γ0)⟩
  apply le_W
  intro γ
  exact hmin ⟨γ.nonneg, γ.sum_row, γ.sum_col⟩

/-! ## `lem:soft-contraction` for the Vigoda profile, `x ∈ (0,1]` -/

section Contraction

variable [Nonempty V] [Nonempty C]

/-- `softK_x^{G,τ} = K_{x,p}^{G,τ}`, for every `x ∈ (0,1]`. -/
abbrev softVigoda (I : PinningData V C) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    (V → C) → FinDist (V → C) :=
  softFlipKernel vigodaProfile I x hx0 hx1

theorem softVigoda_W_le_average_le (I : PinningData V C) (X Y : V → C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    W ham (softVigoda I x hx0 hx1 X) (softVigoda I x hx0 hx1 Y) ≤
      expectReal (commonCoinLaw (K := I.Constraint) (1 - x) (coinParam hx0 hx1))
        (fun ω => W ham (hardStep (activeHardListInstance I (activatedSet I X ω)) X)
          (hardStep (activeHardListInstance I (activatedSet I Y ω)) Y)) := by
  rw [softVigoda, softFlipKernel_eq_coin_mixture, softFlipKernel_eq_coin_mixture]
  simp only [flipKernel_of_nonempty, profileStep_vigoda]
  exact W_bind_diag ham_nonneg _ _ _

/-- **`lem:soft-contraction`, adjacent bound, Wasserstein form**, for every
pinned system with constraint degree at most `Δ` and every `x ∈ (0,1]`: for
adjacent `X, Y`, `W(K X, K Y) ≤ 1 - (q - (11/6) t Δ)/(n q)`.  No hypothesis on
the hard coupling remains; it is supplied by `conditionalHardCouplingEstimate`. -/
theorem softVigoda_adjacent_W_le (I : PinningData V C) {Δ : ℕ} (hdegree : I.DegreeBound Δ)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) (X Y : V → C) (hXY : hamCard X Y = 1) :
    W ham (softVigoda I x hx0 hx1 X) (softVigoda I x hx0 hx1 Y) ≤
      1 - ((Fintype.card C : ℝ) - (11 / 6 : ℝ) * (1 - x) * Δ) /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  obtain ⟨v, hv, hoff⟩ := exists_unique_disagreement hXY
  have hconditional := conditionalHardCouplingEstimate I X Y v hv hoff
  let ht := coinParam hx0 hx1
  let p := commonCoinLaw (K := I.Constraint) (1 - x) ht
  let w (ω : I.Constraint → Bool) := W ham
    (hardStep (activeHardListInstance I (activatedSet I X ω)) X)
    (hardStep (activeHardListInstance I (activatedSet I Y ω)) Y)
  have havg := expectReal_mono p hconditional
  change expectReal p (fun ω => ((Fintype.card V : ℝ) * Fintype.card C) * (w ω - 1)) ≤ _
    at havg
  rw [expectReal_mul_const, expectReal_sub, expectReal_const,
    expectReal_sub, expectReal_mul_const] at havg
  have hf : expectReal p (rootFreeCoinCount I v) = I.graph.degree v * (1 - x) :=
    expected_rootFreeCoinCount I v (1 - x) ht
  rw [hf] at havg
  have hl : (Fintype.card C : ℝ) - (∑ c, (I.boundaryCount v c : ℝ)) * (1 - x) ≤
      expectReal p (rootCommonListCount I X Y v) :=
    expected_rootCommonListCount_lower I X Y v (1 - x) ht
  have hd : (I.graph.degree v : ℝ) + (∑ c, (I.boundaryCount v c : ℝ)) ≤ Δ := by
    exact_mod_cast hdegree v
  have hb : 0 ≤ ∑ c, (I.boundaryCount v c : ℝ) := by positivity
  have ht0 : 0 ≤ 1 - x := ht.1
  have hsum : (I.graph.degree v : ℝ) * (1 - x) +
      (∑ c, (I.boundaryCount v c : ℝ)) * (1 - x) ≤ (Δ : ℝ) * (1 - x) := by
    nlinarith [mul_le_mul_of_nonneg_right hd ht0]
  have hnq : 0 < (Fintype.card V : ℝ) * (Fintype.card C : ℝ) := by
    exact mul_pos (by exact_mod_cast Fintype.card_pos (α := V))
      (by exact_mod_cast Fintype.card_pos (α := C))
  have htarget : expectReal p w ≤
      1 - ((Fintype.card C : ℝ) - (11 / 6 : ℝ) * (1 - x) * Δ) /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
    have hcancel : ((Fintype.card V : ℝ) * Fintype.card C) *
        (1 - ((Fintype.card C : ℝ) - (11 / 6 : ℝ) * (1 - x) * Δ) /
          ((Fintype.card V : ℝ) * Fintype.card C)) =
        ((Fintype.card V : ℝ) * Fintype.card C) -
          ((Fintype.card C : ℝ) - (11 / 6 : ℝ) * (1 - x) * Δ) := by
      field_simp
    nlinarith [mul_nonneg hb ht0]
  exact (softVigoda_W_le_average_le I X Y x hx0 hx1).trans htarget

/-- **`lem:soft-contraction`, eq. `(eq:soft-averaged-drift)`.**  For every
pinned system of constraint degree at most `Δ`, `x ∈ (0,1]`, `t = 1-x`,
`n = |V^τ| ≥ 1`, adjacent colourings `X, Y` have a coupling `(X', Y')` of one
step of `softK_x` with `n q (E Ham(X',Y') - 1) ≤ (11/6) t Δ - q`. -/
theorem softVigoda_adjacent_coupling (I : PinningData V C) {Δ : ℕ}
    (hdegree : I.DegreeBound Δ) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (X Y : V → C) (hXY : hamCard X Y = 1) :
    ∃ γ : Coupling (softVigoda I x hx0 hx1 X) (softVigoda I x hx0 hx1 Y),
      ((Fintype.card V : ℝ) * Fintype.card C) * (γ.cost ham - 1) ≤
        (11 / 6 : ℝ) * (1 - x) * Δ - Fintype.card C := by
  obtain ⟨γ, hγ⟩ := exists_coupling_cost_eq_W ham_nonneg
    (softVigoda I x hx0 hx1 X) (softVigoda I x hx0 hx1 Y)
  refine ⟨γ, ?_⟩
  have hW := softVigoda_adjacent_W_le I hdegree x hx0 hx1 X Y hXY
  rw [← hγ] at hW
  have hnq : 0 < (Fintype.card V : ℝ) * (Fintype.card C : ℝ) := by
    exact mul_pos (by exact_mod_cast Fintype.card_pos (α := V))
      (by exact_mod_cast Fintype.card_pos (α := C))
  have h := mul_le_mul_of_nonneg_left (sub_le_sub_right hW 1) hnq.le
  have hcalc : ((Fintype.card V : ℝ) * Fintype.card C) *
      (1 - ((Fintype.card C : ℝ) - (11 / 6 : ℝ) * (1 - x) * Δ) /
        ((Fintype.card V : ℝ) * Fintype.card C) - 1) =
      (11 / 6 : ℝ) * (1 - x) * Δ - Fintype.card C := by
    field_simp
    ring
  linarith

/-- The contraction rate `κ_x = (q - (11/6) t Δ)/q` of `eq:soft-kappa`. -/
def kappa (q Δ x : ℝ) : ℝ := (q - (11 / 6 : ℝ) * (1 - x) * Δ) / q

/-- **`lem:soft-contraction`, all pairs.**  If `q > (11/6) t Δ`, then
`κ_x > 0` and, by path coupling, `W(K X, K Y) ≤ (1 - κ_x/n) Ham(X,Y)` for all
colourings; the same factor contracts `W` between arbitrary initial laws. -/
theorem softVigoda_contraction (I : PinningData V C) {Δ : ℕ} (hdegree : I.DegreeBound Δ)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hq : (11 / 6 : ℝ) * (1 - x) * Δ < Fintype.card C) :
    0 < kappa (Fintype.card C) Δ x ∧
    (∀ X Y : V → C, W ham (softVigoda I x hx0 hx1 X) (softVigoda I x hx0 hx1 Y) ≤
      (1 - kappa (Fintype.card C) Δ x / Fintype.card V) * ham X Y) ∧
    (∀ α β : FinDist (V → C),
      W ham (α.bind (softVigoda I x hx0 hx1)) (β.bind (softVigoda I x hx0 hx1)) ≤
        (1 - kappa (Fintype.card C) Δ x / Fintype.card V) * W ham α β) := by
  have hC : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos (α := C)
  have hV : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have hrate : 1 - kappa (Fintype.card C) Δ x / Fintype.card V =
      1 - ((Fintype.card C : ℝ) - (11 / 6 : ℝ) * (1 - x) * Δ) /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
    unfold kappa
    field_simp
  have hadj : ∀ X Y : V → C, hamCard X Y = 1 →
      W ham (softVigoda I x hx0 hx1 X) (softVigoda I x hx0 hx1 Y) ≤
        1 - kappa (Fintype.card C) Δ x / Fintype.card V := by
    intro X Y hXY
    rw [hrate]
    exact softVigoda_adjacent_W_le I hdegree x hx0 hx1 X Y hXY
  have hκ1 : kappa (Fintype.card C) Δ x ≤ 1 := by
    unfold kappa
    rw [div_le_one hC]
    have : 0 ≤ (11 / 6 : ℝ) * (1 - x) * Δ := by
      have : 0 ≤ 1 - x := by linarith
      positivity
    linarith
  have hc0 : 0 ≤ 1 - kappa (Fintype.card C) Δ x / Fintype.card V := by
    have h1 : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
    have : kappa (Fintype.card C) Δ x / Fintype.card V ≤ 1 := by
      rw [div_le_one hV]
      linarith
    linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold kappa
    exact div_pos (by linarith) hC
  · intro X Y
    classical
    have h := W_ham_le_of_adjacent (softVigoda I x hx0 hx1) hadj X Y
    simpa [ham] using h
  · intro α β
    classical
    exact W_ham_bind_contract (softVigoda I x hx0 hx1) hc0 hadj α β

/-- **`lem:soft-contraction`, the paper's statement, collected**: the adjacent
coupling with `(eq:soft-averaged-drift)`, and, if `q > (11/6) t Δ`, contraction of
Hamming distance by `1 - κ_x/n` with `κ_x > 0`. -/
theorem lem_soft_contraction (I : PinningData V C) {Δ : ℕ} (hdegree : I.DegreeBound Δ)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    (∀ X Y : V → C, hamCard X Y = 1 →
      ∃ γ : Coupling (softVigoda I x hx0 hx1 X) (softVigoda I x hx0 hx1 Y),
        ((Fintype.card V : ℝ) * Fintype.card C) * (γ.cost ham - 1) ≤
          (11 / 6 : ℝ) * (1 - x) * Δ - Fintype.card C) ∧
    ((11 / 6 : ℝ) * (1 - x) * Δ < Fintype.card C →
      0 < kappa (Fintype.card C) Δ x ∧
      ∀ X Y : V → C, W ham (softVigoda I x hx0 hx1 X) (softVigoda I x hx0 hx1 Y) ≤
        (1 - kappa (Fintype.card C) Δ x / Fintype.card V) * ham X Y) :=
  ⟨fun X Y hXY => softVigoda_adjacent_coupling I hdegree x hx0 hx1 X Y hXY,
   fun hq => ⟨(softVigoda_contraction I hdegree x hx0 hx1 hq).1,
     (softVigoda_contraction I hdegree x hx0 hx1 hq).2.1⟩⟩

/-- On `0 < x < 1` the kernel above is the library's `softVigodaKernel`. -/
theorem softVigoda_eq_library (I : PinningData V C) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    softVigoda I x hx0 hx1.le = softVigodaKernel I x hx0 hx1 :=
  softFlipKernel_vigoda I x hx0 hx1

end Contraction

/-! ## Corollaries at the use sites -/

section Corollaries

/- As in `RootBoundary.lean`: make every `DecidableEq` instance the classical
one, so that the Fintype instance on colourings of `RootRemaining` agrees with
the one used at the definition sites. -/
local instance (priority := 2000) softFlipKernelDecEq (α : Type*) : DecidableEq α :=
  Classical.decEq α

theorem vigodaProfile_rho_one : vigodaProfile.ρ 1 = 1 := rfl

theorem cvProfile_rho_one : cvProfile.ρ 1 = 1 := rfl

/-- The library's Vigoda soft kernel (`0 < x < 1`, any vertex set) is
reversible and irreducible. -/
theorem softVigodaKernelWithEmpty_reversible_irreducible [Nonempty C]
    (I : PinningData V C) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    IsReversible (softVigodaKernelWithEmpty I x hx0 hx1)
        (I.gibbs x hx0.le (I.partition_pos_of_parameter_pos hx0)) ∧
      IsIrreducible (softVigodaKernelWithEmpty I x hx0 hx1) := by
  rw [← softFlipKernel_vigoda_withEmpty I x hx0 hx1]
  exact ⟨softFlipKernel_reversible _ _ _ _ _,
    softFlipKernel_irreducible _ _ (by rw [vigodaProfile_rho_one]; norm_num) _ _ _⟩

/-- The library's CV soft kernel (`0 < x < 1`) is reversible and irreducible,
as asserted in the companion's CV appendix. -/
theorem softCVKernel_reversible_irreducible [Nonempty V] [Nonempty C]
    (I : PinningData V C) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    IsReversible (CI2ZF.Appendix.CV.softCVKernel I x hx0 hx1)
        (I.gibbs x hx0.le (I.partition_pos_of_parameter_pos hx0)) ∧
      IsIrreducible (CI2ZF.Appendix.CV.softCVKernel I x hx0 hx1) := by
  rw [← softFlipKernel_cv I x hx0 hx1]
  exact ⟨softFlipKernel_reversible _ _ _ _ _,
    softFlipKernel_irreducible _ _ (by rw [cvProfile_rho_one]; norm_num) _ _ _⟩

lemma boundaryExcess_addBoundarySet (I : PinningData V C) (S : Finset V) (a : C) :
    boundaryExcess I (addBoundarySet I S a) = S.card := by
  unfold boundaryExcess
  have h : ∀ u, (∑ c, ((addBoundarySet I S a).boundaryCount u c - I.boundaryCount u c)) =
      if u ∈ S then 1 else 0 := by
    intro u
    simp only [addBoundarySet, Nat.add_sub_cancel_left]
    by_cases hu : u ∈ S <;> simp [hu]
  simp_rw [h]
  rw [Finset.sum_boole]
  simp

/-- The child-to-middle row bound `(eq:soft-child-middle-row)` for an arbitrary
profile with `s ρ_s ≤ R` and every `x ∈ (0,1]`: the child adds at most `Δ`
labelled free–pinned edges. -/
theorem rootChild_softFlip_boundary_W_le [Nonempty C] (P : FlipProfile) {R : ℝ}
    (hR : ∀ s : ℕ, 1 ≤ s → (s : ℝ) * P.ρ s ≤ R)
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex)
    [Nonempty (RootRemaining tau r)] (a : C) {Δ : ℕ}
    (hdegree : ∀ v, G.degree v ≤ Δ) (X : RootRemaining tau r → C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    W ham (softFlipKernel P (rootChildData tau G r a) x hx0 hx1 X)
      (softFlipKernel P (rootMiddleData tau G r) x hx0 hx1 X) ≤
        (1 - x) * R * Δ / ((Fintype.card (RootRemaining tau r) : ℝ) * Fintype.card C) := by
  have hR0 : 0 ≤ R := by
    have h1 := hR 1 le_rfl
    have h2 := P.nonneg 1 le_rfl
    simp only [Nat.cast_one, one_mul] at h1
    linarith
  have hmain := softFlipKernel_addBoundaries_W_le P hR (rootMiddleData tau G r)
    (addBoundarySet (rootMiddleData tau G r) (rootBoundaryVertices tau G r) a) rfl
    (fun v b => Nat.le_add_right _ _) X x hx0 hx1
  rw [rootChildData_eq_addBoundarySet, W_ham_comm]
  refine hmain.trans ?_
  rw [boundaryExcess_addBoundarySet]
  have hS : ((rootBoundaryVertices tau G r).card : ℝ) ≤ Δ := by
    exact_mod_cast rootBoundaryVertices_card_le tau G r hdegree
  have hB : 0 ≤ (1 - x) * R /
      ((Fintype.card (RootRemaining tau r) : ℝ) * Fintype.card C) := by
    have : 0 ≤ 1 - x := by linarith
    positivity
  calc ((rootBoundaryVertices tau G r).card : ℝ) *
        ((1 - x) * R / ((Fintype.card (RootRemaining tau r) : ℝ) * Fintype.card C)) ≤
      Δ * ((1 - x) * R / ((Fintype.card (RootRemaining tau r) : ℝ) * Fintype.card C)) :=
        mul_le_mul_of_nonneg_right hS hB
    _ = _ := by ring

/-- `(eq:soft-child-middle-row)` for the Vigoda profile, now for all `x ∈ (0,1]`. -/
theorem rootChild_softVigoda_boundary_W_le [Nonempty C]
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex)
    [Nonempty (RootRemaining tau r)] (a : C) {Δ : ℕ}
    (hdegree : ∀ v, G.degree v ≤ Δ) (X : RootRemaining tau r → C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    W ham (softFlipKernel vigodaProfile (rootChildData tau G r a) x hx0 hx1 X)
      (softFlipKernel vigodaProfile (rootMiddleData tau G r) x hx0 hx1 X) ≤
        (1 - x) * Δ / ((Fintype.card (RootRemaining tau r) : ℝ) * Fintype.card C) := by
  have h := rootChild_softFlip_boundary_W_le vigodaProfile
    (fun (s : ℕ) _ => vigoda_branch_bound s) tau G r a hdegree X x hx0 hx1
  simpa using h

/-- The CV child-to-middle row bound of the companion, for all `x ∈ (0,1]`. -/
theorem rootChild_softCV_boundary_W_le [Nonempty C]
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex)
    [Nonempty (RootRemaining tau r)] (a : C) {Δ : ℕ}
    (hdegree : ∀ v, G.degree v ≤ Δ) (X : RootRemaining tau r → C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    W ham (softFlipKernel cvProfile (rootChildData tau G r a) x hx0 hx1 X)
      (softFlipKernel cvProfile (rootMiddleData tau G r) x hx0 hx1 X) ≤
        (1 - x) * Δ / ((Fintype.card (RootRemaining tau r) : ℝ) * Fintype.card C) := by
  have h := rootChild_softFlip_boundary_W_le cvProfile
    (fun (s : ℕ) _ => CI2ZF.Appendix.CV.size_mass_le_one s) tau G r a hdegree X x hx0 hx1
  simpa using h

end Corollaries

end

end CI2ZF.Potts
