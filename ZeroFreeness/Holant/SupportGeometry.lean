import ZeroFreeness.Coupling.Foundations.HammingResponses
import Mathlib.Data.List.Chain

/-!
# Geodesics in downward-closed Boolean supports

Removing selected coordinates preserves feasibility. To move between two
feasible assignments, remove differing selected coordinates first, and only
then add coordinates belonging to the target. This gives a Hamming geodesic
entirely inside the feasible support, so one-coordinate response estimates
imply the full Lipschitz estimate on that support.
-/

namespace ZeroFreeness.Holant
open Finset PottsCI
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- A Boolean support is closed under deleting selected coordinates. -/
def BooleanDownwardClosed (S : Set (E → Bool)) : Prop :=
  ∀ ⦃σ τ⦄, σ ∈ S → (∀ e, τ e = true → σ e = true) → τ ∈ S

/-- Updating a differing coordinate to its target value is one exact step
of a Hamming geodesic. -/
theorem hamCard_update_toward {σ τ : E → Bool} {e : E} (he : σ e ≠ τ e) :
    hamCard σ (Function.update σ e (τ e)) = 1 ∧
      hamCard (Function.update σ e (τ e)) τ + 1 = hamCard σ τ := by
  constructor
  · have hs : (univ.filter fun v => σ v ≠ Function.update σ e (τ e) v) = {e} := by
      ext v
      by_cases hv : v = e
      · subst v
        simp [he]
      · simp [hv]
    simp only [hamCard, hs, card_singleton]
  · have hs : (univ.filter fun v => Function.update σ e (τ e) v ≠ τ v) =
        (univ.filter fun v => σ v ≠ τ v).erase e := by
      ext v
      by_cases hv : v = e
      · subst v
        simp
      · simp [hv]
    have hm : e ∈ univ.filter fun v => σ v ≠ τ v := by simp [he]
    simp only [hamCard, hs, card_erase_of_mem hm]
    have := card_pos.mpr ⟨e, hm⟩
    omega

/-- Every nontrivial pair has a feasible neighbor one unit closer to the
target. The argument chooses a deletion whenever a deletion is available. -/
theorem exists_feasible_intermediate {S : Set (E → Bool)} (hS : BooleanDownwardClosed S)
    {σ τ : E → Bool} (hσ : σ ∈ S) (hτ : τ ∈ S) {k : ℕ}
    (hd : hamCard σ τ = k + 1) :
    ∃ ζ ∈ S, hamCard σ ζ = 1 ∧ hamCard ζ τ = k := by
  have hchoice : ∃ e, σ e ≠ τ e ∧ Function.update σ e (τ e) ∈ S := by
    by_cases hremove : ∃ e, σ e = true ∧ τ e = false
    · obtain ⟨e, heσ, heτ⟩ := hremove
      refine ⟨e, by simp [heσ, heτ], hS hσ ?_⟩
      intro v hv
      by_cases hve : v = e
      · subst v
        simp [heτ] at hv
      · simpa [hve] using hv
    · have hne : (univ.filter fun e => σ e ≠ τ e).Nonempty := by
        rw [← card_pos, ← hamCard, hd]
        omega
      obtain ⟨e, he⟩ := hne
      have he' : σ e ≠ τ e := (mem_filter.mp he).2
      refine ⟨e, he', hS hτ ?_⟩
      intro v hv
      by_cases hve : v = e
      · subst v
        simpa using hv
      · have hvσ : σ v = true := by simpa [hve] using hv
        cases hvτ : τ v with
        | false => exact (hremove ⟨v, hvσ, hvτ⟩).elim
        | true => rfl
  obtain ⟨e, he, hf⟩ := hchoice
  obtain ⟨hfirst, hrest⟩ := hamCard_update_toward he
  exact ⟨Function.update σ e (τ e), hf, hfirst, by omega⟩

/-- An explicit feasible path uses exactly the Hamming number of edges.
The list following `σ` has one entry for each single-coordinate change. -/
theorem exists_feasible_hamming_path {S : Set (E → Bool)} (hS : BooleanDownwardClosed S)
    {σ τ : E → Bool} (hσ : σ ∈ S) (hτ : τ ∈ S) :
    ∃ path : List (E → Bool),
      (σ :: path).IsChain (fun x y => hamCard x y = 1) ∧
      (σ :: path).getLast? = some τ ∧ path.length = hamCard σ τ ∧
      ∀ ζ ∈ σ :: path, ζ ∈ S := by
  have main : ∀ k : ℕ, ∀ σ τ : E → Bool, σ ∈ S → τ ∈ S → hamCard σ τ = k →
      ∃ path : List (E → Bool),
        (σ :: path).IsChain (fun x y => hamCard x y = 1) ∧
        (σ :: path).getLast? = some τ ∧ path.length = k ∧
        ∀ ζ ∈ σ :: path, ζ ∈ S := by
    intro k
    induction k with
    | zero =>
      intro σ τ hσ _ hd
      have heq := hamCard_eq_zero hd
      subst τ
      exact ⟨[], List.isChain_singleton _, by simp, rfl, by simpa using hσ⟩
    | succ k ih =>
      intro σ τ hσ hτ hd
      obtain ⟨ζ, hζ, hfirst, hrest⟩ := exists_feasible_intermediate hS hσ hτ hd
      obtain ⟨path, hchain, hlast, hlength, hfeas⟩ := ih ζ τ hζ hτ hrest
      refine ⟨ζ :: path, ?_, ?_, by simp [hlength], ?_⟩
      · exact hchain.cons (by simpa using hfirst)
      · simpa using hlast
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hσ
        · exact hfeas w hw
  exact main (hamCard σ τ) σ τ hσ hτ rfl

/-- Single-coordinate bounds extend to the full feasible domain, without
assuming that an arbitrary update preserves feasibility. -/
theorem norm_sub_le_ham_on_downward_support {S : Set (E → Bool)}
    (hS : BooleanDownwardClosed S) {X : Type*} [SeminormedAddCommGroup X]
    (f : S → X) {α : ℝ}
    (hstep : ∀ σ τ : S, hamCard σ.val τ.val = 1 → ‖f σ - f τ‖ ≤ α)
    (σ τ : S) : ‖f σ - f τ‖ ≤ α * ham σ.val τ.val := by
  have main : ∀ k : ℕ, ∀ σ τ : S, hamCard σ.val τ.val = k →
      ‖f σ - f τ‖ ≤ α * k := by
    intro k
    induction k with
    | zero =>
      intro σ τ hd
      have heq : σ = τ := Subtype.ext (hamCard_eq_zero hd)
      simp [heq]
    | succ k ih =>
      intro σ τ hd
      obtain ⟨ζ, hζ, hfirst, hrest⟩ := exists_feasible_intermediate hS σ.property τ.property hd
      let ζ' : S := ⟨ζ, hζ⟩
      calc
        ‖f σ - f τ‖ = ‖(f σ - f ζ') + (f ζ' - f τ)‖ := by
          congr 1
          abel
        _ ≤ ‖f σ - f ζ'‖ + ‖f ζ' - f τ‖ := norm_add_le _ _
        _ ≤ α + α * k := add_le_add (hstep σ ζ' hfirst) (ih ζ' τ hrest)
        _ = α * (k + 1 : ℕ) := by push_cast; ring
  exact main (hamCard σ.val τ.val) σ τ rfl

/-- The same local response estimate also bounds the oscillation by the
number of shell coordinates, as required for the complex-average lemma. -/
theorem norm_sub_le_card_on_downward_support {S : Set (E → Bool)}
    (hS : BooleanDownwardClosed S) {X : Type*} [SeminormedAddCommGroup X]
    (f : S → X) {α : ℝ} (hα : 0 ≤ α)
    (hstep : ∀ σ τ : S, hamCard σ.val τ.val = 1 → ‖f σ - f τ‖ ≤ α)
    (σ τ : S) : ‖f σ - f τ‖ ≤ α * Fintype.card E :=
  (norm_sub_le_ham_on_downward_support hS f hstep σ τ).trans
    (mul_le_mul_of_nonneg_left (ham_le_card σ.val τ.val) hα)

end
end ZeroFreeness.Holant
