import CI2ZF.BFSShells
import CI2ZF.ShellMarginals

/-! The shell-sum and low-cost-shell inequalities for the actual BFS spheres,
with laws on configurations of the sphere vertex subtype. -/
namespace CI2ZF.BFS
open Finset PottsCI PottsCI.FinDist
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

def restrictSphere (G : SimpleGraph V) (v : V) (r : ℕ) (σ : V → C) :
    {w : V // w ∈ shell G v r} → C := fun w => σ w.val

def sphereMarginal (μ : FinDist (V → C)) (G : SimpleGraph V) (v : V) (r : ℕ) :
    FinDist ({w : V // w ∈ shell G v r} → C) :=
  mapLaw μ (restrictSphere G v r)

omit [DecidableEq V] [Fintype C] in
lemma ham_restrictSphere (G : SimpleGraph V) (v : V) (offset R : ℕ) (i : Fin R)
    (σ τ : V → C) :
    ham (restrictSphere G v (offset + i.val + 1) σ)
      (restrictSphere G v (offset + i.val + 1) τ) =
      shellHam (shellLabelFrom G v offset R) i σ τ := by
  classical
  unfold ham hamCard
  rw [natCast_card_filter]
  change (∑ w : {w : V // w ∈ shell G v (offset + i.val + 1)},
    if σ w.val ≠ τ w.val then (1 : ℝ) else 0) = _
  trans ∑ w ∈ shell G v (offset + i.val + 1), if σ w ≠ τ w then (1 : ℝ) else 0
  · exact (sum_subtype (p := fun w : V => w ∈ shell G v (offset + i.val + 1))
      (shell G v (offset + i.val + 1)) (fun _ => Iff.rfl)
      (fun w : V => if σ w ≠ τ w then (1 : ℝ) else 0)).symm
  unfold shell shellHam
  rw [sum_filter]
  apply sum_congr rfl
  intro w _
  simp only [shellLabelFrom_eq_some_iff, mem_shell]
  by_cases h : σ w = τ w <;> simp [h]

theorem W_sphereMarginal_le (μ ν : FinDist (V → C)) (G : SimpleGraph V)
    (v : V) (offset R : ℕ) (i : Fin R) :
    W ham (sphereMarginal μ G v (offset + i.val + 1))
      (sphereMarginal ν G v (offset + i.val + 1)) ≤
      W (shellHam (shellLabelFrom G v offset R) i) μ ν := by
  calc
    _ ≤ W (fun σ τ => ham (restrictSphere G v (offset + i.val + 1) σ)
        (restrictSphere G v (offset + i.val + 1) τ)) μ ν :=
      W_mapLaw_le _ _ ham ham_nonneg
    _ = _ := by
      congr 1
      funext σ τ
      exact ham_restrictSphere G v offset R i σ τ

/-- The exact sphere marginals at any consecutive block of radii satisfy
one common full-configuration transportation budget. -/
theorem sum_W_sphereMarginal_le (μ ν : FinDist (V → C)) (G : SimpleGraph V)
    (v : V) (offset R : ℕ) :
    (∑ i : Fin R, W ham (sphereMarginal μ G v (offset + i.val + 1))
      (sphereMarginal ν G v (offset + i.val + 1))) ≤ W ham μ ν := by
  calc
    _ ≤ ∑ i : Fin R, W (shellHam (shellLabelFrom G v offset R) i) μ ν :=
      sum_le_sum fun i _ => W_sphereMarginal_le μ ν G v offset R i
    _ ≤ _ := sum_W_le_W (shellHam (shellLabelFrom G v offset R)) ham
      (shellHam_nonneg _) (sum_shellHam_le_ham _)

/-- The paper's low-cost shell lies at a genuine radius between `2` and
`R + 1`, inclusive. -/
theorem exists_low_W_sphereMarginal (μ ν : FinDist (V → C)) (G : SimpleGraph V)
    (v : V) {R : ℕ} (hR : 0 < R) {B : ℝ} (hCI : W ham μ ν ≤ B) :
    ∃ r : ℕ, 2 ≤ r ∧ r ≤ R + 1 ∧
      W ham (sphereMarginal μ G v r) (sphereMarginal ν G v r) ≤ B / R := by
  have : Nonempty (Fin R) := ⟨⟨0, hR⟩⟩
  obtain ⟨i, hi⟩ := exists_low_hamming_shell μ ν (shellLabelFrom G v 1 R) hCI
  refine ⟨1 + i.val + 1, by omega, by omega, ?_⟩
  exact (W_sphereMarginal_le μ ν G v 1 R i).trans (by simpa using hi)

end
end CI2ZF.BFS
