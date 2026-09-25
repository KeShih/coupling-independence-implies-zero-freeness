import ZeroFreeness.Holant.ShellSelection

/-! Select a sphere for the pulled-back subset-Hamming transportation cost;
this form feeds directly into the typed feasible-shell marginal comparison. -/
namespace ZeroFreeness.Holant
open Finset PottsCI PottsCI.FinDist HolantCoupling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]

theorem exists_low_ambient_shell_cost (H : NormalizedInstance V E) (Γ : SimpleGraph E)
    (e : E) (μ ν : FinDist (Finset E)) {L : ℕ} (hL : 0 < L) {C : ℝ}
    (hCI : W subsetHam μ ν ≤ C) :
    ∃ r : ℕ, r < L ∧
      W (fun A B => subsetHam (A ∩ ambientShell H Γ e r)
        (B ∩ ambientShell H Γ e r)) μ ν ≤ C / L := by
  have : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  let shells : Fin L → Finset E := fun i => ambientShell H Γ e i.val
  have hdisj : ∀ i j, i ≠ j → Disjoint (shells i) (shells j) := by
    intro i j hij
    exact ambient_shells_disjoint H Γ e (by intro h; exact hij (Fin.ext h))
  obtain ⟨i, hi⟩ := ZeroFreeness.exists_low_W_shell
    (μ := μ) (ν := ν) (fun i A B => subsetHam (A ∩ shells i) (B ∩ shells i)) subsetHam
    (fun _ _ _ => subsetHam_nonneg _ _) (sum_subsetHam_inter_le shells hdisj) hCI
  exact ⟨i.val, i.isLt, by simpa using hi⟩

end
end ZeroFreeness.Holant
