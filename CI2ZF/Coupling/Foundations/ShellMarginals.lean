import CI2ZF.Coupling.Foundations.FiniteCoupling

/-!
# Hamming transport on actual shell marginals

A shell label assigns each vertex to at most one shell. Restricting a full
configuration gives an actual configuration on the shell vertex subtype.
The induced marginal distributions satisfy the shell-sum transportation bound
used in the Potts zero-free argument.
-/

namespace CI2ZF

open scoped BigOperators
open PottsCI PottsCI.FinDist

noncomputable section

variable {V C ι : Type*} [Fintype V] [DecidableEq C] [DecidableEq ι]

/-- Vertices of a shell, represented as a subtype of the original vertex set. -/
abbrev ShellVertex (shellOf : V → Option ι) (i : ι) :=
  {v : V // shellOf v = some i}

/-- Restrict a full configuration to one shell. -/
def restrictToShell (shellOf : V → Option ι) (i : ι) (σ : V → C) :
    ShellVertex shellOf i → C := fun v => σ v.1

/-- Hamming distance after restriction is exactly the shell cost on the
original configuration space. -/
theorem ham_restrictToShell (shellOf : V → Option ι) (i : ι) (σ τ : V → C) :
    PottsCI.ham (restrictToShell shellOf i σ) (restrictToShell shellOf i τ) =
      shellHam shellOf i σ τ := by
  classical
  unfold PottsCI.ham PottsCI.hamCard
  rw [Finset.natCast_card_filter]
  change (∑ v : ShellVertex shellOf i, if σ v.1 ≠ τ v.1 then (1 : ℝ) else 0) = _
  have hsub := Finset.sum_subtype (p := fun v : V => shellOf v = some i) (F := inferInstance)
    (Finset.univ.filter fun v => shellOf v = some i)
    (fun v => by simp) (fun v : V => if σ v ≠ τ v then (1 : ℝ) else 0)
  rw [← hsub, Finset.sum_filter]
  unfold shellHam
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : σ v = τ v <;> simp [h]

variable [Fintype C] [DecidableEq V]

/-- The actual marginal law on configurations of one shell. -/
def shellMarginal (μ : FinDist (V → C)) (shellOf : V → Option ι) (i : ι) :
    FinDist (ShellVertex shellOf i → C) :=
  mapLaw μ (restrictToShell shellOf i)

/-- The transport distance between shell marginals is bounded by the
transport cost of the same shell coordinates on the full space. -/
theorem W_shellMarginal_le (μ ν : FinDist (V → C))
    (shellOf : V → Option ι) (i : ι) :
    W PottsCI.ham (shellMarginal μ shellOf i) (shellMarginal ν shellOf i) ≤
      W (shellHam shellOf i) μ ν := by
  calc
    W PottsCI.ham (shellMarginal μ shellOf i) (shellMarginal ν shellOf i) ≤
        W (fun σ τ => PottsCI.ham (restrictToShell shellOf i σ)
          (restrictToShell shellOf i τ)) μ ν :=
      W_mapLaw_le (restrictToShell shellOf i) (restrictToShell shellOf i)
        PottsCI.ham PottsCI.ham_nonneg
    _ = W (shellHam shellOf i) μ ν := by
      congr 1
      funext σ τ
      exact ham_restrictToShell shellOf i σ τ

variable [Fintype ι]

/-- The shell-sum inequality for actual marginal laws. The common full-space
coupling controls all disjoint shells before taking infima. -/
theorem sum_W_shellMarginal_le (μ ν : FinDist (V → C))
    (shellOf : V → Option ι) :
    (∑ i, W PottsCI.ham (shellMarginal μ shellOf i) (shellMarginal ν shellOf i)) ≤
      W PottsCI.ham μ ν := by
  calc
    (∑ i, W PottsCI.ham (shellMarginal μ shellOf i) (shellMarginal ν shellOf i)) ≤
        ∑ i, W (shellHam shellOf i) μ ν :=
      Finset.sum_le_sum fun i _ => W_shellMarginal_le μ ν shellOf i
    _ ≤ W PottsCI.ham μ ν :=
      sum_W_le_W (shellHam shellOf) PottsCI.ham
        (shellHam_nonneg shellOf) (sum_shellHam_le_ham shellOf)

/-- Coupling independence selects an actual shell marginal with Hamming
transport distance at most the CI budget divided by the number of shells. -/
theorem exists_low_W_shellMarginal [Nonempty ι]
    (μ ν : FinDist (V → C)) (shellOf : V → Option ι) {B : ℝ}
    (hCI : W PottsCI.ham μ ν ≤ B) :
    ∃ i, W PottsCI.ham (shellMarginal μ shellOf i) (shellMarginal ν shellOf i) ≤
      B / Fintype.card ι := by
  obtain ⟨i, hi⟩ := exists_low_hamming_shell μ ν shellOf hCI
  exact ⟨i, (W_shellMarginal_le μ ν shellOf i).trans hi⟩

end

end CI2ZF
