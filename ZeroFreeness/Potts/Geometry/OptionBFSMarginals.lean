import ZeroFreeness.Potts.Geometry.GenericGibbsRelabel
import ZeroFreeness.Potts.Geometry.OptionBFSSplit
import ZeroFreeness.Potts.Geometry.OptionShellMarginals
import ZeroFreeness.Coupling.Foundations.FinDistEnumeration

/-! The actual shell Gibbs law of a root-deleted, three-part child is
the sphere marginal in the original parent graph. Concrete Potts CI
therefore supplies a low-cost separator shell, including at zero. -/
namespace ZeroFreeness.Potts.OptionBFS
open PottsCI PottsCI.FinDist Separator
attribute [local instance] Classical.propDecidable
noncomputable section
variable {O C : Type*} [Fintype O] [Fintype C]
local instance (priority := 2000) optionBFSMarginalInsideFintype
    (G : SimpleGraph (Option O)) (k : ℕ) : Fintype (Inside G k) :=
  @Subtype.fintype O (fun o => some o ∈ BFS.ball G none k)
    (fun o => @Finset.decidableMem (Option O) (Classical.decEq _) (some o) (BFS.ball G none k))
    inferInstance
local instance (priority := 2000) optionBFSMarginalOutsideFintype
    (G : SimpleGraph (Option O)) (k : ℕ) : Fintype (BFS.Outside G none k) :=
  @Subtype.fintype (Option O) (fun w => w ∉ BFS.ball G none (k + 1))
    (fun w => @instDecidableNot (w ∈ BFS.ball G none (k + 1))
      (@Finset.decidableMem (Option O) (Classical.decEq _) w (BFS.ball G none (k + 1))))
    inferInstance
local instance (priority := 2000) optionBFSMarginalInsideEq (G : SimpleGraph (Option O)) (k : ℕ) :
    DecidableEq (Inside G k) := Classical.decEq _
local instance (priority := 2000) optionBFSMarginalShellEq (G : SimpleGraph (Option O)) (k : ℕ) :
    DecidableEq (BFS.Shell G none k) := Classical.decEq _
local instance (priority := 2000) optionBFSMarginalOutsideEq (G : SimpleGraph (Option O)) (k : ℕ) :
    DecidableEq (BFS.Outside G none k) := Classical.decEq _

/-- Root padding is arbitrary because a sphere of radius `k + 1` omits
the root. The two children may therefore use the same padding colour. -/
theorem childSplit_shellMarginal_eq_sphere
    (I : PinningData (Option O) C) (a padding : C) (k : ℕ)
    (x : ℝ) (hx : 0 ≤ x)
    (hZ : 0 < (optionChildData I a).partition x)
    (hZ' : 0 < (childSplit I a k).partition x) :
    Separator.shellMarginal (childSplit I a k) x hx hZ' =
      reenumerate (BFS.sphereMarginal
        (paddedRootLaw ((optionChildData I a).gibbs x hx hZ) padding)
        I.graph none (k + 1)) := by
  unfold childSplit at hZ' ⊢
  rw [shellMarginal_relabel (optionChildData I a) (childEquiv I.graph k) x hx hZ hZ']
  unfold BFS.sphereMarginal paddedRootLaw
  rw [reenumerate_mapLaw, mapLaw_comp]
  congr 1
  funext σ s
  change σ ((childEquiv I.graph k).symm (Sum.inr (Sum.inl s))) = padRoot padding σ s.val
  rw [← some_childEquiv_symm_shell I.graph k s]
  rfl

/-- The same actual separator law, using only positivity of the specified
child. In particular it does not impose an extra colour of slack. -/
def childGibbsShellLaw (I : PinningData (Option O) C) (a : C) (k : ℕ)
    (x : ℝ) (hx : 0 ≤ x) (hZ : 0 < (optionChildData I a).partition x) :
    FinDist (BFS.Shell I.graph none k → C) :=
  Separator.shellMarginal (childSplit I a k) x hx
    (partition_relabel_pos (optionChildData I a) (childEquiv I.graph k) x hZ)

theorem childGibbsShellLaw_eq_sphere
    (I : PinningData (Option O) C) (a padding : C) (k : ℕ)
    (x : ℝ) (hx : 0 ≤ x) (hZ : 0 < (optionChildData I a).partition x) :
    childGibbsShellLaw I a k x hx hZ =
      reenumerate (BFS.sphereMarginal
        (paddedRootLaw ((optionChildData I a).gibbs x hx hZ) padding)
        I.graph none (k + 1)) :=
  childSplit_shellMarginal_eq_sphere I a padding k x hx hZ _

/-- A bound on the two actual child Gibbs laws gives a low-cost actual
separator marginal, under arbitrary valid positivity proofs. -/
theorem exists_low_childGibbsShellLaw_of_ci
    (I : PinningData (Option O) C) (a b : C) (x : ℝ) (hx : 0 ≤ x)
    (hZa : 0 < (optionChildData I a).partition x)
    (hZb : 0 < (optionChildData I b).partition x)
    {R : ℕ} (hR : 0 < R) {B : ℝ}
    (hCI : W ham ((optionChildData I a).gibbs x hx hZa)
      ((optionChildData I b).gibbs x hx hZb) ≤ B) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ R ∧
      W ham (childGibbsShellLaw I a k x hx hZa)
        (childGibbsShellLaw I b k x hx hZb) ≤ B / R := by
  obtain ⟨r, hr2, hrR, hr⟩ := exists_low_root_sphere I _ _ a hR hCI
  cases r with
  | zero => omega
  | succ k =>
    refine ⟨k, by omega, by omega, ?_⟩
    rw [childGibbsShellLaw_eq_sphere I a a, childGibbsShellLaw_eq_sphere I b a, W_reenumerate]
    exact hr

/-- A notation for the genuine separator marginal, with positivity
derived from the original data's degree and number of colours. -/
def childShellLaw [Nonempty C] (I : PinningData (Option O) C) (a : C) (k : ℕ)
    {Δ : ℕ} (hdegree : I.DegreeBound Δ) (hcolours : Δ + 2 ≤ Fintype.card C)
    (x : PinningData.NonnegativeParameter) : FinDist (BFS.Shell I.graph none k → C) :=
  Separator.shellMarginal (childSplit I a k) x x.property
    (partition_relabel_pos (optionChildData I a) (childEquiv I.graph k) x
      ((optionChildData I a).partition_pos x.property
        (optionChildData_degreeBound I hdegree a) hcolours))

theorem childShellLaw_eq_sphere [Nonempty C]
    (I : PinningData (Option O) C) (a padding : C) (k : ℕ)
    {Δ : ℕ} (hdegree : I.DegreeBound Δ) (hcolours : Δ + 2 ≤ Fintype.card C)
    (x : PinningData.NonnegativeParameter) :
    childShellLaw I a k hdegree hcolours x =
      reenumerate (BFS.sphereMarginal
        (paddedRootLaw ((optionChildData I a).nonnegativeGibbs
          (optionChildData_degreeBound I hdegree a) hcolours x) padding)
        I.graph none (k + 1)) :=
  childSplit_shellMarginal_eq_sphere I a padding k x x.property _ _

/-- The shell has the separator's own probability law; the only premise
here is a bound for the two actual normalized children on the original
root-deleted configuration space. -/
theorem exists_low_childShellLaw_of_ci [Nonempty C]
    (I : PinningData (Option O) C) (a b : C)
    {Δ : ℕ} (hdegree : I.DegreeBound Δ) (hcolours : Δ + 2 ≤ Fintype.card C)
    (x : PinningData.NonnegativeParameter) {R : ℕ} (hR : 0 < R) {B : ℝ}
    (hCI : W ham
      ((optionChildData I a).nonnegativeGibbs (optionChildData_degreeBound I hdegree a) hcolours x)
      ((optionChildData I b).nonnegativeGibbs (optionChildData_degreeBound I hdegree b) hcolours x)
        ≤ B) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ R ∧
      W ham (childShellLaw I a k hdegree hcolours x)
        (childShellLaw I b k hdegree hcolours x) ≤ B / R := by
  obtain ⟨r, hr2, hrR, hr⟩ := exists_low_root_sphere I _ _ a hR hCI
  cases r with
  | zero => omega
  | succ k =>
    refine ⟨k, by omega, by omega, ?_⟩
    rw [childShellLaw_eq_sphere I a a, childShellLaw_eq_sphere I b a, W_reenumerate]
    exact hr

/-- The strict-line low-cost shell follows entirely from concrete Potts
CI and remains valid at both endpoints of the physical interval. -/
theorem strict_exists_low_childShellLaw [Nonempty C]
    (I : PinningData (Option O) C) {Δ : ℕ} (hΔ : 2 ≤ Δ) (hdegree : I.DegreeBound Δ)
    (hq : (11 / 6 : ℝ) * Δ < Fintype.card C) (a b : C)
    (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1)
    {R : ℕ} (hR : 0 < R) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ R ∧
      W ham (childShellLaw I a k hdegree (colours_slack_of_vigoda_line hΔ hq.le) x)
        (childShellLaw I b k hdegree (colours_slack_of_vigoda_line hΔ hq.le) x) ≤
          (2 / ciGap (Fintype.card C) Δ) / R :=
  exists_low_childShellLaw_of_ci I a b hdegree _ x hR
    (option_root_strict_uniform_ci I hΔ hdegree hq a b x hx1)

/-- On the critical line, the same genuine shell bound holds uniformly
on every closed interval bounded away from zero. -/
theorem critical_exists_low_childShellLaw [Nonempty C]
    (I : PinningData (Option O) C) {Δ : ℕ} (hΔ : 2 ≤ Δ) (hdegree : I.DegreeBound Δ)
    (hq : (Fintype.card C : ℝ) = (11 / 6 : ℝ) * Δ) (a b : C)
    {δ : ℝ} (hδ : 0 < δ) (x : PinningData.NonnegativeParameter)
    (hx : (x : ℝ) ∈ Set.Icc δ 1) {R : ℕ} (hR : 0 < R) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ R ∧
      W ham (childShellLaw I a k hdegree (colours_slack_of_vigoda_line hΔ hq.ge) x)
        (childShellLaw I b k hdegree (colours_slack_of_vigoda_line hΔ hq.ge) x) ≤
          (12 / (11 * δ)) / R :=
  exists_low_childShellLaw_of_ci I a b hdegree _ x hR
    (option_root_critical_uniform_ci I hΔ hdegree hq a b hδ x hx)

end
end ZeroFreeness.Potts.OptionBFS
