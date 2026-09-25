import ZeroFreeness.LeeYang.Model

/-! Field coordinates follow actual vertices through every restriction.
The analytic proof uses one complex parameter along an arbitrary bounded
field direction, with the all-one field at parameter zero. -/
namespace ZeroFreeness.LeeYang
noncomputable section
set_option linter.unusedSectionVars false
variable {V W T C : Type*}

def fieldPull (e : W → V) (ℓ : V → C → ℂ) : W → C → ℂ :=
  fun w c => ℓ (e w) c

def fieldLine (d : V → C → ℂ) (z : ℂ) : V → C → ℂ :=
  fun v c => 1 + z * d v c

def DirectionBound (d : V → C → ℂ) : Prop := ∀ v c, ‖d v c‖ ≤ 1

@[simp] theorem fieldPull_apply (e : W → V) (ℓ : V → C → ℂ) (w : W) (c : C) :
    fieldPull e ℓ w c = ℓ (e w) c := rfl

@[simp] theorem fieldLine_apply (d : V → C → ℂ) (z : ℂ) (v : V) (c : C) :
    fieldLine d z v c = 1 + z * d v c := rfl

@[simp] theorem fieldPull_id (ℓ : V → C → ℂ) : fieldPull id ℓ = ℓ := rfl

@[simp] theorem fieldPull_comp (e : W → V) (f : T → W) (ℓ : V → C → ℂ) :
    fieldPull f (fieldPull e ℓ) = fieldPull (e ∘ f) ℓ := rfl

@[simp] theorem fieldPull_oneField (e : W → V) :
    fieldPull e (oneField : V → C → ℂ) = oneField := rfl

@[simp] theorem fieldPull_fieldLine (e : W → V) (d : V → C → ℂ) (z : ℂ) :
    fieldPull e (fieldLine d z) = fieldLine (fieldPull e d) z := rfl

@[simp] theorem fieldLine_zero (d : V → C → ℂ) : fieldLine d 0 = oneField := by
  funext v c
  simp [fieldLine, oneField]

theorem DirectionBound.pull {d : V → C → ℂ} (hd : DirectionBound d) (e : W → V) :
    DirectionBound (fieldPull e d) := fun w c => hd (e w) c

theorem fieldLine_dist_one_le {d : V → C → ℂ} (hd : DirectionBound d)
    (z : ℂ) (v : V) (c : C) : ‖fieldLine d z v c - 1‖ ≤ ‖z‖ := by
  simp only [fieldLine, add_sub_cancel_left, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg z) (hd v c)

end
end ZeroFreeness.LeeYang
