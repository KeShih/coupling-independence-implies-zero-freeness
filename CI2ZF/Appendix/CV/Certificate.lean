import CI2ZF.Appendix.CV.Arithmetic

/-! Kernel-checked finite certificate for the low-multiplicity CV record.
The 21 branch states encode exactly the allowed size/availability/feasibility
patterns, including the repeated-component marker and the zero-rate tail.
The numerical proof uses `decide`, not native evaluation or external certificates. -/
namespace CI2ZF.Appendix.CV

/-- The CV mass in integer units of one thousandth. -/
def scaledMass : ℕ → ℤ
  | 1 => 1000
  | 2 => 324
  | 3 => 154
  | 4 => 88
  | 5 => 44
  | 6 => 11
  | _ => 0

lemma scaledMass_eq (r : ℕ) : (scaledMass r : ℝ) = 1000 * mass r := by
  by_cases h : r ≤ 6
  · interval_cases r <;> norm_num [scaledMass, mass]
  · have hr : 7 ≤ r := by omega
    rw [mass_zero_of_seven_le r hr]
    match r with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
    | _ + 7 => simp [scaledMass]

abbrev Branch := Fin 21

def branchSize (b : Branch) : ℕ :=
  if b.val = 0 then 0 else if b.val ≤ 2 then 1 else 2 + (b.val - 3) / 3

def available (b : Branch) : Bool :=
  if b.val = 0 then false else if b.val ≤ 2 then b.val == 2 else (b.val - 3) % 3 != 0

def feasible (b : Branch) : Bool :=
  if b.val = 0 then false else if b.val ≤ 2 then b.val == 2 else (b.val - 3) % 3 == 2

def atomMass (b : Branch) : ℤ := if feasible b then scaledMass (branchSize b) else 0

def rootOK (b : Branch) : Bool := branchSize b == 0 || feasible b

def safe11 (a b : Branch) : ℕ :=
  if branchSize a == 1 && branchSize b == 1 && available a && available b then 1 else 0

def safe12 (a b : Branch) : ℕ :=
  if ((branchSize a == 1 && branchSize b == 2) ||
      (branchSize a == 2 && branchSize b == 1)) && available a && available b then 1 else 0

lemma branch_state_restrictions (b : Branch) :
    branchSize b ≤ 7 ∧
    (feasible b = true → available b = true) ∧
    (branchSize b = 0 → feasible b = false ∧ available b = false) ∧
    (branchSize b = 1 → feasible b = available b) := by
  revert b; decide

set_option maxRecDepth 100000 in
/-- Every allowed truncated size/availability/feasibility record is encoded. -/
lemma branch_encoding_complete (s : Fin 8) (a f : Bool)
    (hf : f = true → a = true)
    (hzero : s.val = 0 → a = false ∧ f = false)
    (hone : s.val = 1 → f = a) :
    ∃ b : Branch, branchSize b = s.val ∧ available b = a ∧ feasible b = f := by
  revert s a f hf hzero hone
  decide +kernel

lemma safe_count_budget (a b : Branch) : safe11 a b + safe12 a b ≤ 1 := by
  revert a b; decide

def oneCharge (a b : Branch) : ℤ :=
  let ar := atomMass a - if feasible a then scaledMass (1 + branchSize a) else 0
  let br := atomMass b - if feasible b then scaledMass (1 + branchSize b) else 0
  branchSize a * ar + branchSize b * br - min ar br

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- All 400 positive one-incidence records at the balancing point. -/
theorem one_certificate (a b : Branch) (ha : branchSize a > 0) (hb : branchSize b > 0) :
    oneCharge a b + 132 * (safe11 a b : ℤ) - 38 * (safe12 a b : ℤ) ≤ 808 := by
  revert a b ha hb
  decide +kernel

/-- A largest-component choice is synchronized whenever maxima intersect. -/
def permitted (a₀ a₁ b₀ b₁ : Branch) (i j : Bool) : Bool :=
  let amax := if i then branchSize a₀ ≤ branchSize a₁ else branchSize a₁ ≤ branchSize a₀
  let bmax := if j then branchSize b₀ ≤ branchSize b₁ else branchSize b₁ ≤ branchSize b₀
  let common := (branchSize a₁ ≤ branchSize a₀ && branchSize b₁ ≤ branchSize b₀) ||
    (branchSize a₀ ≤ branchSize a₁ && branchSize b₀ ≤ branchSize b₁)
  amax && bmax && (!common || i == j)

structure Family where
  rootCost : ℤ
  residual₀ : ℤ
  residual₁ : ℤ
  deriving DecidableEq

def family (a₀ a₁ : Branch) (i : Bool) : Family :=
  let r := 1 + branchSize a₀ + branchSize a₁
  let p := if rootOK a₀ && rootOK a₁ then scaledMass r else 0
  { rootCost := (if i then branchSize a₀ else branchSize a₁) * p
    residual₀ := atomMass a₀ - if i then 0 else p
    residual₁ := atomMass a₁ - if i then p else 0 }

def twoCharge (a₀ a₁ b₀ b₁ : Branch) (i j : Bool) : ℤ :=
  let a := family a₀ a₁ i
  let b := family b₀ b₁ j
  a.rootCost + b.rootCost + branchSize a₀ * a.residual₀ + branchSize a₁ * a.residual₁ +
    branchSize b₀ * b.residual₀ + branchSize b₁ * b.residual₁ -
    min a.residual₀ b.residual₀ - min a.residual₁ b.residual₁

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- All 193600 nonempty two-incidence records, including every permitted tie.
Each of 21 first-branch cases is checked by the kernel separately. -/
theorem two_certificate (a₀ a₁ b₀ b₁ : Branch) (i j : Bool)
    (ha : 0 < branchSize a₀ + branchSize a₁)
    (hb : 0 < branchSize b₀ + branchSize b₁)
    (hp : permitted a₀ a₁ b₀ b₁ i j = true) :
    twoCharge a₀ a₁ b₀ b₁ i j +
      132 * ((safe11 a₀ b₀ + safe11 a₁ b₁ : ℕ) : ℤ) -
      38 * ((safe12 a₀ b₀ + safe12 a₁ b₁ : ℕ) : ℤ) ≤ 2616 := by
  fin_cases a₀ <;> revert a₁ b₀ b₁ i j ha hb hp <;> decide +kernel

noncomputable section
/-- Appendix finite estimate for all real coefficient pairs (hence the stated box). -/
theorem one_corrected (a b : Branch) (ha : branchSize a > 0) (hb : branchSize b > 0)
    (gain loss : ℝ) :
    (oneCharge a b : ℝ) / 1000 + loss * safe11 a b - gain * safe12 a b ≤
      -1 + low gain loss := by
  have hc : (oneCharge a b : ℝ) + 132 * safe11 a b - 38 * safe12 a b ≤ 808 := by
    exact_mod_cast one_certificate a b ha hb
  have hm := balancing_domination ((oneCharge a b : ℝ) / 1000) gain loss 1
    (safe11 a b) (safe12 a b) (safe_count_budget a b)
  norm_num at hm
  linarith

theorem two_corrected (a₀ a₁ b₀ b₁ : Branch) (i j : Bool)
    (ha : 0 < branchSize a₀ + branchSize a₁)
    (hb : 0 < branchSize b₀ + branchSize b₁)
    (hp : permitted a₀ a₁ b₀ b₁ i j = true) (gain loss : ℝ) :
    (twoCharge a₀ a₁ b₀ b₁ i j : ℝ) / 1000 +
      loss * (safe11 a₀ b₀ + safe11 a₁ b₁) -
      gain * (safe12 a₀ b₀ + safe12 a₁ b₁) ≤ -1 + 2 * low gain loss := by
  have hc : (twoCharge a₀ a₁ b₀ b₁ i j : ℝ) +
      132 * (safe11 a₀ b₀ + safe11 a₁ b₁) -
      38 * (safe12 a₀ b₀ + safe12 a₁ b₁) ≤ 2616 := by
    exact_mod_cast two_certificate a₀ a₁ b₀ b₁ i j ha hb hp
  have hm := balancing_domination ((twoCharge a₀ a₁ b₀ b₁ i j : ℝ) / 1000) gain loss 2
    (safe11 a₀ b₀ + safe11 a₁ b₁) (safe12 a₀ b₀ + safe12 a₁ b₁)
    (by have := safe_count_budget a₀ b₀; have := safe_count_budget a₁ b₁; omega)
  push_cast at hm
  norm_num at hm
  linarith

/-- The paper's equality witness proves sharpness of the finite estimate. -/
theorem one_balancing_equality :
    (oneCharge (⟨5, by decide⟩ : Branch) (⟨2, by decide⟩ : Branch) : ℝ) / 1000 +
      (33 / 250) * safe11 ⟨5, by decide⟩ ⟨2, by decide⟩ -
      (19 / 500) * safe12 ⟨5, by decide⟩ ⟨2, by decide⟩ = -1 + (226 / 125) := by
  norm_num [oneCharge, atomMass, feasible, branchSize, scaledMass, safe11, safe12, available]

end
end CI2ZF.Appendix.CV
