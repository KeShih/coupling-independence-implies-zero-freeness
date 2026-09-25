import ZeroFreeness.Potts.Model.PinningRestriction

/-! A class of finite pinning data closed under induced restriction and
further pinning. No degree or zero-free conclusion is built into the class. -/
namespace ZeroFreeness.Potts
open PottsCI
universe u v

structure PinningFamily (C : Type v) [Fintype C] where
  contains : {V : Type u} → [Fintype V] → PinningData V C → Prop
  restrict_mem : ∀ {V W : Type u} [Fintype V] [Fintype W]
    (I : PinningData V C) (e : W ↪ V) (p : V → Option C),
    (∀ w, p (e w) = none) → contains I → contains (restrictPinningData I e p)

end ZeroFreeness.Potts
