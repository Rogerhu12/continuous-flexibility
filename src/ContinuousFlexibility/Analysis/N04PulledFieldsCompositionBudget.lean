import Mathlib.Tactic

/-!
# One common high order for the masked moving-point estimate

The inverse prefix is requested through `N`; its denominator uses
`top + 1`. Both inverse and physical high orders fit into `s + loss`,
where the loss is selected before the spatial order `s`.
-/

namespace ContinuousFlexibility.Analysis

def n04PulledFieldsCompositionPrefix (s K offset : ℕ) : ℕ :=
  s + (offset + 1) * K

def n04PulledFieldsCompositionTop (s K offset : ℕ) : ℕ :=
  n04PulledFieldsCompositionPrefix s K offset + offset

def n04PulledFieldsCompositionLoss (base K offset physicalLoss : ℕ) : ℕ :=
  (offset + 1) * K + offset + max (base + 1) physicalLoss

theorem n04PulledFieldsCompositionPrefix_total_le (s K offset : ℕ) :
    K + s ≤ n04PulledFieldsCompositionPrefix s K offset := by
  have hK : K ≤ (offset + 1) * K := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right K (Nat.le_add_left 1 offset)
  unfold n04PulledFieldsCompositionPrefix
  omega

theorem n04PulledFieldsCompositionPrefix_le_top (s K offset : ℕ) :
    s + (offset + 1) * K ≤ n04PulledFieldsCompositionTop s K offset :=
  Nat.le_add_right _ _

theorem n04PulledFieldsCompositionTop_order_le
    {k a b K s offset : ℕ} (hk : k ≤ K) (hab : a + b ≤ s) :
    a + b + (offset + 1) * k ≤ n04PulledFieldsCompositionTop s K offset :=
  (Nat.add_le_add hab (Nat.mul_le_mul_left (offset + 1) hk)).trans
    (n04PulledFieldsCompositionPrefix_le_top s K offset)

theorem n04PulledFieldsCompositionTop_inverseHigh (base s K offset : ℕ) :
    base + n04PulledFieldsCompositionTop s K offset + 1 =
      s + (base + (offset + 1) * (K + 1)) := by
  unfold n04PulledFieldsCompositionTop n04PulledFieldsCompositionPrefix
  ring

/-- The maximum of the two actual high indices is one spatial order
plus a loss depending only on the fixed bases and parameter prefix. -/
theorem n04PulledFieldsCompositionLoss_maxHigh (base s K offset physicalLoss : ℕ) :
    max (base + n04PulledFieldsCompositionTop s K offset + 1)
        (n04PulledFieldsCompositionTop s K offset + physicalLoss) =
      s + n04PulledFieldsCompositionLoss base K offset physicalLoss := by
  unfold n04PulledFieldsCompositionTop n04PulledFieldsCompositionPrefix
    n04PulledFieldsCompositionLoss
  omega

theorem n04PulledFieldsCompositionLoss_inverseHigh_le
    (base s K offset physicalLoss : ℕ) :
    base + n04PulledFieldsCompositionTop s K offset + 1 ≤
      s + n04PulledFieldsCompositionLoss base K offset physicalLoss := by
  rw [← n04PulledFieldsCompositionLoss_maxHigh base s K offset physicalLoss]
  exact le_max_left _ _

theorem n04PulledFieldsCompositionLoss_physicalHigh_le
    (base s K offset physicalLoss : ℕ) :
    n04PulledFieldsCompositionTop s K offset + physicalLoss ≤
      s + n04PulledFieldsCompositionLoss base K offset physicalLoss := by
  rw [← n04PulledFieldsCompositionLoss_maxHigh base s K offset physicalLoss]
  exact le_max_right _ _

end ContinuousFlexibility.Analysis
