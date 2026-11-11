import ContinuousFlexibility.Radial.OuterDeepGeometry
import ContinuousFlexibility.Radial.R07DeepTailData

/-!
# Equality of the actual outer and R07 deep-tail data

Both constructions use the same mass intervals, including the shifted
resistance intervals on the left. The right full core includes its outgoing
join, and the left entrance retains the complete initial resistance edge.
The equality also identifies the integer-power and real-power densities.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

/-- The outer factory is exactly the existing R07 factory beyond cell `n`.
This is equality of all eight data fields, without any deep-tail estimate
as a hypothesis. -/
theorem morsePhysicalDeepTail_eq_r07 {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) (j n : ℕ) (hn : M.index ≤ n) (η K : ℝ) :
    morsePhysicalDeepTail M D right j (n + 1)
        (morseOuterDeepEntrance M right n) η K =
      r07DeepTailData M D right j (n + 1) η K := by
  have hlog : tailPhysicalLog right = r07OutwardLog right := by
    cases right <;> rfl
  have hentry : morseOuterDeepEntrance M right n =
      (if right then r07MassNodeRadius M right (n + 1)
        else morseChainResistanceEnd M right (n + 1)) := by
    cases right with
    | false => exact morseOuterDeepEntrance_left_eq_resistanceEnd h n hn
    | true =>
        simpa only [morseOuterDeepEntrance, r07MassNodeRadius, ite_true] using
          (h.join_data true n hn).2.2.1
  have hp : outerMassLogDensity D j (tailPhysicalEndpoint D right) right =
      r07PhysicalDensity D right j := by
    funext x
    simpa only [r07PhysicalDensity, tailPhysicalEndpoint] using
      morsePhysicalDeepTail_density_eq M D right j (n + 1)
        (morseOuterDeepEntrance M right n) η K x
  unfold morsePhysicalDeepTail r07DeepTailData
  rw [hlog, hentry, hp]
  rfl

end ContinuousFlexibility.Radial
