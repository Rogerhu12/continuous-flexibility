module

public import ContinuousFlexibility.Analysis.CanonicalStripGeometry

/-!
# Symmetries of the actual inverse of a travel strip

The inverse is the set-theoretic inverse furnished by a genuine bijection.
Its periodic lift and reflection follow from the original chart identities;
no separate inverse with assumed symmetry is introduced.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

/-- Angular translation passes to the actual inverse on the open strip. -/
theorem travelStrip_invFunOn_periodic
    {a b c d P : ℝ} {F : PolarPoint → PolarPoint}
    (hBij : BijOn F (Ioo a b ×ˢ (univ : Set ℝ)) (Ioo c d ×ˢ univ))
    (hPeriod : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ),
      F (p + (0, P)) = F p + (0, P))
    {p : PolarPoint} (hp : p ∈ Ioo c d ×ˢ (univ : Set ℝ)) :
    Function.invFunOn F (Ioo a b ×ˢ univ) (p + (0, P)) =
      Function.invFunOn F (Ioo a b ×ˢ univ) p + (0, P) := by
  exact inverseChart_periodic_of_chart_periodic hBij.surjOn.mapsTo_invFunOn
    (fun _ hq => hBij.injOn.leftInvOn_invFunOn hq)
    (fun _ hq => hBij.surjOn.rightInvOn_invFunOn hq) hPeriod hp

/-- Reflection passes to the same actual inverse, without any continuity
assumption on that inverse. -/
theorem travelStrip_invFunOn_reflection
    {a b c d : ℝ} {F : PolarPoint → PolarPoint}
    (hBij : BijOn F (Ioo a b ×ˢ (univ : Set ℝ)) (Ioo c d ×ˢ univ))
    (hReflection : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ),
      F (p.1, -p.2) = ((F p).1, -(F p).2))
    {p : PolarPoint} (hp : p ∈ Ioo c d ×ˢ (univ : Set ℝ)) :
    Function.invFunOn F (Ioo a b ×ˢ univ) (p.1, -p.2) =
      ((Function.invFunOn F (Ioo a b ×ˢ univ) p).1,
        -(Function.invFunOn F (Ioo a b ×ˢ univ) p).2) := by
  let G := Function.invFunOn F (Ioo a b ×ˢ (univ : Set ℝ))
  have hGp : G p ∈ Ioo a b ×ˢ (univ : Set ℝ) :=
    hBij.surjOn.mapsTo_invFunOn hp
  have hGp' : ((G p).1, -(G p).2) ∈ Ioo a b ×ˢ (univ : Set ℝ) :=
    ⟨hGp.1, mem_univ _⟩
  have hRight : F (G p) = p := hBij.surjOn.rightInvOn_invFunOn hp
  have hEq : F ((G p).1, -(G p).2) = (p.1, -p.2) := by
    rw [hReflection (G p) hGp, hRight]
  calc
    G (p.1, -p.2) = G (F ((G p).1, -(G p).2)) := congrArg G hEq.symm
    _ = ((G p).1, -(G p).2) := hBij.injOn.leftInvOn_invFunOn hGp'

end ContinuousFlexibility.Analysis
