module

public import ContinuousFlexibility.Radial.InnerIntervalTrace

/-!
# First-order integration by parts on the original closed model domain

This is proved on the actual Schrodinger core and then extended by
continuity. The auxiliary test is any smooth function at the closed
interval; it need not vanish at the endpoints because the domain
coordinate does.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff InnerProductSpace

theorem innerEnergyClosure_firstOrder_pairing {a b : ℝ} {V p : ℝ → ℝ}
    (hab : a < b) (hp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x)
    {P Pd u d q : RadialL2}
    (hP : (P : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator p)
    (hPd : (Pd : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator (deriv p))
    (hu : (u, d, q) ∈ closure (IntervalEnergyCore V a b)) :
    ⟪d, P⟫_ℝ + ⟪u, Pd⟫_ℝ = 0 :=
  innerEnergyClosure_derivative_pairing hab hp hP hPd hu

end ContinuousFlexibility.Radial
