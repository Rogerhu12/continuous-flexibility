import ContinuousFlexibility.Analysis.BoundaryTaylorPrincipalRemainder
import ContinuousFlexibility.Analysis.CanonicalDensityExtension

/-!
# Canonical zero jets for the actual boundary Taylor construction

The density is built from the actual corrected chart and logarithmic
height. The root normal form gives physical zero jets, then a genuine
local inverse transports them. Its interior agreement with invFunOn
identifies the extension with the actual canonical numerator.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- No endpoint jets of the canonical numerator are inputs. They follow
from the root equation and the actual finite Taylor construction. Global
invertibility is an explicit geometric input and is only used in the open
strip. The conclusion is independent of invFunOn's totalized boundary values. -/
theorem exists_boundaryTaylor_canonicalDensity_extension
    {U V : Set PolarPoint} (hU : IsOpen U) (hV : IsOpen V)
    {A : SymmetricCoefficients} {Fref F : PolarPoint → PolarPoint}
    {href h : PolarPoint → ℝ}
    (hAa : ContDiffOn ℝ ∞ A.a U) (hAb : ContDiffOn ℝ ∞ A.b U)
    (hAc : ContDiffOn ℝ ∞ A.c U)
    (hFref : ContDiffOn ℝ ∞ Fref U) (hF : ContDiffOn ℝ ∞ F U)
    (hRef : ContDiffOn ℝ ∞ href U) (hh : ContDiffOn ℝ ∞ h U)
    (hRefPos : ∀ p ∈ U, 0 < href p) (hPos : ∀ p ∈ U, 0 < h p)
    {c d α β : ℝ} (hcd : c < d)
    (hc : ∀ θ : ℝ, (c, θ) ∈ U) (hd : ∀ θ : ℝ, (d, θ) ∈ U)
    (n : ℕ) (side : Bool) (i : Fin 3) {N : ℝ → ℝ} (hN : ContDiff ℝ ∞ N)
    (hJ : ∀ p ∈ U, planeJacobian F p ≠ 0)
    (hJnew : ∀ p ∈ U,
      planeJacobian (boundaryTaylorChart (n + 1) c d Fref F) p ≠ 0)
    (hroot : EqOn (canonicalCoefficientComponent i (coordinatePrincipalDensity A F h))
      (fun p => N ((F p).1)) V)
    (hclosure : ∀ θ : ℝ, (if side then d else c, θ) ∈ closure V)
    (hbij : BijOn (boundaryTaylorChart (n + 1) c d Fref F)
      (Ioo c d ×ˢ (univ : Set ℝ)) (Ioo α β ×ˢ (univ : Set ℝ)))
    (hboundary : ∀ p : PolarPoint, p.1 = c ∨ p.1 = d →
      (boundaryTaylorChart (n + 1) c d Fref F p).1 ∉ Ioo α β)
    (θ : ℝ) :
    let Fnew := boundaryTaylorChart (n + 1) c d Fref F;
    let ρ := canonicalCoefficientComponent i
      (coordinatePrincipalDensity A Fnew (boundaryTaylorHeight n c d href h));
    let G := Function.invFunOn Fnew (Ioo c d ×ˢ (univ : Set ℝ));
    let x : ℝ := if side then d else c;
    ∃ (E : PolarPoint → ℝ) (δ : ℝ), 0 < δ ∧
      ContDiffOn ℝ ∞ E (Metric.ball (Fnew (x, θ)) δ) ∧
      EqOn E (fun q => ρ (G q) - N q.1)
        (Metric.ball (Fnew (x, θ)) δ ∩ (Ioo α β ×ˢ (univ : Set ℝ))) ∧
      ∀ k ≤ n, iteratedDeriv k (fun r => E (r, (Fnew (x, θ)).2))
        (Fnew (x, θ)).1 = 0 := by
  let Fnew := boundaryTaylorChart (n + 1) c d Fref F
  let x : ℝ := if side then d else c
  have hx : ∀ t : ℝ, (x, t) ∈ U := by
    cases side with
    | false => exact hc
    | true => exact hd
  have hxcc : x ∈ Icc c d := by
    cases side with
    | false => exact ⟨le_rfl, hcd.le⟩
    | true => exact ⟨hcd.le, le_rfl⟩
  have hFn : ContDiffOn ℝ ∞ Fnew U :=
    contDiffOn_boundaryTaylorChart hU hFref hF hc hd (n + 1) hFref
  obtain ⟨hR, hzero⟩ :=
    boundaryTaylorPrincipalRemainder_smooth_zeroJets hU hV
      hAa hAb hAc hFref hF hRef hh hRefPos hPos hcd.ne hc hd
      n side i hN hJ hJnew hroot hclosure
  exact exists_canonicalDensity_extension_of_physical_zeroJets hcd
    hbij.mapsTo hboundary hbij.injOn hbij.surjOn.mapsTo_invFunOn
    hbij.surjOn.rightInvOn_invFunOn hU hR x hx hxcc hzero θ
    hFn hJnew

end ContinuousFlexibility.Analysis

