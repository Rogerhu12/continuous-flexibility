import ContinuousFlexibility.Analysis.N04bRootFieldFactors
import ContinuousFlexibility.Analysis.OneHighCircleFlowLocalization

/-!
# Global smooth extensions of the actual root characteristic factors

The existing smooth radial clamp takes the whole real line into the
original factor strip and equals the identity on a smaller closed collar.
Composition therefore gives globally smooth periodic factors, preserving
the actual corrected characteristic equation throughout that collar.
The positive factor remains positive everywhere.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Construct globally smooth periodic root factors while retaining both
actual corrected characteristic equations on one closed physical collar. -/
theorem n04b_exists_extended_corrected_root_factors
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hL : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {r₀ σ : ℝ} (hr₀ : r₀ ∈ Ioo D.a D.b)
    (hroot : deriv D.w r₀ = 0) (hsign : σ * deriv (deriv D.w) r₀ < 0) :
    ∃ (ρ : ℝ) (d c₀ : PolarPoint → ℝ), 0 < ρ ∧
      ContDiff ℝ ∞ d ∧ ContDiff ℝ ∞ c₀ ∧
      (∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi) ∧
      (∀ r, Function.Periodic (fun θ => c₀ (r, θ)) Real.pi) ∧
      (∀ p, 0 < c₀ p) ∧
      ∀ p ∈ Icc (0 : ℝ) ρ ×ˢ (univ : Set ℝ),
        rootProfileShift r₀ σ p ∈ annularOpen D ∧
          σ * minusCharacteristicSpeed (L.coefficients z) (rootProfileShift r₀ σ p) =
            d p - σ * Real.sqrt p.1 * c₀ p ∧
          σ * plusCharacteristicSpeed (L.coefficients z) (rootProfileShift r₀ σ p) =
            d p + σ * Real.sqrt p.1 * c₀ p := by
  obtain ⟨δ, d, c₀, hδ, hd, hc, hdp, hcp, hphysical⟩ :=
    n04b_exists_corrected_root_factors hT hS h03 hL hz hs hr₀ hroot hsign
  let ρ : ℝ := δ / 2
  have hρ : 0 < ρ := half_pos hδ
  have hab : -ρ ≤ ρ := by linarith
  have hinterval : Ioo (-ρ - ρ) (ρ + ρ) = Ioo (-δ) δ := by
    congr 1 <;> dsimp only [ρ] <;> ring
  let de : PolarPoint → ℝ :=
    circleFlowLocalizedSpeed (a := -ρ) (b := ρ) (ε := ρ) d hab hρ
  let ce : PolarPoint → ℝ :=
    circleFlowLocalizedSpeed (a := -ρ) (b := ρ) (ε := ρ) c₀ hab hρ
  have hds : ContDiff ℝ ∞ de :=
    contDiff_circleFlowLocalizedSpeed hab hρ (by simpa only [hinterval] using hd)
  have hcs : ContDiff ℝ ∞ ce :=
    contDiff_circleFlowLocalizedSpeed hab hρ (by simpa only [hinterval] using hc)
  have hdeperiod : ∀ r, Function.Periodic (fun θ => de (r, θ)) Real.pi :=
    circleFlowLocalizedSpeed_periodic hab hρ
      (fun r _ θ => by simpa only [Prod.mk_add_mk, add_zero] using hdp (r, θ))
  have hceperiod : ∀ r, Function.Periodic (fun θ => ce (r, θ)) Real.pi :=
    circleFlowLocalizedSpeed_periodic hab hρ
      (fun r _ θ => by simpa only [Prod.mk_add_mk, add_zero] using hcp (r, θ))
  refine ⟨ρ, de, ce, hρ, hds, hcs, hdeperiod, hceperiod, ?_, ?_⟩
  · intro p
    have hm : circleFlowSmoothTimeClamp (-ρ) ρ ρ hab hρ p.1 ∈ Ioo (-δ) δ := by
      simpa only [hinterval] using circleFlowSmoothTimeClamp_mem hab hρ p.1
    exact (hphysical
      (circleFlowSmoothTimeClamp (-ρ) ρ ρ hab hρ p.1, p.2)
      ⟨hm, mem_univ _⟩).2.1
  · intro p hp
    have ht : p.1 ∈ Icc (-ρ) ρ := ⟨by linarith [hp.1.1], hp.1.2⟩
    have hi : p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ) := by
      refine ⟨⟨by linarith [hp.1.1], ?_⟩, mem_univ _⟩
      exact hp.1.2.trans_lt (half_lt_self hδ)
    have hde : de p = d p := circleFlowLocalizedSpeed_eq hab hρ ht p.2
    have hce : ce p = c₀ p := circleFlowLocalizedSpeed_eq hab hρ ht p.2
    have hh := hphysical p hi
    refine ⟨hh.1, ?_⟩
    rw [hde, hce]
    exact hh.2.2 hp.1.1

end ContinuousFlexibility.Analysis
