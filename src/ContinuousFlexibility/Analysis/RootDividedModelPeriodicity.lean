module

public import ContinuousFlexibility.Analysis.N01ScaledDividedFactorJets
public import ContinuousFlexibility.Analysis.RootDividedHeight
public import ContinuousFlexibility.Analysis.RootChartSymmetry
public import ContinuousFlexibility.Analysis.NeighborhoodCharacteristicSpeedExtension

/-!
# Periodicity of the actual divided root height

The normalized divided determinant retains the angular period of the
actual state height. Consequently the smooth divided root height and
its inverse are periodic on their total domains. No regularity or
quantitative estimate is assumed for this algebraic identity.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

theorem rootScaledDividedDiscriminant_period_add
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (g : ℝ → ℝ) (r σ δ x θ : ℝ) :
    rootScaledDividedDiscriminant D S C z g r σ δ (x, θ + Real.pi) =
      rootScaledDividedDiscriminant D S C z g r σ δ (x, θ) := by
  have hz := neighborhood_stateHeight_periodic (C := C) hS z
  have hA := (periodic_heightCorrectedCoefficients (stateProfile D S C z.1) hz).1
  have hc := (periodic_factoredCharacteristicField D.w g
    (stateProfile D S C z.1) (r := r) (σ := σ) hz).1
  have hshift : rootProfileShift r σ (δ * x, θ + Real.pi) =
      rootProfileShift r σ (δ * x, θ) + (0, Real.pi) := by
    simp only [rootProfileShift, Prod.mk_add_mk, add_zero]
  have hc' : factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) r σ (δ * x, θ + Real.pi) =
      factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) r σ (δ * x, θ) := by
    simpa only [Prod.mk_add_mk, add_zero] using hc (δ * x, θ)
  simp only [rootScaledDividedDiscriminant, rootCoefficientRadialFactor,
    hshift, hA (rootProfileShift r σ (δ * x, θ)), hc']

theorem rootDividedHeight_period_add
    {G : ℝ × ℝ × ℝ → ℝ} {V : PolarPoint → ℝ} {δ T : ℝ}
    (hG : ∀ x ζ θ, G (x, ζ, θ + T) = G (x, ζ, θ) + T)
    (hV : ∀ x θ, V (x, θ + T) = V (x, θ)) (x θ : ℝ) :
    rootDividedHeight δ V G (x, θ + T) = rootDividedHeight δ V G (x, θ) := by
  have hχ : extendedRootOddCoefficient G (x, θ + T) =
      extendedRootOddCoefficient G (x, θ) :=
    seeleyPeriodicExtension_periodic
      (fun r _ => rootOddCoefficient_periodic hG r) x θ
  simp only [rootDividedHeight, extendedRootRadialFactor, hχ, hV x θ]

end ContinuousFlexibility.Analysis
