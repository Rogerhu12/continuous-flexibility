import ContinuousFlexibility.Analysis.N06RootPhysicalWeightedSmallness
import ContinuousFlexibility.Analysis.RootCoefficientDivision
import ContinuousFlexibility.Analysis.RootDividedHeight

/-!
# The actual root discriminant and the unit height formula

The absorbed finite packet gives the original physical discriminant
where the actual profile equals its reference. The same divided height
is a product of the odd coefficient, the fixed radial radicand, and
the physical discriminant. No parameter regularity of a chosen root
flow is needed for these identities.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- This is the original physical discriminant at the actual profile,
expressed in the absorbed finite coordinates. -/
theorem n04PositiveGeometry_rootDiscriminant_eq_absorbed
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) (p : PolarPoint)
    (hr : p.1 ≠ 0) (hw : D.w p.1 ≠ 0)
    (hprofile : stateProfile D S C z.1 p.1 = D.w p.1) :
    polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p =
      n06RootNormalizedDiscriminant (n06ActualRootAbsorbedCoordinates D S z p) := by
  exact ((n06_actualRootAbsorbed_denominators D S z p).2.trans
    ((n06_normalizeRoot_denominators (v := n06ActualNuJetCoordinates D S z p) hw).2.trans
      (n06_rootFinite_denominators_eq hT hS hN z hr hprofile).2)).symm

/-- The equality holds on the same genuine root strip as the divided
coefficient formula, before taking any ordinary boundary derivatives. -/
theorem n04PositiveGeometry_rootDiscriminant_eqOn
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} {g : ℝ → ℝ} {r σ R : ℝ}
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) r σ R) :
    EqOn (fun p => polarDiscriminant (stateProfile D S C z.1)
      (stateHeight D S C z) (rootProfileShift r σ p))
      (fun p => n06RootNormalizedDiscriminant
        (n06ActualRootAbsorbedCoordinates D S z (rootProfileShift r σ p)))
      (Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ)) := by
  intro p hp
  have hs := hstrip p hp
  exact n04PositiveGeometry_rootDiscriminant_eq_absorbed hT hS hN z
    (rootProfileShift r σ p) hs.1.ne' hs.2.1.ne' hs.2.2.2.2.2.1

/-- The exact four-factor formula for every real power of the actual
unit divided height. All powers are taken on their positive locus. -/
theorem n04PositiveGeometry_rootDividedHeight_rpow_eq
    {wref g w : ℝ → ℝ} {h : PolarPoint → ℝ}
    {r σ : ℝ} {p : PolarPoint} {G : ℝ × ℝ × ℝ → ℝ}
    (hr : 0 < (rootProfileShift r σ p).1)
    (hw : 0 < wref (rootProfileShift r σ p).1) (hg : 0 < g p.1)
    (hD : 0 < polarDiscriminant w h (rootProfileShift r σ p))
    (hQ : heightQ (profileEnergy w (rootProfileShift r σ p))
      (heightRadial h (rootProfileShift r σ p))
      (angularPartial (heightAngular h) (rootProfileShift r σ p)) ≠ 0)
    (hχ : 0 < extendedRootOddCoefficient G p) (γ : ℝ) :
    rootDividedHeight 1 (rootCoefficientRadialFactor wref g w h r σ) G p ^ γ =
      (3 / 2 : ℝ) ^ (γ / 6) *
        (extendedRootOddCoefficient G p ^ (γ / 6) *
          (rootProfileRadicand wref g r σ p.1 ^ (-γ / 4) *
            polarDiscriminant w h (rootProfileShift r σ p) ^ (γ / 2))) := by
  let A : ℝ := rootProfileRadicand wref g r σ p.1
  let disc : ℝ := polarDiscriminant w h (rootProfileShift r σ p)
  let V : ℝ := rootCoefficientRadialFactor wref g w h r σ p
  have hA : 0 < A := rootProfileRadicand_pos hr hw hg
  have hVeq : V = A / disc ^ 2 := rootCoefficientRadialFactor_eq hr hw hg hD hQ
  have hV : 0 < V := hVeq.symm ▸ div_pos hA (pow_pos hD 2)
  have hsquare : (disc ^ 2) ^ (-γ / 4) = disc ^ (-γ / 2) := by
    rw [← Real.rpow_natCast disc 2, ← Real.rpow_mul hD.le]
    congr 1
    ring
  have hVpower : V ^ (-γ / 4) = A ^ (-γ / 4) * disc ^ (γ / 2) := by
    rw [hVeq, Real.div_rpow hA.le (sq_nonneg disc), hsquare, div_eq_mul_inv,
      ← Real.rpow_neg hD.le (-γ / 2), show -(-γ / 2) = γ / 2 by ring]
  have hχscale : 0 < (3 / 2 : ℝ) * extendedRootOddCoefficient G p :=
    mul_pos (by norm_num) hχ
  rw [rootDividedHeight_eq_powers (by norm_num : (0 : ℝ) < 1) hV hχ, one_mul,
    Real.mul_rpow (Real.rpow_nonneg hχscale.le _) (Real.rpow_nonneg hV.le _),
    ← Real.rpow_mul hχscale.le, ← Real.rpow_mul hV.le,
    show (1 / 6 : ℝ) * γ = γ / 6 by ring,
    show (-(1 / 4 : ℝ)) * γ = -γ / 4 by ring,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3 / 2) hχ.le, hVpower]
  dsimp only [A, disc]
  ring

/-- The formula holds throughout a genuine root strip wherever the
actual odd coefficient is positive. -/
theorem n04PositiveGeometry_rootDividedHeight_rpow_eqOn
    {wref g w : ℝ → ℝ} {h : PolarPoint → ℝ}
    {r σ R : ℝ} {G : ℝ × ℝ × ℝ → ℝ}
    (hstrip : RootCoefficientStripConditions wref g w h r σ R)
    (hχ : ∀ p ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ),
      0 < extendedRootOddCoefficient G p) (γ : ℝ) :
    EqOn (fun p => rootDividedHeight 1
      (rootCoefficientRadialFactor wref g w h r σ) G p ^ γ)
      (fun p => (3 / 2 : ℝ) ^ (γ / 6) *
        (extendedRootOddCoefficient G p ^ (γ / 6) *
          (rootProfileRadicand wref g r σ p.1 ^ (-γ / 4) *
            polarDiscriminant w h (rootProfileShift r σ p) ^ (γ / 2))))
      (Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ)) := by
  intro p hp
  have hs := hstrip p hp
  exact n04PositiveGeometry_rootDividedHeight_rpow_eq hs.1 hs.2.1 hs.2.2.1
    hs.2.2.2.1 hs.2.2.2.2.1.ne' (hχ p hp) γ

end ContinuousFlexibility.Analysis
