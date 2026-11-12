import ContinuousFlexibility.Analysis.N06LeftColumnPhysical
import ContinuousFlexibility.Analysis.FixedReferenceScalarSourceMaterialJets
import ContinuousFlexibility.Analysis.LocalMixedProductBounds

/-!
# The actual left and nu columns in a fixed radial reference atlas

The physical fields are determined by the original N01/N03 data. Their
canonical pullbacks use the same stored inverse and the same stored
source factor. The identities below require only those actual fields on
the unit strip, so they apply to positive pieces and negative halves.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open CanonicalGeometry
open scoped ContDiff

def referenceScalarColumnRadial (D : ReferenceData) (S : PhysicalSpacesData) :
    Atom → ℝ → ℝ
  | .leftColumn => deriv (fun r => D.w r * deriv S.chiLeft r)
  | .nuColumn => referenceColumn D
  | _ => fun _ => 0

def referenceScalarColumnAngular : Atom → ℝ → ℝ
  | .leftColumn => fun _ => 1
  | .nuColumn => cosineMode 2
  | _ => fun _ => 0

theorem referenceScalarColumn_regular
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (v : Atom) (hv : v = .leftColumn ∨ v = .nuColumn) :
    ContDiff ℝ ∞ (referenceScalarColumnRadial D S v) ∧
      ContDiff ℝ ∞ (referenceScalarColumnAngular v) ∧
      Function.Periodic (referenceScalarColumnAngular v) Real.pi := by
  have hD : RadialProfileGeometry D := hN.1.1.choose_spec.1
  rcases hv with rfl | rfl
  · refine ⟨?_, contDiff_const, fun _ => rfl⟩
    exact (contDiff_infty_iff_deriv.mp
      (hD.2.2.1.1.mul (contDiff_infty_iff_deriv.mp hS.2.2.1.1).2)).2
  · refine ⟨referenceColumn_contDiff hD hN.1.2.2.2.1,
      r11b_contDiff_cosineMode 2, ?_⟩
    intro θ
    simpa only [referenceScalarColumnAngular, Nat.mul_one] using
      cosineMode_even_frequency_periodic 1 θ

/-- Exact inverse and source-factor fields identify each actual reference
column throughout its unit strip. No canonical column estimate is an
input, and no alternative physical forcing is selected. -/
theorem referenceScalarColumn_actual_eqOn
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (K : CanonicalData S) (m : ℕ) (X F : ℝ → ℝ)
    (hinverse : ∀ p ∈ unitStrip,
      K.inverseChart (C.referenceState, 0) m (canonicalUnitPoint K m p) = (X p.1, p.2))
    (hrange : ∀ x ∈ Ioo (0 : ℝ) 1, X x ∈ radialCore D)
    (hfactor : ∀ p ∈ unitStrip,
      atom D T S C L K (C.referenceState, 0) m .sourceFactor p = F p.1)
    (v : Atom) (hv : v = .leftColumn ∨ v = .nuColumn) :
    EqOn (atom D T S C L K (C.referenceState, 0) m v)
      (fun p : PolarPoint => F p.1 * referenceScalarColumnRadial D S v (X p.1) *
        referenceScalarColumnAngular v p.2) unitStrip := by
  intro p hp
  have hsource (f : PolarPoint → ℝ) :
      canonicalSource S K (C.referenceState, 0) m f (canonicalUnitPoint K m p) =
        F p.1 * f (X p.1, p.2) := by
    rw [← hfactor p hp]
    change canonicalSource S K (C.referenceState, 0) m f (canonicalUnitPoint K m p) =
      canonicalSource S K (C.referenceState, 0) m (fun _ => 1)
        (canonicalUnitPoint K m p) * f (X p.1, p.2)
    simp only [canonicalSource, hinverse p hp, mul_one, div_eq_mul_inv]
    ring
  rcases hv with rfl | rfl
  · change canonicalSource S K (C.referenceState, 0) m
      (divergenceOperator (L.coefficients (C.referenceState, 0))
        (fun q => S.chiLeft q.1)) (canonicalUnitPoint K m p) = _
    rw [hsource]
    have he := n06_currentLeftColumn_reference hS hN.1.1 hN.2 (X p.1, p.2)
    change divergenceOperator (L.coefficients (C.referenceState, 0))
      (fun q => S.chiLeft q.1) (X p.1, p.2) =
        n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft) (X p.1, p.2) at he
    rw [he, n06_referenceLeftColumn_formula]
    simp only [referenceScalarColumnRadial, referenceScalarColumnAngular, mul_one]
  · change canonicalSource S K (C.referenceState, 0) m
      (nuColumnField D S C (C.referenceState, 0)) (canonicalUnitPoint K m p) = _
    rw [hsource]
    have hD : RadialProfileGeometry D := hN.1.1.1.1.choose_spec.1
    have hborder : RadialTrueBorder D := hN.1.1.1.2.2.2.1
    have hr : (X p.1, p.2).1 ≠ (0 : ℝ) :=
      (hD.1.trans (hrange p.1 hp.1).1).ne'
    rw [n06_nuColumn_reference hD.2.2.1.1 hborder.1 hD.2.2.2.1.1 hN.1.1.2.2.1 hr]
    change F p.1 * (referenceColumn D (X p.1) * cosineMode 2 p.2) =
      F p.1 * referenceColumn D (X p.1) * cosineMode 2 p.2
    ring

end ContinuousFlexibility.Analysis
