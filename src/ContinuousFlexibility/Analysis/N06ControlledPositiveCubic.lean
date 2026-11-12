import ContinuousFlexibility.Analysis.N06ReferenceForcingMap
import ContinuousFlexibility.Analysis.N06ReferenceUnitEquation
import ContinuousFlexibility.Analysis.N06N05PositiveCubicSourceMap

/-!
# The positive cubic map from the original N05 graph and reference atlas

The reference forcing is constructed from the three actual physical
columns in the selected source level. The original closed graph supplies
its weak equation. Thus the positive cubic map no longer takes a forcing
lift or an independent weak equation as input. The radial geometry and
its identification with the actual reference coefficients remain explicit.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

theorem n06N05_controlled_positiveCubicSourceMap
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {Vol : VolumeModelData S K} {base loss b : ℕ} {ε : ℝ}
    {B : CanonicalDomainData S K Vol b}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hborder : RadialTrueBorder D)
    (h : NonlinearPropertiesThrough05 D T S C R L K Vol b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (Aexp : ℝ) (a c pot q : ℕ → ℝ → ℝ) (κ : ℕ → ℝ) (Cref : ℝ)
    (hgeometry : N06PositiveUnitGeometry T K a c pot q κ Cref)
    (ha : ∀ m, K.positive m = true →
      EqOn (K.coefficients (C.referenceState, 0) m).a (fun p => a m p.1)
        (canonicalOpen S K m))
    (hb : ∀ m, K.positive m = true →
      EqOn (K.coefficients (C.referenceState, 0) m).b (fun _ => 0)
        (canonicalOpen S K m))
    (hc : ∀ m, K.positive m = true →
      EqOn (K.coefficients (C.referenceState, 0) m).c (fun p => c m p.1)
        (canonicalOpen S K m))
    (hpot : ∀ m, K.positive m = true →
      EqOn (K.potential (C.referenceState, 0) m) (fun p => pot m p.1)
        (canonicalOpen S K m))
    (hcd : ∀ m, K.positive m = true → ∀ y ∈ Ioo (K.left m) (K.right m),
      DifferentiableAt ℝ (c m) y) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ δ : ℝ, 0 ≤ δ → ∀ A Bc Cc : ℕ → PolarPoint → ℝ,
      N06PositiveCubicControl K b
        (fun m => T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (K.cell m)) ^ Aexp) δ A Bc Cc →
      ∃ M : Vol.level (3 / 4 : ℝ) 0 b →L[ℝ] Vol.level (3 / 4 : ℝ) 0 b,
        ‖M‖ ≤ Q * δ ∧
        (∀ F m φ, CanonicalTest S K m φ →
          (∫ p, Vol.forget (3 / 4 : ℝ) 0 b (M F) m p * φ p ∂canonicalMeasure S K m) =
            ∫ p, n06InverseCanonicalHeight B F m p *
              n06PositiveCubicTestOperator K A Bc Cc m φ p ∂canonicalMeasure S K m) ∧
        (∀ F (G : Vol.level (3 / 4 : ℝ) 0 b),
          (∀ m φ, CanonicalTest S K m φ →
            (∫ p, Vol.forget (3 / 4 : ℝ) 0 b G m p * φ p ∂canonicalMeasure S K m) =
              ∫ p, n06InverseCanonicalHeight B F m p *
                n06PositiveCubicTestOperator K A Bc Cc m φ p ∂canonicalMeasure S K m) →
          M F = G) := by
  obtain ⟨J, _hJ, hweak⟩ :=
    n06N05_exists_referenceForcingMap hD hT hS hborder h hcoordinates
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have hB : N04PartB S C L K base ε :=
    (n06_N04_qualitative_parts h.1.2.2.2.2.1).2
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  apply n06N05_positiveCubicSourceMap hD hT h.2 Aexp a c pot q κ Cref hgeometry J
  intro F m hm φ hφ
  have heq := n06_canonicalOperator_pairing_eq_unitReference hB href hsector hm
    (ha m hm) (hb m hm) (hc m hm) (hpot m hm) (hcd m hm)
    ((B.inverse F).val.1.1 m : PolarPoint → ℝ) hφ.1
  have hpair := heq.symm.trans (hweak F m hm φ hφ)
  simpa only [n06InverseCanonicalHeight_apply] using hpair

end ContinuousFlexibility.Statements
