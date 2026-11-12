import ContinuousFlexibility.Analysis.N06PositiveCubicSourceMap
import ContinuousFlexibility.Analysis.N06WeightedHeight

/-!
# The positive cubic perturbation on the same N05 inverse

The weighted height lift is the one already proved to represent the
height of `B.inverse`. The forcing lift may include the actual scalar
reference columns. Primitive reference coefficient bounds and its true
weak equation then give the positive cubic source as a bounded
endomorphism of the original source level, without a material or angular
loss in the target.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff BigOperators ENNReal
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency true

theorem n06N05_positiveCubicSourceMap
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {Vol : VolumeModelData S K}
    {b : ℕ} {B : CanonicalDomainData S K Vol b}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hN05 : N05Properties D T S C K Vol b B)
    (Aexp : ℝ) (a c V q : ℕ → ℝ → ℝ) (κ : ℕ → ℝ) (Cref : ℝ)
    (hgeometry : N06PositiveUnitGeometry T K a c V q κ Cref)
    (J : Vol.level (3 / 4 : ℝ) 0 b →L[ℝ] Vol.level (3 / 4 : ℝ) 0 b)
    (hweak : ∀ F m, K.positive m = true → ∀ φ, CanonicalTest S K m φ →
      (∫ p, n06InverseCanonicalHeight B F m p *
        n06UnitReferenceTestOperator (a m) (c m) (V m) φ p ∂canonicalMeasure S K m) =
          ∫ p, Vol.forget (3 / 4 : ℝ) 0 b (J F) m p * φ p ∂canonicalMeasure S K m) :
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
                n06PositiveCubicTestOperator K A Bc Cc m φ p ∂canonicalMeasure S K m) → M F = G) := by
  have hVol : IsVolumeModel T S K Vol := hN05.2.1
  obtain ⟨_Cheight, _hCheight, H, _hHnorm, _hHglobal, hH, _hHgraph⟩ :=
    n06N05_exists_weightedHeight hN05
  exact n06_positiveCubicSourceMap_from_lifts hD hT hVol (3 / 4 : ℝ) Aexp B.lossMaterial
    (by norm_num) b a c V q κ Cref hgeometry (n06InverseCanonicalHeight B) J H hH hweak

end ContinuousFlexibility.Statements
