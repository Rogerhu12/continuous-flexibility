module

public import ContinuousFlexibility.Analysis.N06PositiveCubicPairing
public import ContinuousFlexibility.Analysis.N06WeakCubicSourceMap

/-!
# The actual positive cubic source as a continuous linear map

The reference forcing and height are the selected bounded linear lifts.
The weak reference equation produces the five genuine graph fields;
their material bound and the actual cubic pairing give a unique bounded
linear source map on the original volume level. Its constant precedes
the perturbing coefficient family and its smallness parameter.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff BigOperators ENNReal
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem n06_positiveCubicSourceMap_from_lifts
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
    {Vol : VolumeModelData S K}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hVol : IsVolumeModel T S K Vol)
    (β Aexp loss : ℝ) (hβ : 0 < β) (b : ℕ)
    (a c V q : ℕ → ℝ → ℝ) (κ : ℕ → ℝ) (Cref : ℝ)
    (hgeometry : N06PositiveUnitGeometry T K a c V q κ Cref)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E →ₗ[ℝ] CanonicalSequence S K)
    (J : E →L[ℝ] Vol.level β 0 b) (H : E →L[ℝ] Vol.level β (-loss) b)
    (hH : ∀ F, Vol.forget β (-loss) b (H F) = U F)
    (hweak : ∀ F m, K.positive m = true → ∀ φ, CanonicalTest S K m φ →
      (∫ p, U F m p * n06UnitReferenceTestOperator (a m) (c m) (V m) φ p
        ∂canonicalMeasure S K m) =
          ∫ p, Vol.forget β 0 b (J F) m p * φ p ∂canonicalMeasure S K m) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ δ : ℝ, 0 ≤ δ → ∀ A B C : ℕ → PolarPoint → ℝ,
      N06PositiveCubicControl K b
        (fun m => T.H (T.sample (K.cell m)) ^ β * T.E0 (T.sample (K.cell m)) ^ Aexp) δ A B C →
      ∃ M : E →L[ℝ] Vol.level β 0 b, ‖M‖ ≤ Q * δ ∧
        (∀ F m φ, CanonicalTest S K m φ →
          (∫ p, Vol.forget β 0 b (M F) m p * φ p ∂canonicalMeasure S K m) =
            ∫ p, U F m p * n06PositiveCubicTestOperator K A B C m φ p
              ∂canonicalMeasure S K m) ∧
        (∀ F (G : Vol.level β 0 b),
          (∀ m φ, CanonicalTest S K m φ →
            (∫ p, Vol.forget β 0 b G m p * φ p ∂canonicalMeasure S K m) =
              ∫ p, U F m p * n06PositiveCubicTestOperator K A B C m φ p
                ∂canonicalMeasure S K m) → M F = G) := by
  obtain ⟨Qsource, hQsource, hsource⟩ := n06_positiveCubicSource_material_family
    hD hT hVol β Aexp loss hβ b a c V q κ Cref hgeometry
  let Q : ℝ := Qsource * (‖J‖ + ‖H‖)
  have hQ : 0 ≤ Q := mul_nonneg hQsource (add_nonneg (norm_nonneg J) (norm_nonneg H))
  have href (F : E) : ∀ m, K.positive m = true → ∀ φ, CanonicalTest S K m φ →
      (∫ p, n06MaterialJetRow T K β (-loss) (H F).val m 0 p *
        n06UnitReferenceTestOperator (a m) (c m) (V m) φ p ∂canonicalMeasure S K m) =
          ∫ p, n06MaterialJetRow T K β 0 (J F).val m 0 p * φ p ∂canonicalMeasure S K m := by
    intro m hm φ hφ
    rw [n06MaterialJetRow_zero_eq_forget hVol β (-loss) b (H F) m,
      n06MaterialJetRow_zero_eq_forget hVol β 0 b (J F) m, hH F]
    exact hweak F m hm φ hφ
  refine ⟨Q, hQ, ?_⟩
  intro δ hδ A B C hcoeff
  apply n06Volume_sourceMap_of_weak_pairing hVol β 0 b U
    (n06PositiveCubicTestOperator K A B C)
    (hcoeff.testOperator_memLp hgeometry.left hgeometry.right)
    (mul_nonneg hQ hδ)
  intro F
  obtain ⟨P, G, hGfield, hGnorm⟩ := hsource δ hδ A B C hcoeff (J F) (H F) (href F)
  refine ⟨G, ?_, ?_⟩
  · intro m φ hφ
    have hpair := n06_positiveCubicSource_pairing hVol P hcoeff
      hgeometry.left hgeometry.right G hGfield m φ hφ
    rw [hH F] at hpair
    exact hpair
  · have hlifts : ‖J F‖ + ‖H F‖ ≤ (‖J‖ + ‖H‖) * ‖F‖ := by
      calc
        _ ≤ ‖J‖ * ‖F‖ + ‖H‖ * ‖F‖ := add_le_add (J.le_opNorm F) (H.le_opNorm F)
        _ = _ := by ring
    calc
      ‖G‖ ≤ (Qsource * δ) * (‖J F‖ + ‖H F‖) := hGnorm
      _ ≤ (Qsource * δ) * ((‖J‖ + ‖H‖) * ‖F‖) :=
        mul_le_mul_of_nonneg_left hlifts (mul_nonneg hQsource hδ)
      _ = (Q * δ) * ‖F‖ := by dsimp only [Q]; ring

end ContinuousFlexibility.Statements
