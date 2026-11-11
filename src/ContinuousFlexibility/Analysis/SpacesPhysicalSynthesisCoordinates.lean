import ContinuousFlexibility.Analysis.SpacesPhysicalSynthesisRows
import ContinuousFlexibility.Analysis.SpacesCylinderEvenJets

/-!
# Weighted coordinates of physical shell synthesis

The finite radial Leibniz sum produces each actual mixed jet. Gluing is
bounded on the entire row Hilbert space, and signed angular evenization
enforces the symmetry of the physical weak graph without increasing the
coordinate norm.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal NNReal BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)

def spacesPhysicalSynthesisRawCoordinate (a b c k : ℕ) : SpacesPhysicalIntegerRows →L[ℝ] CylinderL2 :=
  ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) •
    (spacesPhysicalEnvelopeSynthesis hT i c).comp
      (spacesPhysicalSynthesisJetRows hT (a - i) b c (a + b + c) (by omega) k)

theorem spacesPhysicalSynthesisRawCoordinate_apply (a b c k : ℕ) (u : SpacesPhysicalIntegerRows) :
    spacesPhysicalSynthesisRawCoordinate hT a b c k u =
      ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) • spacesPhysicalEnvelopeSynthesis hT i c
        (spacesPhysicalSynthesisJetRows hT (a - i) b c (a + b + c) (by omega) k u) := by
  simp only [spacesPhysicalSynthesisRawCoordinate, sum_apply, smul_apply, ContinuousLinearMap.comp_apply]

def spacesPhysicalSynthesisCoordinateConstant (a b c : ℕ) : ℝ≥0 :=
  (∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ≥0) * spacesPhysicalEnvelopeConstant hT i c) *
    spacesPhysicalFourierGrowthConstant (a + b + c)

theorem spacesPhysicalSynthesisRawCoordinate_norm_le (a b c k : ℕ) (u : SpacesPhysicalIntegerRows) :
    ‖spacesPhysicalSynthesisRawCoordinate hT a b c k u‖ ≤
      (spacesPhysicalSynthesisCoordinateConstant hT a b c : ℝ) *
        Real.exp (((a + b + c : ℕ) : ℝ) * (k : ℝ)) * ‖u‖ := by
  have hi (i : ℕ) :
      ‖(a.choose i : ℝ) • spacesPhysicalEnvelopeSynthesis hT i c
        (spacesPhysicalSynthesisJetRows hT (a - i) b c (a + b + c) (by omega) k u)‖ ≤
      ((a.choose i : ℝ) * (spacesPhysicalEnvelopeConstant hT i c : ℝ)) *
        ((spacesPhysicalFourierGrowthConstant (a + b + c) : ℝ) *
          Real.exp (((a + b + c : ℕ) : ℝ) * (k : ℝ)) * ‖u‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    calc
      _ ≤ (a.choose i : ℝ) * ((spacesPhysicalEnvelopeConstant hT i c : ℝ) *
          ‖spacesPhysicalSynthesisJetRows hT (a - i) b c (a + b + c) (by omega) k u‖) :=
        mul_le_mul_of_nonneg_left (spacesPhysicalEnvelopeSynthesis_norm_le hT i c _) (Nat.cast_nonneg _)
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (spacesPhysicalSynthesisJetRows_norm_le hT
            (a - i) b c (a + b + c) (by omega) k u) (spacesPhysicalEnvelopeConstant hT i c).property)
          (Nat.cast_nonneg _)
  rw [spacesPhysicalSynthesisRawCoordinate_apply]
  calc
    _ ≤ ∑ i ∈ Finset.range (a + 1),
        ‖(a.choose i : ℝ) • spacesPhysicalEnvelopeSynthesis hT i c
          (spacesPhysicalSynthesisJetRows hT (a - i) b c (a + b + c) (by omega) k u)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (a + 1),
        ((a.choose i : ℝ) * (spacesPhysicalEnvelopeConstant hT i c : ℝ)) *
          ((spacesPhysicalFourierGrowthConstant (a + b + c) : ℝ) *
            Real.exp (((a + b + c : ℕ) : ℝ) * (k : ℝ)) * ‖u‖) :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by
      rw [← Finset.sum_mul]
      simp only [spacesPhysicalSynthesisCoordinateConstant, NNReal.coe_mul, NNReal.coe_sum,
        NNReal.coe_natCast]
      ring

/-- One exact weighted derivative coordinate of shell synthesis. -/
def spacesPhysicalSynthesisCoordinate (a b c k : ℕ) : SpacesPhysicalIntegerRows →L[ℝ] CylinderL2 :=
  (spacesCylinderParity b).comp (spacesPhysicalSynthesisRawCoordinate hT a b c k)

theorem spacesPhysicalSynthesisCoordinate_apply (a b c k : ℕ) (u : SpacesPhysicalIntegerRows) :
    spacesPhysicalSynthesisCoordinate hT a b c k u =
      spacesCylinderParity b (spacesPhysicalSynthesisRawCoordinate hT a b c k u) := rfl

theorem spacesPhysicalSynthesisCoordinate_norm_le (a b c k : ℕ) (u : SpacesPhysicalIntegerRows) :
    ‖spacesPhysicalSynthesisCoordinate hT a b c k u‖ ≤
      (spacesPhysicalSynthesisCoordinateConstant hT a b c : ℝ) *
        Real.exp (((a + b + c : ℕ) : ℝ) * (k : ℝ)) * ‖u‖ :=
  (spacesCylinderParity_norm_le b _).trans (spacesPhysicalSynthesisRawCoordinate_norm_le hT a b c k u)

/-- The compactly supported smooth packet before its angular evenization. -/
def spacesPhysicalPacket (n : ℤ) (S : Finset SpacesTorusFrequency) (u : CylinderL2)
    (p : PolarPoint) : ℝ :=
  spacesRadialEnvelope n p.1 * spacesPhysicalCellJetFunction n S u p

theorem spacesPhysicalPacket_contDiff (n : ℤ) (S : Finset SpacesTorusFrequency) (u : CylinderL2) :
    ContDiff ℝ ∞ (spacesPhysicalPacket n S u) :=
  ((spacesRadialEnvelope_contDiff n).comp contDiff_fst).mul
    (spacesPhysicalCellJetFunction_contDiff n S u)

theorem spacesPhysicalPacket_isCylinderTest (n : ℤ) (S : Finset SpacesTorusFrequency) (u : CylinderL2) :
    IsCylinderTest (spacesPhysicalPacket n S u) := by
  refine ⟨spacesPhysicalPacket_contDiff n S u, ?_, |(n : ℝ)| + 3, by positivity, fun p hp => ?_⟩
  · intro p
    simp only [spacesPhysicalPacket, Prod.fst_add, add_zero,
      spacesPhysicalCellJetFunction_periodic n S u p]
  · have hd : |p.1| ≤ |p.1 - n| + |(n : ℝ)| := by
      calc
        |p.1| = |(p.1 - n) + n| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    have hz : spacesRadialEnvelope n p.1 = 0 := by
      apply spacesRadialEnvelope_eq_zero
      intro hm
      have hdist : |p.1 - n| < 2 := abs_lt.mpr ⟨by linarith [hm.1], by linarith [hm.2]⟩
      linarith
    simp only [spacesPhysicalPacket, hz, zero_mul]

theorem spacesRadialEnvelope_derivative_mul_indicator (n : ℤ) (i : ℕ)
    (f : PolarPoint → ℝ) (p : PolarPoint) :
    iteratedDeriv i (spacesRadialEnvelope n) p.1 * (spacesPhysicalCellRadialSet n).indicator f p =
      iteratedDeriv i (spacesRadialEnvelope n) p.1 * f p := by
  by_cases hp : p ∈ spacesPhysicalCellRadialSet n
  · rw [indicator_of_mem hp]
  · have hz : iteratedDeriv i (spacesRadialEnvelope n) p.1 = 0 := by
      by_contra hz
      have hm := spacesRadialEnvelope_derivative_support n i hz
      apply hp
      exact ⟨⟨by linarith [hm.1], by linarith [hm.2]⟩, mem_univ _⟩
    rw [hz, zero_mul, zero_mul]

theorem spacesPhysicalSynthesisTerm_single_ae (r b c i s : ℕ) (hord : r + b + c ≤ s)
    (k : ℕ) (n : ℤ) (u : CylinderL2) :
    (spacesPhysicalEnvelopeSynthesis hT i c
      (spacesPhysicalSynthesisJetRows hT r b c s hord k (lp.single 2 n u)) : PolarPoint → ℝ) =ᵐ[
      materialCylinderMeasure] fun p => T.M (T.radius p.1) ^ c *
        iteratedDeriv i (spacesRadialEnvelope n) p.1 *
          mixedDerivative r b (spacesPhysicalCellJetFunction n
            (spacesPhysicalFrequencyBand (T.M (T.radius n)) k) u) p := by
  rw [spacesPhysicalSynthesisJetRows_single]
  filter_upwards [spacesPhysicalEnvelopeSynthesis_single_ae hT i c n
      (T.M (T.radius n) ^ c • spacesPhysicalCellBand n (T.M (T.radius n)) k r b u),
    Lp.coeFn_smul (T.M (T.radius n) ^ c) (spacesPhysicalCellBand n (T.M (T.radius n)) k r b u),
    spacesPhysicalCellJet_ae n (spacesPhysicalFrequencyBand (T.M (T.radius n)) k) r b u]
    with p he hs hj
  rw [he, hs, Pi.smul_apply, smul_eq_mul]
  change spacesPhysicalEnvelopeMultiplier (T := T) i c n p *
    (T.M (T.radius n) ^ c * spacesPhysicalCellJet n
      (spacesPhysicalFrequencyBand (T.M (T.radius n)) k) r b u p) = _
  rw [hj]
  unfold spacesPhysicalEnvelopeMultiplier
  have hn : T.M (T.radius n) ^ c ≠ 0 := pow_ne_zero c (spaces_material_M_pos hT n).ne'
  calc
    _ = T.M (T.radius p.1) ^ c * (iteratedDeriv i (spacesRadialEnvelope n) p.1 *
        (spacesPhysicalCellRadialSet n).indicator (mixedDerivative r b
          (spacesPhysicalCellJetFunction n (spacesPhysicalFrequencyBand (T.M (T.radius n)) k) u)) p) := by
      rw [div_eq_mul_inv]
      calc
        _ = ((T.M (T.radius n) ^ c)⁻¹ * T.M (T.radius n) ^ c) *
          (T.M (T.radius p.1) ^ c * (iteratedDeriv i (spacesRadialEnvelope n) p.1 *
            (spacesPhysicalCellRadialSet n).indicator (mixedDerivative r b
              (spacesPhysicalCellJetFunction n (spacesPhysicalFrequencyBand (T.M (T.radius n)) k) u)) p)) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hn, one_mul]
    _ = _ := by rw [spacesRadialEnvelope_derivative_mul_indicator]; ring

theorem spacesPhysicalSynthesisRawCoordinate_single_ae (a b c k : ℕ) (n : ℤ) (u : CylinderL2) :
    (spacesPhysicalSynthesisRawCoordinate hT a b c k (lp.single 2 n u) : PolarPoint → ℝ) =ᵐ[
      materialCylinderMeasure] fun p => T.M (T.radius p.1) ^ c *
        mixedDerivative a b (spacesPhysicalPacket n (spacesPhysicalFrequencyBand (T.M (T.radius n)) k) u) p := by
  rw [spacesPhysicalSynthesisRawCoordinate_apply]
  have hi (i : ℕ) :
      (((a.choose i : ℝ) • spacesPhysicalEnvelopeSynthesis hT i c
        (spacesPhysicalSynthesisJetRows hT (a - i) b c (a + b + c) (by omega) k (lp.single 2 n u)) : CylinderL2) :
          PolarPoint → ℝ) =ᵐ[materialCylinderMeasure] fun p =>
        (a.choose i : ℝ) * (T.M (T.radius p.1) ^ c * iteratedDeriv i (spacesRadialEnvelope n) p.1 *
          mixedDerivative (a - i) b (spacesPhysicalCellJetFunction n
            (spacesPhysicalFrequencyBand (T.M (T.radius n)) k) u) p) := by
    filter_upwards [Lp.coeFn_smul (a.choose i : ℝ) (spacesPhysicalEnvelopeSynthesis hT i c
      (spacesPhysicalSynthesisJetRows hT (a - i) b c (a + b + c) (by omega) k (lp.single 2 n u))),
      spacesPhysicalSynthesisTerm_single_ae hT (a - i) b c i (a + b + c) (by omega) k n u]
      with p hp hq
    rw [hp, Pi.smul_apply, smul_eq_mul, hq]
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range (a + 1))
    (fun i => (a.choose i : ℝ) • spacesPhysicalEnvelopeSynthesis hT i c
      (spacesPhysicalSynthesisJetRows hT (a - i) b c (a + b + c) (by omega) k (lp.single 2 n u))),
    ae_all_iff.mpr hi] with p hp hq
  rw [hp]
  unfold spacesPhysicalPacket
  rw [spacesCell_mixedDerivative_radial_mul (spacesRadialEnvelope_contDiff n)
    (spacesPhysicalCellJetFunction_contDiff n _ u), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hq i]
  ring

theorem spacesPhysicalSynthesisCoordinate_single_ae (a b c k : ℕ) (n : ℤ) (u : CylinderL2) :
    (spacesPhysicalSynthesisCoordinate hT a b c k (lp.single 2 n u) : PolarPoint → ℝ) =ᵐ[
      materialCylinderMeasure] fun p => T.M (T.radius p.1) ^ c * mixedDerivative a b
        (spacesCylinderEvenFunction (spacesPhysicalPacket n
          (spacesPhysicalFrequencyBand (T.M (T.radius n)) k) u)) p := by
  have hr := spacesPhysicalSynthesisRawCoordinate_single_ae hT a b c k n u
  have href := measurePreserving_cylinderAngularReflection.quasiMeasurePreserving.ae_eq_comp hr
  filter_upwards [spacesCylinderParity_ae b
    (spacesPhysicalSynthesisRawCoordinate hT a b c k (lp.single 2 n u)), hr, href] with p hp hr href
  simp only [Function.comp_apply, cylinderAngularReflection] at href
  rw [spacesPhysicalSynthesisCoordinate_apply, hp, hr, href,
    spacesCylinderEvenFunction_mixedDerivative (spacesPhysicalPacket_contDiff n _ u)]
  ring

end ContinuousFlexibility.Statements
