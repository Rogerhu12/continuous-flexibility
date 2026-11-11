import ContinuousFlexibility.Analysis.SpacesPhysicalCellBands

/-!
# Smooth representatives of the physical cell jets

Every finite spectral band is represented by a genuine smooth periodic
Fourier polynomial on the material plane. Its actual mixed derivatives
agree almost everywhere with the already constructed cell jet operators.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

local instance spacesPhysicalCellPolynomialsMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance spacesPhysicalCellPolynomialsDecidableFrequency : DecidableEq SpacesTorusFrequency := Classical.decEq _

theorem spaces_mixedDerivative_sum {ι : Type*} {S : Finset ι} {f : ι → PolarPoint → ℝ}
    (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i)) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => ∑ i ∈ S, f i q) p = ∑ i ∈ S, mixedDerivative a b (f i) p := by
  have ha (r : ℝ) : iteratedDeriv b (fun θ => ∑ i ∈ S, f i (r, θ)) p.2 =
      ∑ i ∈ S, iteratedDeriv b (fun θ => f i (r, θ)) p.2 :=
    iteratedDeriv_fun_sum (fun i hi => ((hf i hi).comp
      (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by simp))
  have hs (i : ι) (hi : i ∈ S) : ContDiff ℝ ∞
      (fun r => iteratedDeriv b (fun θ => f i (r, θ)) p.2) := by
    have hslice : ContDiff ℝ ∞ (fun r : ℝ => (r, p.2)) := contDiff_id.prodMk contDiff_const
    have h := (contDiff_mixedDerivative (hf i hi) 0 b).comp hslice
    simpa only [Function.comp_def, mixedDerivative, iteratedDeriv_zero] using h
  unfold mixedDerivative
  simp_rw [ha]
  exact iteratedDeriv_fun_sum (fun i hi => (hs i hi).contDiffAt.of_le (by simp))

/-- A genuine smooth real Fourier polynomial on the material plane. -/
def spacesPhysicalPolynomial (n : ℤ) (S : Finset SpacesTorusFrequency)
    (c : SpacesTorusCoefficients) (p : PolarPoint) : ℝ :=
  ∑ j ∈ S, (c j * spacesPhysicalFourierWave n j p).re

theorem spacesPhysicalPolynomial_contDiff (n : ℤ) (S : Finset SpacesTorusFrequency)
    (c : SpacesTorusCoefficients) : ContDiff ℝ ∞ (spacesPhysicalPolynomial n S c) :=
  ContDiff.sum (fun j _ => Complex.reCLM.contDiff.comp
    (contDiff_const.mul (spacesPhysicalFourierWave_contDiff n j)))

theorem spacesPhysicalPolynomial_periodic (n : ℤ) (S : Finset SpacesTorusFrequency)
    (c : SpacesTorusCoefficients) : Function.Periodic (spacesPhysicalPolynomial n S c) (0, Real.pi) := by
  intro p
  apply Finset.sum_congr rfl
  intro j _
  rw [spacesPhysicalFourierWave_periodic n j p]

theorem spacesPhysicalPolynomial_torus (n : ℤ) (S : Finset SpacesTorusFrequency)
    (c : SpacesTorusCoefficients) (p : PolarPoint) :
    spacesPhysicalPolynomial n S c p =
      (spacesTorusPolynomial S c (spacesPhysicalCellQuotient n p)).re := by
  rw [spacesTorusPolynomial_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [spacesPhysicalFourierWave_quotient]

theorem spacesPhysicalPolynomial_mixedDerivative (n : ℤ) (S : Finset SpacesTorusFrequency)
    (c : SpacesTorusCoefficients) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (spacesPhysicalPolynomial n S c) p =
      (spacesTorusPolynomial S (spacesTorusCoefficientCut S (spacesPhysicalFourierSymbol a b) c)
        (spacesPhysicalCellQuotient n p)).re := by
  change mixedDerivative a b (fun q => ∑ j ∈ S, (c j * spacesPhysicalFourierWave n j q).re) p = _
  have hf (j : SpacesTorusFrequency) (_hj : j ∈ S) :
      ContDiff ℝ ∞ (fun q => (c j * spacesPhysicalFourierWave n j q).re) :=
    Complex.reCLM.contDiff.comp ((contDiff_const (c := c j)).mul (spacesPhysicalFourierWave_contDiff n j))
  rw [spaces_mixedDerivative_sum hf,
    spacesTorusPolynomial_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [spacesPhysicalFourierWave_mixedDerivative, spacesTorusCoefficientCut_apply, ite_eq_left hj,
    ← spacesPhysicalFourierWave_quotient]
  unfold spacesPhysicalFourierSymbol
  congr 1
  ring

/-- The smooth finite polynomial underlying one actual cylinder projection. -/
def spacesPhysicalCellJetFunction (n : ℤ) (S : Finset SpacesTorusFrequency) (u : CylinderL2) :
    PolarPoint → ℝ :=
  spacesPhysicalPolynomial n S (spacesTorusRealFourier (spacesPhysicalCellToTorusL2 n u))

theorem spacesPhysicalCellJetFunction_contDiff (n : ℤ) (S : Finset SpacesTorusFrequency)
    (u : CylinderL2) : ContDiff ℝ ∞ (spacesPhysicalCellJetFunction n S u) :=
  spacesPhysicalPolynomial_contDiff n S _

theorem spacesPhysicalCellJetFunction_periodic (n : ℤ) (S : Finset SpacesTorusFrequency)
    (u : CylinderL2) : Function.Periodic (spacesPhysicalCellJetFunction n S u) (0, Real.pi) :=
  spacesPhysicalPolynomial_periodic n S _

theorem spacesPhysicalCellJet_ae (n : ℤ) (S : Finset SpacesTorusFrequency)
    (a b : ℕ) (u : CylinderL2) :
    (spacesPhysicalCellJet n S a b u : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      (spacesPhysicalCellRadialSet n).indicator
        (mixedDerivative a b (spacesPhysicalCellJetFunction n S u)) := by
  rw [spacesPhysicalCellJet_apply]
  apply spacesPhysicalCellToCylinder_ae_of_ae
  have hp := (spacesPhysicalCellQuotient_preserving n).quasiMeasurePreserving.ae_eq_comp
    (spacesTorusRealCut_ae S (spacesPhysicalFourierSymbol a b) (spacesPhysicalCellToTorusL2 n u))
  filter_upwards [spacesTorusToPhysicalCell_ae ℝ n
    (spacesTorusRealCut S (spacesPhysicalFourierSymbol a b) (spacesPhysicalCellToTorusL2 n u)), hp]
    with p hq hp
  exact hq.trans (hp.trans (spacesPhysicalPolynomial_mixedDerivative n S _ a b p).symm)

theorem spacesCell_mixedDerivative_radial_mul {κ : ℝ → ℝ} {f : PolarPoint → ℝ}
    (hκ : ContDiff ℝ ∞ κ) (hf : ContDiff ℝ ∞ f) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => κ q.1 * f q) p =
      ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) * iteratedDeriv i κ p.1 *
        mixedDerivative (a - i) b f p := by
  have hfr : ContDiff ℝ ∞ (fun r => iteratedDeriv b (fun θ => f (r, θ)) p.2) := by
    have h := (contDiff_mixedDerivative hf 0 b).comp
      (contDiff_id.prodMk (contDiff_const (c := p.2)))
    simpa only [Function.comp_def, id_eq, mixedDerivative, iteratedDeriv_zero] using h
  unfold mixedDerivative
  simp_rw [iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_fun_mul (hκ.contDiffAt.of_le (by simp)) (hfr.contDiffAt.of_le (by simp))]

end ContinuousFlexibility.Statements
