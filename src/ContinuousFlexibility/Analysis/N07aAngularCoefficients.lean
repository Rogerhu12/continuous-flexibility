import ContinuousFlexibility.Analysis.N07aAngularFourier
import ContinuousFlexibility.Analysis.N07aAngularCharacters
import ContinuousFlexibility.Analysis.N07aAngularPairing

/-!
# The true weak angular derivative in actual Fourier coordinates

This is the concrete link from the frozen weak graph to the existing
Fourier Hilbert space. The interval area cancels between a source and its
weak derivative, leaving exactly the angular symbol `2 I n`. The radial
Fourier index is arbitrary throughout.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal ContDiff Topology ComplexConjugate

set_option backward.isDefEq.respectTransparency false

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {S : PhysicalSpacesData} {K : CanonicalData S}

def n07aAngularCanonicalWave (m : ℕ) (j : SpacesTorusFrequency) (p : PolarPoint) : ℂ :=
  UnitAddTorus.mFourier j (n07aAngularCellQuotient (K := K) m p)

theorem n07aAngularCanonicalWave_separated (m : ℕ) (j : SpacesTorusFrequency)
    (p : PolarPoint) :
    n07aAngularCanonicalWave (K := K) m j p =
      n07aAngularWave
        (spacesUnitFourierAffine (j 0) (1 / (K.right m - K.left m))
          (-K.left m / (K.right m - K.left m))) (j 1) p := by
  rw [n07aAngularCanonicalWave, n07a_mFourier_finTwo]
  simp only [n07aAngularCellQuotient, Matrix.cons_val_zero, Matrix.cons_val_one,
    n07a_unitFourier_pi, n07aAngularWave, spacesUnitFourierAffine]
  congr 2
  ring

theorem n07aAngularCanonicalWave_contDiff (m : ℕ) (j : SpacesTorusFrequency) :
    ContDiff ℝ ∞ (n07aAngularCanonicalWave (K := K) m j) := by
  have he := funext (n07aAngularCanonicalWave_separated (K := K) m j)
  rw [he]
  exact n07aAngularWave_contDiff (spacesUnitFourierAffine_contDiff _ _ _) _

theorem n07aAngularCanonicalWave_norm (m : ℕ) (j : SpacesTorusFrequency) (p : PolarPoint) :
    ‖n07aAngularCanonicalWave (K := K) m j p‖ = 1 :=
  n07a_mFourier_norm j _

theorem n07aAngularCanonicalWave_chart (m : ℕ) (hm : K.left m < K.right m)
    (j : SpacesTorusFrequency) (t : SpacesTorus) :
    n07aAngularCanonicalWave (K := K) m j (n07aAngularCellChart (K := K) m t) =
      UnitAddTorus.mFourier j t := by
  rw [n07aAngularCanonicalWave, n07aAngularCellQuotient_chart m hm]

theorem n07aAngularFourier_coefficient (m : ℕ) (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) (j : SpacesTorusFrequency) :
    n07aAngularFourier m hm u j =
      (((Real.sqrt (n07aAngularCellArea (K := K) m) *
        (n07aAngularCellArea (K := K) m)⁻¹) : ℝ) : ℂ) *
        ∫ p, n07aAngularCanonicalWave (K := K) m (-j) p * (u p : ℂ)
          ∂canonicalMeasure S K m := by
  let A : ℝ := n07aAngularCellArea (K := K) m
  let F : PolarPoint → ℂ := fun p => n07aAngularCanonicalWave (K := K) m (-j) p * (u p : ℂ)
  have hF : Integrable F (canonicalMeasure S K m) :=
    memLp_one_iff_integrable.mp
      ((n07aCanonicalContinuous_memLp (S := S) (K := K) m
        (n07aAngularCanonicalWave_contDiff m (-j)).continuous).mul (Lp.memLp u).ofReal)
  have hFn : Integrable F (n07aAngularCellMeasure (K := K) m) :=
    hF.smul_measure ENNReal.ofReal_ne_top
  have hc : MeasurePreserving (n07aAngularCellChart (K := K) m)
      (volume : Measure SpacesTorus) (n07aAngularCellMeasure (K := K) m) :=
    n07aAngularCellChart_preserving m hm
  have hmF : AEStronglyMeasurable F
      (Measure.map (n07aAngularCellChart (K := K) m) (volume : Measure SpacesTorus)) := by
    rw [hc.map_eq]
    exact hFn.aestronglyMeasurable
  have hmap := integral_map hc.measurable.aemeasurable hmF
  rw [hc.map_eq] at hmap
  rw [n07aAngularFourier_apply, spacesTorusRealFourier_apply,
    spacesTorusFourier_coefficient, n07a_mFourierCoeff_integral]
  calc
    (∫ t, UnitAddTorus.mFourier (-j) t *
        spacesLpComplexification volume (n07aAngularPhysicalTorusEquiv m hm u) t) =
      (Real.sqrt A : ℂ) * ∫ t, F (n07aAngularCellChart (K := K) m t) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [spacesLpComplexification_ae volume
          (n07aAngularPhysicalTorusEquiv m hm u), n07aAngularPhysicalTorusEquiv_ae m hm u]
          with t hcomplex hreal
        rw [hcomplex, hreal, Complex.ofReal_mul]
        dsimp only [F, A]
        rw [n07aAngularCanonicalWave_chart m hm]
        ring
    _ = (Real.sqrt A : ℂ) * ∫ p, F p ∂n07aAngularCellMeasure (K := K) m := by
      rw [hmap]
    _ = _ := by
      rw [n07aAngularCellMeasure, integral_smul_measure,
        ENNReal.toReal_ofReal (inv_nonneg.mpr (n07aAngularCellArea_pos m hm).le),
        Complex.real_smul, Complex.ofReal_mul]
      dsimp only [A, F]
      ring

/-- Every actual weak angular derivative has the exact Fourier multiplier. -/
theorem n07aAngularWeak_fourier (m : ℕ) (hm : K.left m < K.right m)
    {f g : CanonicalL2 S K m} {k : ℕ}
    (hfg : WeakCanonicalAngularDerivative S K m f g k) (j : SpacesTorusFrequency) :
    n07aAngularFourier m hm g j =
      (2 * Complex.I * (j 1 : ℂ)) ^ k * n07aAngularFourier m hm f j := by
  have h := n07aAngularWeak_fourier_pairing_full m hm hfg
    (spacesUnitFourierAffine_contDiff (-(j 0))
      (1 / (K.right m - K.left m)) (-K.left m / (K.right m - K.left m))) (j 1)
  have hpair :
      (∫ p, n07aAngularCanonicalWave (K := K) m (-j) p * (g p : ℂ)
        ∂canonicalMeasure S K m) =
      (2 * Complex.I * (j 1 : ℂ)) ^ k *
        ∫ p, n07aAngularCanonicalWave (K := K) m (-j) p * (f p : ℂ)
          ∂canonicalMeasure S K m := by
    simpa only [n07aAngularCanonicalWave_separated, Pi.neg_apply] using h
  rw [n07aAngularFourier_coefficient, n07aAngularFourier_coefficient, hpair]
  ring

/-- The weak derivative in the prescribed test class is unique as an
actual canonical `L²` class. -/
theorem n07aAngularWeak_unique (m : ℕ) (hm : K.left m < K.right m)
    {f g h : CanonicalL2 S K m} {k : ℕ}
    (hfg : WeakCanonicalAngularDerivative S K m f g k)
    (hfh : WeakCanonicalAngularDerivative S K m f h k) : g = h := by
  apply (n07aAngularFourier m hm).injective
  apply lp.ext
  funext j
  rw [n07aAngularWeak_fourier m hm hfg j, n07aAngularWeak_fourier m hm hfh j]

theorem n07aAngularGraph_fourier {s : ℕ} {v : CanonicalVolumeJets S K s}
    (hv : v ∈ canonicalVolumeGraph S K s) (m : ℕ) (hm : K.left m < K.right m)
    (k : Fin (s + 1)) (j : SpacesTorusFrequency) :
    n07aAngularFourier m hm (v m k) j =
      (2 * Complex.I * (j 1 : ℂ)) ^ k.val * n07aAngularFourier m hm (v m 0) j :=
  n07aAngularWeak_fourier m hm (hv.2 m k) j

end ContinuousFlexibility.Statements
