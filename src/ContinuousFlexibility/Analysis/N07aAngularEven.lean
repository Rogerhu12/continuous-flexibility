import ContinuousFlexibility.Analysis.N07aAngularCoefficients
import ContinuousFlexibility.Analysis.CylinderTestPairing

/-!
# Actual angular reflection and canonical Fourier parity

Reflection uses the exact involution appearing in `canonicalVolumeGraph`.
It preserves the canonical measure and becomes reflection of only the
angular Fourier index. The radial index remains unrestricted.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

def n07aAngularFrequencyReflection (j : SpacesTorusFrequency) : SpacesTorusFrequency :=
  ![j 0, -(j 1)]

@[simp] theorem n07aAngularFrequencyReflection_zero (j : SpacesTorusFrequency) :
    n07aAngularFrequencyReflection j 0 = j 0 := by
  simp only [n07aAngularFrequencyReflection, Matrix.cons_val_zero]

@[simp] theorem n07aAngularFrequencyReflection_one (j : SpacesTorusFrequency) :
    n07aAngularFrequencyReflection j 1 = -(j 1) := by
  simp only [n07aAngularFrequencyReflection, Matrix.cons_val_one, Matrix.cons_val_zero]

theorem n07aAngularFrequencyReflection_involutive (j : SpacesTorusFrequency) :
    n07aAngularFrequencyReflection (n07aAngularFrequencyReflection j) = j := by
  funext i
  fin_cases i <;> simp [n07aAngularFrequencyReflection]

theorem n07aAngularFrequencyReflection_neg (j : SpacesTorusFrequency) :
    n07aAngularFrequencyReflection (-j) = -n07aAngularFrequencyReflection j := by
  funext i
  fin_cases i <;> simp [n07aAngularFrequencyReflection]

theorem n07aCircleFourierWave_reflection (n : ℤ) (θ : ℝ) :
    circleFourierWave n (Real.pi - θ) = circleFourierWave (-n) θ := by
  rw [show Real.pi - θ = -θ + Real.pi by ring, circleFourierWave_periodic]
  simp only [circleFourierWave, fourier_coe_apply, Complex.ofReal_neg, Int.cast_neg]
  congr 1
  ring

variable {S : PhysicalSpacesData} {K : CanonicalData S}

theorem n07aAngularCanonicalWave_reflection (m : ℕ) (j : SpacesTorusFrequency)
    (p : PolarPoint) :
    n07aAngularCanonicalWave (K := K) m j (cylinderAngularReflection p) =
      n07aAngularCanonicalWave (K := K) m (n07aAngularFrequencyReflection j) p := by
  rw [n07aAngularCanonicalWave_separated, n07aAngularCanonicalWave_separated]
  simp only [n07aAngularWave, cylinderAngularReflection,
    n07aAngularFrequencyReflection_zero, n07aAngularFrequencyReflection_one,
    n07aCircleFourierWave_reflection]

theorem n07aCanonicalMeasure_eq_prod (S : PhysicalSpacesData) (K : CanonicalData S) (m : ℕ) :
    canonicalMeasure S K m =
      (volume.restrict (Ioo (K.left m) (K.right m))).prod angleMeasure := by
  rw [canonicalMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict]
  rfl

theorem n07aAngularReflection_preserving (m : ℕ) :
    MeasurePreserving cylinderAngularReflection (canonicalMeasure S K m) (canonicalMeasure S K m) := by
  let : SFinite angleMeasure := by unfold angleMeasure; infer_instance
  rw [n07aCanonicalMeasure_eq_prod]
  exact (MeasurePreserving.id (volume.restrict (Ioo (K.left m) (K.right m)))).prod
    measurePreserving_angleReflection

def n07aAngularReflection (m : ℕ) : CanonicalL2 S K m →ₗᵢ[ℝ] CanonicalL2 S K m :=
  Lp.compMeasurePreservingₗᵢ ℝ cylinderAngularReflection (n07aAngularReflection_preserving m)

theorem n07aAngularReflection_ae (m : ℕ) (u : CanonicalL2 S K m) :
    (n07aAngularReflection m u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => u (p.1, Real.pi - p.2) :=
  Lp.coeFn_compMeasurePreserving u (n07aAngularReflection_preserving m)

theorem n07aAngularReflection_fixed_iff (m : ℕ) (u : CanonicalL2 S K m) :
    n07aAngularReflection m u = u ↔
      (fun p : PolarPoint => u (p.1, Real.pi - p.2)) =ᵐ[canonicalMeasure S K m] u := by
  constructor
  · intro h
    have he := n07aAngularReflection_ae m u
    rw [h] at he
    exact he.symm
  · intro h
    exact Lp.ext ((n07aAngularReflection_ae m u).trans h)

theorem n07aAngularReflection_fourier (m : ℕ) (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) (j : SpacesTorusFrequency) :
    n07aAngularFourier m hm (n07aAngularReflection m u) j =
      n07aAngularFourier m hm u (n07aAngularFrequencyReflection j) := by
  let F : PolarPoint → ℂ := fun p =>
    n07aAngularCanonicalWave (K := K) m (-n07aAngularFrequencyReflection j) p * (u p : ℂ)
  have hF : Integrable F (canonicalMeasure S K m) :=
    memLp_one_iff_integrable.mp
      ((n07aCanonicalContinuous_memLp (S := S) (K := K) m
        (n07aAngularCanonicalWave_contDiff m _).continuous).mul (Lp.memLp u).ofReal)
  have hpres := n07aAngularReflection_preserving (S := S) (K := K) m
  have hFm : AEStronglyMeasurable F
      (Measure.map cylinderAngularReflection (canonicalMeasure S K m)) := by
    rw [hpres.map_eq]
    exact hF.aestronglyMeasurable
  have hmap := integral_map hpres.measurable.aemeasurable hFm
  rw [hpres.map_eq] at hmap
  rw [n07aAngularFourier_coefficient, n07aAngularFourier_coefficient]
  congr 1
  calc
    (∫ p, n07aAngularCanonicalWave (K := K) m (-j) p *
        (n07aAngularReflection m u p : ℂ) ∂canonicalMeasure S K m) =
        ∫ p, F (cylinderAngularReflection p) ∂canonicalMeasure S K m := by
      apply integral_congr_ae
      filter_upwards [n07aAngularReflection_ae m u] with p hp
      simp only [F, n07aAngularCanonicalWave_reflection,
        n07aAngularFrequencyReflection_neg, n07aAngularFrequencyReflection_involutive]
      exact congrArg (fun x : ℝ => n07aAngularCanonicalWave (K := K) m (-j) p * (x : ℂ)) hp
    _ = ∫ p, F p ∂canonicalMeasure S K m := hmap.symm

/-- The frozen reflection condition is exactly even angular Fourier parity. -/
theorem n07aAngularEven_fourier_iff (m : ℕ) (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) :
    ((fun p : PolarPoint => u (p.1, Real.pi - p.2)) =ᵐ[canonicalMeasure S K m] u) ↔
      ∀ j : SpacesTorusFrequency,
        n07aAngularFourier m hm u (n07aAngularFrequencyReflection j) = n07aAngularFourier m hm u j := by
  rw [← n07aAngularReflection_fixed_iff]
  constructor
  · intro hu j
    have h := congrArg (fun v : CanonicalL2 S K m => n07aAngularFourier m hm v j) hu
    simpa only [n07aAngularReflection_fourier] using h
  · intro hu
    apply (n07aAngularFourier m hm).injective
    apply lp.ext
    funext j
    rw [n07aAngularReflection_fourier]
    exact hu j

end ContinuousFlexibility.Statements
