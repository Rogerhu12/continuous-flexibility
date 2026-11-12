import ContinuousFlexibility.Analysis.N05CanonicalSymmetryLimits

/-!
# Even canonical tests approximating every finite angular weak jet

First cut off inside the actual radial interval. Mollify the zero
extension, take its even average, and multiply by a wider radial plateau.
These are actual smooth periodic even canonical tests. Every ordinary
angular derivative converges strongly to the corresponding cutoff weak
derivative. The identification uses closedness and uniqueness of the
actual weak derivative, with no parity or density premise.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Topology

def n05CanonicalEvenCutoffMollification (S : PhysicalSpacesData)
    (K : CanonicalData S) (m n : ℕ) (f : CanonicalL2 S K m) (k : ℕ) : PolarPoint → ℝ :=
  fun p => n05CanonicalRadialCutoffFunction (K.left m) (K.right m) (2 * n + 1) p.1 *
    spacesCylinderEvenFunction (n05CanonicalCylinderMollification
      (n05CanonicalZeroExtension S K m (n05CanonicalRadialCutoffOperator S K m n f))
      (spacesMollifierBump k)) p

theorem n05CanonicalEvenCutoffMollification_contDiff (S : PhysicalSpacesData)
    (K : CanonicalData S) (m n : ℕ) (f : CanonicalL2 S K m) (k : ℕ) :
    ContDiff ℝ ∞ (n05CanonicalEvenCutoffMollification S K m n f k) :=
  ((n05CanonicalRadialCutoffFunction_contDiff _ _ _).comp contDiff_fst).mul
    (spacesCylinderEvenFunction_contDiff (n05CanonicalCylinderMollification_contDiff _ _))

theorem n05CanonicalEvenCutoffMollification_periodic (S : PhysicalSpacesData)
    (K : CanonicalData S) (m n : ℕ) (f : CanonicalL2 S K m) (k : ℕ) :
    Function.Periodic (n05CanonicalEvenCutoffMollification S K m n f k) (0, Real.pi) := by
  have hp := spacesCylinderEvenFunction_periodic
    (n05CanonicalCylinderMollification_periodic
      (n05CanonicalZeroExtension S K m (n05CanonicalRadialCutoffOperator S K m n f))
      (spacesMollifierBump k))
  intro p
  simp only [n05CanonicalEvenCutoffMollification, Prod.fst_add, add_zero, hp p]

theorem n05CanonicalEvenCutoffMollification_even (S : PhysicalSpacesData)
    (K : CanonicalData S) (m n : ℕ) (f : CanonicalL2 S K m) (k : ℕ) (p : PolarPoint) :
    n05CanonicalEvenCutoffMollification S K m n f k (p.1, Real.pi - p.2) =
      n05CanonicalEvenCutoffMollification S K m n f k p := by
  simp only [n05CanonicalEvenCutoffMollification, spacesCylinderEvenFunction_reflection]

theorem n05CanonicalEvenCutoffMollification_test (S : PhysicalSpacesData)
    (K : CanonicalData S) (m n : ℕ) (f : CanonicalL2 S K m) (k : ℕ) :
    CanonicalTest S K m (n05CanonicalEvenCutoffMollification S K m n f k) := by
  refine ⟨n05CanonicalEvenCutoffMollification_contDiff S K m n f k,
    n05CanonicalEvenCutoffMollification_periodic S K m n f k,
    tsupport (n05CanonicalRadialCutoffFunction (K.left m) (K.right m) (2 * n + 1)),
    n05CanonicalRadialCutoffFunction_hasCompactSupport _ _ _,
    n05CanonicalRadialCutoffFunction_tsupport_subset _ _ _, ?_⟩
  intro r hr θ
  simp only [n05CanonicalEvenCutoffMollification, image_eq_zero_of_notMem_tsupport hr, zero_mul]

theorem n05CanonicalEvenCutoffMollification_jet (S : PhysicalSpacesData)
    (K : CanonicalData S) (m n : ℕ) (f : CanonicalL2 S K m) (k j : ℕ) :
    n05CanonicalSmoothJet S K m
      (n05CanonicalEvenCutoffMollification_contDiff S K m n f k) j =
        n05CanonicalRadialCutoffOperator S K m (2 * n + 1)
          (n05CanonicalSignedProjection S K m j
            (n05CanonicalMollifiedJet S K m
              (n05CanonicalZeroExtension S K m (n05CanonicalRadialCutoffOperator S K m n f))
              (spacesMollifierBump k) 0 j)) := by
  let u := n05CanonicalZeroExtension S K m (n05CanonicalRadialCutoffOperator S K m n f)
  let χ := n05CanonicalRadialCutoffFunction (K.left m) (K.right m) (2 * n + 1)
  have hχ : ContDiff ℝ ∞ χ := n05CanonicalRadialCutoffFunction_contDiff _ _ _
  have hf := n05CanonicalCylinderMollification_contDiff u (spacesMollifierBump k)
  change n05CanonicalSmoothJet S K m
    ((hχ.comp contDiff_fst).mul (spacesCylinderEvenFunction_contDiff hf)) j = _
  rw [n05CanonicalSmoothJet_radial_mul S K m (spacesCylinderEvenFunction_contDiff hf)
    j χ hχ 1 (n05CanonicalRadialCutoffFunction_abs_le _ _ _),
    n05CanonicalSmoothJet_even S K m hf j]
  rfl

theorem n05CanonicalEvenCutoffMollification_jet_tendsto_signed
    (S : PhysicalSpacesData) (K : CanonicalData S) (m n : ℕ)
    {f g : CanonicalL2 S K m} {j : ℕ}
    (h : WeakCanonicalAngularDerivative S K m f g j) :
    Tendsto (fun k => n05CanonicalSmoothJet S K m
      (n05CanonicalEvenCutoffMollification_contDiff S K m n f k) j) atTop
      (𝓝 (n05CanonicalRadialCutoffOperator S K m (2 * n + 1)
        (n05CanonicalSignedProjection S K m j (n05CanonicalRadialCutoffOperator S K m n g)))) := by
  have ht := n05CanonicalMollifiedCutoffAngularJet_tendsto S K m n h
  have hs := (n05CanonicalSignedProjection S K m j).continuous.tendsto
    (n05CanonicalRadialCutoffOperator S K m n g) |>.comp ht
  have hr := (n05CanonicalRadialCutoffOperator S K m (2 * n + 1)).continuous.tendsto
    (n05CanonicalSignedProjection S K m j (n05CanonicalRadialCutoffOperator S K m n g)) |>.comp hs
  simpa only [Function.comp_def, n05CanonicalEvenCutoffMollification_jet] using hr

theorem n05CanonicalEvenCutoffMollification_zero_tendsto
    (S : PhysicalSpacesData) (K : CanonicalData S) (m n : ℕ)
    (f : CanonicalL2 S K m) (heven : n05CanonicalReflection S K m f = f) :
    Tendsto (fun k => n05CanonicalSmoothJet S K m
      (n05CanonicalEvenCutoffMollification_contDiff S K m n f k) 0) atTop
      (𝓝 (n05CanonicalRadialCutoffOperator S K m n f)) := by
  have hzero : WeakCanonicalAngularDerivative S K m f f 0 := by
    intro φ hφ
    simp only [pow_zero, one_mul, mixedDerivative, iteratedDeriv_zero, Prod.eta]
  have he :
      n05CanonicalSignedProjection S K m 0 (n05CanonicalRadialCutoffOperator S K m n f) =
        n05CanonicalRadialCutoffOperator S K m n f := by
    rw [n05CanonicalSignedProjection_zero]
    exact n05CanonicalEvenProjection_fixed S K m _
      (n05CanonicalRadialCutoffOperator_even S K m n f heven)
  simpa only [he, n05CanonicalRadialCutoffOperator_plateau] using
    n05CanonicalEvenCutoffMollification_jet_tendsto_signed S K m n hzero

theorem n05CanonicalEvenCutoffMollification_jet_tendsto
    (S : PhysicalSpacesData) (K : CanonicalData S) (m n : ℕ)
    {f g : CanonicalL2 S K m} {j : ℕ}
    (heven : n05CanonicalReflection S K m f = f)
    (h : WeakCanonicalAngularDerivative S K m f g j) :
    Tendsto (fun k => n05CanonicalSmoothJet S K m
      (n05CanonicalEvenCutoffMollification_contDiff S K m n f k) j) atTop
      (𝓝 (n05CanonicalRadialCutoffOperator S K m n g)) := by
  have ht := n05CanonicalEvenCutoffMollification_jet_tendsto_signed S K m n h
  have hw := n05WeakCanonicalAngularDerivative_of_tendsto
    (n05CanonicalEvenCutoffMollification_zero_tendsto S K m n f heven) ht
    (fun k => n05CanonicalSmoothJet_weak S K m
      (n05CanonicalEvenCutoffMollification_contDiff S K m n f k)
      (n05CanonicalEvenCutoffMollification_periodic S K m n f k) j)
  have he := n05WeakCanonicalAngularDerivative_unique hw
    (n05WeakCanonicalAngularDerivative_radialCutoff h n)
  simpa only [he] using ht

end ContinuousFlexibility.Statements
