module

public import ContinuousFlexibility.Analysis.N05CanonicalSmoothJets
public import ContinuousFlexibility.Analysis.SpacesLpOverlap

/-!
# Radial cutoff multiplication on the actual canonical weak derivatives

A smooth bounded radial scalar acts continuously on canonical L². Testing
against its product with a canonical test proves commutation with every
angular weak derivative. Radial multiplication also preserves evenness.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Topology

theorem n05CanonicalTest_mul_radial {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    CanonicalTest S K m (fun p => χ p.1 * φ p) := by
  obtain ⟨J, hJ, hJI, hz⟩ := hφ.2.2
  refine ⟨(hχ.comp contDiff_fst).mul hφ.1, ?_, J, hJ, hJI, ?_⟩
  · intro p
    simp only [Prod.fst_add, add_zero, hφ.2.1 p]
  · intro r hr θ
    simp only [hz r hr θ, mul_zero]

theorem n05CanonicalAngularDerivative_radial_mul (χ : ℝ → ℝ)
    (φ : PolarPoint → ℝ) (j : ℕ) (p : PolarPoint) :
    mixedDerivative 0 j (fun q => χ q.1 * φ q) p =
      χ p.1 * mixedDerivative 0 j φ p := by
  simp only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_const_mul_field]

def n05CanonicalRadialMultiply (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (χ : ℝ → ℝ) (hχ : Continuous χ) (C : ℝ) (hC : ∀ r, |χ r| ≤ C) :
    CanonicalL2 S K m →L[ℝ] CanonicalL2 S K m :=
  spacesLpMultiplier (canonicalMeasure S K m) (fun p => χ p.1)
    (hχ.comp continuous_fst).aestronglyMeasurable C (fun p => hC p.1)

theorem n05CanonicalRadialMultiply_ae (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (χ : ℝ → ℝ) (hχ : Continuous χ) (C : ℝ) (hC : ∀ r, |χ r| ≤ C)
    (u : CanonicalL2 S K m) :
    (n05CanonicalRadialMultiply S K m χ hχ C hC u : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] fun p => χ p.1 * u p :=
  spacesLpMultiplier_ae _ _ _ _ _ u

theorem n05CanonicalRadialMultiply_norm_le (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (χ : ℝ → ℝ) (hχ : Continuous χ) (C : ℝ) (hC : ∀ r, |χ r| ≤ C)
    (u : CanonicalL2 S K m) :
    ‖n05CanonicalRadialMultiply S K m χ hχ C hC u‖ ≤ C * ‖u‖ :=
  spacesLpMultiplier_norm_le _ _ _ _ _ u

theorem n05CanonicalRadialMultiply_even (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (χ : ℝ → ℝ) (hχ : Continuous χ) (C : ℝ) (hC : ∀ r, |χ r| ≤ C)
    (u : CanonicalL2 S K m) (hu : n05CanonicalReflection S K m u = u) :
    n05CanonicalReflection S K m (n05CanonicalRadialMultiply S K m χ hχ C hC u) =
      n05CanonicalRadialMultiply S K m χ hχ C hC u := by
  apply (n05CanonicalReflection_fixed_iff S K m _).mpr
  have hm := n05CanonicalRadialMultiply_ae S K m χ hχ C hC u
  have hr := (n05CanonicalReflection_measurePreserving S K m).quasiMeasurePreserving.ae_eq_comp hm
  have he := (n05CanonicalReflection_fixed_iff S K m u).mp hu
  filter_upwards [hr, hm, he] with p hp hq he
  change n05CanonicalRadialMultiply S K m χ hχ C hC u (p.1, Real.pi - p.2) =
    χ p.1 * u (p.1, Real.pi - p.2) at hp
  exact hp.trans ((congrArg (χ p.1 * ·) he).trans hq.symm)

theorem n05WeakCanonicalAngularDerivative_radialMultiply {S : PhysicalSpacesData}
    {K : CanonicalData S} {m j : ℕ} {f g : CanonicalL2 S K m}
    (h : WeakCanonicalAngularDerivative S K m f g j)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (C : ℝ) (hC : ∀ r, |χ r| ≤ C) :
    WeakCanonicalAngularDerivative S K m
      (n05CanonicalRadialMultiply S K m χ hχ.continuous C hC f)
      (n05CanonicalRadialMultiply S K m χ hχ.continuous C hC g) j := by
  intro φ hφ
  let ψ : PolarPoint → ℝ := fun p => χ p.1 * φ p
  have hψ : CanonicalTest S K m ψ := n05CanonicalTest_mul_radial hφ hχ
  calc
    (∫ p, n05CanonicalRadialMultiply S K m χ hχ.continuous C hC g p * φ p
      ∂canonicalMeasure S K m) =
        ∫ p, g p * ψ p ∂canonicalMeasure S K m := by
      apply integral_congr_ae
      filter_upwards [n05CanonicalRadialMultiply_ae S K m χ hχ.continuous C hC g] with p hp
      rw [hp]
      dsimp only [ψ]
      ring
    _ = (-1 : ℝ) ^ j * ∫ p, f p * mixedDerivative 0 j ψ p ∂canonicalMeasure S K m :=
      h ψ hψ
    _ = (-1 : ℝ) ^ j *
        ∫ p, n05CanonicalRadialMultiply S K m χ hχ.continuous C hC f p *
          mixedDerivative 0 j φ p ∂canonicalMeasure S K m := by
      congr 1
      apply integral_congr_ae
      filter_upwards [n05CanonicalRadialMultiply_ae S K m χ hχ.continuous C hC f] with p hp
      rw [hp, n05CanonicalAngularDerivative_radial_mul]
      ring

theorem n05CanonicalTest_cutoff_cylinder {S : PhysicalSpacesData} {K : CanonicalData S}
    {m : ℕ} {φ : PolarPoint → ℝ} (hφ : IsCylinderTest φ) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo (K.left m) (K.right m)) :
    CanonicalTest S K m (fun p => χ p.1 * φ p) := by
  refine ⟨(hχ.comp contDiff_fst).mul hφ.1, ?_, tsupport χ, hc, hs, ?_⟩
  · intro p
    simp only [Prod.fst_add, add_zero, hφ.2.1 p]
  · intro r hr θ
    change χ r * φ (r, θ) = 0
    rw [image_eq_zero_of_notMem_tsupport hr, zero_mul]

end ContinuousFlexibility.Statements

