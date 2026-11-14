module

public import ContinuousFlexibility.Analysis.N07aAngularCell
public import ContinuousFlexibility.Analysis.N07aAngularLpScale
public import ContinuousFlexibility.Analysis.SpacesTorusCut

/-!
# Fourier coordinates of the actual canonical source classes

Each prescribed canonical interval has its own area. The exact isometry
below includes that area before applying the existing torus Fourier
isometry. Its outer `lp` version therefore retains all radial pieces and
their actual norms. The range still records real-valuedness; no complex
source or finite-dimensional radial reduction is introduced.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal BigOperators ComplexConjugate

set_option backward.isDefEq.respectTransparency false

variable {S : PhysicalSpacesData} {K : CanonicalData S}

/-- The actual unnormalized canonical `L²` class in normalized torus coordinates. -/
def n07aAngularPhysicalTorusEquiv (m : ℕ) (hm : K.left m < K.right m) :
    CanonicalL2 S K m ≃ₗᵢ[ℝ] SpacesTorusRealL2 :=
  (n07aAngularLpScaleEquiv (canonicalMeasure S K m)
    (n07aAngularCellArea (K := K) m) (n07aAngularCellArea_pos m hm)).trans
      (n07aAngularCellTorusEquiv ℝ m hm)

@[simp] theorem n07aAngularPhysicalTorusEquiv_apply (m : ℕ)
    (hm : K.left m < K.right m) (u : CanonicalL2 S K m) :
    n07aAngularPhysicalTorusEquiv m hm u = n07aAngularCellToTorus ℝ m hm
      (n07aAngularLpScaleEquiv (canonicalMeasure S K m)
        (n07aAngularCellArea (K := K) m) (n07aAngularCellArea_pos m hm) u) := rfl

theorem n07aAngularPhysicalTorusEquiv_ae (m : ℕ) (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) :
    (n07aAngularPhysicalTorusEquiv m hm u : SpacesTorus → ℝ) =ᵐ[
      Measure.pi (fun _ : Fin 2 => AddCircle.haarAddCircle)]
      fun t => Real.sqrt (n07aAngularCellArea (K := K) m) *
        u (n07aAngularCellChart (K := K) m t) := by
  rw [n07aAngularPhysicalTorusEquiv_apply]
  have hscale := (n07aAngularCellChart_preserving m hm).quasiMeasurePreserving.ae_eq_comp
    (n07aAngularLpScaleEquiv_ae (canonicalMeasure S K m)
      (n07aAngularCellArea (K := K) m) (n07aAngularCellArea_pos m hm) u)
  exact (n07aAngularCellToTorus_ae ℝ m hm _).trans hscale

/-- Actual real canonical data embedded isometrically in complex Fourier coordinates. -/
def n07aAngularFourier (m : ℕ) (hm : K.left m < K.right m) :
    CanonicalL2 S K m →ₗᵢ[ℝ] SpacesTorusCoefficients where
  toFun u := spacesTorusRealFourier (n07aAngularPhysicalTorusEquiv m hm u)
  map_add' := by intro u v; rw [map_add, map_add]
  map_smul' := by intro c u; rw [map_smul, map_smul]; rfl
  norm_map' := by
    intro u
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [spacesTorusRealFourier_norm, LinearIsometryEquiv.norm_map]

@[simp] theorem n07aAngularFourier_apply (m : ℕ) (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) :
    n07aAngularFourier m hm u =
      spacesTorusRealFourier (n07aAngularPhysicalTorusEquiv m hm u) := rfl

theorem n07aAngularFourier_neg (m : ℕ) (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) (j : SpacesTorusFrequency) :
    n07aAngularFourier m hm u (-j) = conj (n07aAngularFourier m hm u j) :=
  spacesTorusRealFourier_neg _ j

theorem n07aAngularFourier_norm_sq (m : ℕ) (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) :
    ‖u‖ ^ 2 = ∑' j : SpacesTorusFrequency, ‖n07aAngularFourier m hm u j‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (n07aAngularFourier m hm u)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometry.norm_map] using h

/-- One coefficient Hilbert space for every actual radial component. -/
abbrev N07aAngularCoefficientFamily := lp (fun _ : ℕ => SpacesTorusCoefficients) 2

private def n07aAngularFamilyFourierFun (hK : ∀ m, K.left m < K.right m)
    (u : CanonicalL2Sequence S K) : N07aAngularCoefficientFamily :=
  ⟨fun m => n07aAngularFourier m (hK m) (u m),
    (lp.memℓp u).mono' (fun m => ((n07aAngularFourier m (hK m)).norm_map (u m)).le)⟩

private theorem n07aAngularFamilyFourierFun_apply (hK : ∀ m, K.left m < K.right m)
    (u : CanonicalL2Sequence S K) (m : ℕ) :
    n07aAngularFamilyFourierFun hK u m = n07aAngularFourier m (hK m) (u m) := rfl

private theorem n07aAngularFamilyFourierFun_norm (hK : ∀ m, K.left m < K.right m)
    (u : CanonicalL2Sequence S K) : ‖n07aAngularFamilyFourierFun hK u‖ = ‖u‖ := by
  apply le_antisymm
  · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro m
    rw [n07aAngularFamilyFourierFun_apply, LinearIsometry.norm_map]
  · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro m
    rw [n07aAngularFamilyFourierFun_apply, LinearIsometry.norm_map]

/-- Simultaneous Fourier analysis on all canonical radial components. -/
def n07aAngularFamilyFourier (hK : ∀ m, K.left m < K.right m) :
    CanonicalL2Sequence S K →ₗᵢ[ℝ] N07aAngularCoefficientFamily where
  toFun := n07aAngularFamilyFourierFun hK
  map_add' := by
    intro u v
    apply lp.ext
    funext m
    simp only [n07aAngularFamilyFourierFun_apply, lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' := by
    intro c u
    apply lp.ext
    funext m
    simp only [n07aAngularFamilyFourierFun_apply, lp.coeFn_smul, Pi.smul_apply,
      map_smul, RingHom.id_apply]
  norm_map' := n07aAngularFamilyFourierFun_norm hK

@[simp] theorem n07aAngularFamilyFourier_apply (hK : ∀ m, K.left m < K.right m)
    (u : CanonicalL2Sequence S K) (m : ℕ) :
    n07aAngularFamilyFourier hK u m = n07aAngularFourier m (hK m) (u m) :=
  n07aAngularFamilyFourierFun_apply hK u m

theorem n07aAngularFamilyFourier_neg (hK : ∀ m, K.left m < K.right m)
    (u : CanonicalL2Sequence S K) (m : ℕ) (j : SpacesTorusFrequency) :
    n07aAngularFamilyFourier hK u m (-j) = conj (n07aAngularFamilyFourier hK u m j) :=
  n07aAngularFourier_neg m (hK m) (u m) j

end ContinuousFlexibility.Statements
