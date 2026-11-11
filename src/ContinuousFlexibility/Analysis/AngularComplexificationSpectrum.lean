import ContinuousFlexibility.Analysis.AngularComplexification
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

/-!
# Injectivity, self-adjointness, and real spectrum under complexification

A complex inverse is compressed to the original real space by taking the
real component after applying it to a real-axis vector.  The two inverse
identities follow directly, without an invariant-subspace hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.AngularComplexification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

instance instRealComplexSMulCommClass : SMulCommClass ℝ ℂ (AngularComplexification H) where
  smul_comm r z u := by
    ext <;> simp only [re_real_smul, im_real_smul, re_smul, im_smul] <;> module

instance instComplexRealSMulCommClass : SMulCommClass ℂ ℝ (AngularComplexification H) :=
  SMulCommClass.symm ℝ ℂ (AngularComplexification H)

@[simp] theorem inner_apply (u v : AngularComplexification H) :
    inner ℂ u v = complexInner u v := rfl

/-- A real bounded operator is injective exactly when its complexification is. -/
theorem injective_extend_iff (T : H →L[ℝ] H) :
    Function.Injective (extend T) ↔ Function.Injective T := by
  constructor
  · intro h x y hxy
    apply ofReal.injective
    apply h
    simp only [extend_ofReal, hxy]
  · intro h u v huv
    apply AngularComplexification.ext
    · apply h
      simpa only [re_extend] using congrArg re huv
    · apply h
      simpa only [im_extend] using congrArg im huv

/-- Symmetry is preserved and reflected by the Hermitian extension. -/
theorem isSymmetric_extend_iff (T : H →L[ℝ] H) :
    (extend T).toLinearMap.IsSymmetric ↔ T.toLinearMap.IsSymmetric := by
  constructor
  · intro h x y
    have hxy := congrArg Complex.re (h (ofReal x) (ofReal y))
    simpa only [ContinuousLinearMap.coe_coe, extend_ofReal, inner_apply, complexInner,
      re_ofReal, im_ofReal, inner_zero_left, add_zero] using hxy
  · intro h u v
    have hrr := h u.re v.re
    have hii := h u.im v.im
    have hri := h u.re v.im
    have hir := h u.im v.re
    simp only [ContinuousLinearMap.coe_coe] at hrr hii hri hir ⊢
    apply Complex.ext <;>
      simp only [inner_apply, complexInner, re_extend, im_extend, hrr, hii, hri, hir]

/-- Complexification preserves and reflects self-adjointness. -/
theorem isSelfAdjoint_extend_iff [CompleteSpace H] (T : H →L[ℝ] H) :
    IsSelfAdjoint (extend T) ↔ IsSelfAdjoint T := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric,
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric, isSymmetric_extend_iff]

/-- Real component as a bounded real linear map. -/
def reCLM : AngularComplexification H →L[ℝ] H := WithLp.fstL 2 ℝ H H

@[simp] theorem reCLM_apply (u : AngularComplexification H) : reCLM u = u.re :=
  WithLp.fstL_apply 2 ℝ H H u

/-- Compress a complex operator to the real axis by taking its real component. -/
def realCompression (S : AngularComplexification H →L[ℂ] AngularComplexification H) :
    H →L[ℝ] H :=
  reCLM.comp ((S.restrictScalars ℝ).comp ofReal.toContinuousLinearMap)

@[simp] theorem realCompression_apply
    (S : AngularComplexification H →L[ℂ] AngularComplexification H) (x : H) :
    realCompression S x = (S (ofReal x)).re := by
  unfold realCompression
  simp only [ContinuousLinearMap.comp_apply, reCLM_apply,
    ContinuousLinearMap.coe_restrictScalars', LinearIsometry.coe_toContinuousLinearMap]

@[simp] theorem extend_one : extend (1 : H →L[ℝ] H) = 1 := by
  simpa only [ContinuousLinearMap.one_def] using (extend_id (H := H))

@[simp] theorem extend_mul (S T : H →L[ℝ] H) : extend (S * T) = extend S * extend T := by
  simpa only [ContinuousLinearMap.mul_def] using extend_comp S T

/-- The compressed complex right inverse is a right inverse over the reals. -/
theorem mul_realCompression_eq_one (T : H →L[ℝ] H)
    (S : AngularComplexification H →L[ℂ] AngularComplexification H)
    (h : extend T * S = 1) : T * realCompression S = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun A : AngularComplexification H →L[ℂ] AngularComplexification H =>
    (A (ofReal x)).re) h
  simpa only [mul_apply_eq_comp, one_apply_eq_self, re_extend, re_ofReal,
    realCompression_apply] using hx

/-- The compressed complex left inverse is a left inverse over the reals. -/
theorem realCompression_mul_eq_one (T : H →L[ℝ] H)
    (S : AngularComplexification H →L[ℂ] AngularComplexification H)
    (h : S * extend T = 1) : realCompression S * T = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun A : AngularComplexification H →L[ℂ] AngularComplexification H =>
    (A (ofReal x)).re) h
  simpa only [mul_apply_eq_comp, one_apply_eq_self, extend_ofReal, re_ofReal,
    realCompression_apply] using hx

/-- Invertibility is preserved and reflected by complexification. -/
theorem isUnit_extend_iff (T : H →L[ℝ] H) : IsUnit (extend T) ↔ IsUnit T := by
  constructor
  · intro h
    obtain ⟨S, hright, hleft⟩ := isUnit_iff_exists.mp h
    exact isUnit_iff_exists.mpr ⟨realCompression S,
      mul_realCompression_eq_one T S hright, realCompression_mul_eq_one T S hleft⟩
  · intro h
    obtain ⟨S, hright, hleft⟩ := isUnit_iff_exists.mp h
    refine isUnit_iff_exists.mpr ⟨extend S, ?_, ?_⟩
    · rw [← extend_mul, hright, extend_one]
    · rw [← extend_mul, hleft, extend_one]

/-- Complexification commutes with the real scalar algebra map. -/
theorem extend_algebraMap (r : ℝ) :
    extend (algebraMap ℝ (H →L[ℝ] H) r) =
      algebraMap ℝ (AngularComplexification H →L[ℂ] AngularComplexification H) r := by
  apply ContinuousLinearMap.ext
  intro u
  apply AngularComplexification.ext <;>
    simp only [re_extend, im_extend, ContinuousLinearMap.algebraMap_apply,
      re_real_smul, im_real_smul]

/-- A bounded real operator and its complexification have the same real spectrum. -/
theorem spectrum_real_extend (T : H →L[ℝ] H) : spectrum ℝ (extend T) = spectrum ℝ T := by
  ext r
  rw [spectrum.mem_iff, spectrum.mem_iff, ← extend_algebraMap r, ← extend_sub,
    isUnit_extend_iff]

theorem mem_resolventSet_real_extend_iff (T : H →L[ℝ] H) (r : ℝ) :
    r ∈ resolventSet ℝ (extend T) ↔ r ∈ resolventSet ℝ T := by
  rw [spectrum.mem_resolventSet_iff, spectrum.mem_resolventSet_iff,
    ← extend_algebraMap r, ← extend_sub, isUnit_extend_iff]

end ContinuousFlexibility.Analysis.AngularComplexification
