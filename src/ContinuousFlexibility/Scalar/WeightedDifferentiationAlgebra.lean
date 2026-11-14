module

public import ContinuousFlexibility.Scalar.WeightedDifferentiationSupport

/-!
# Linearity of the actual supported derivatives

Ordinary derivative linearity is used where the input fields are smooth.
Outside the annulus every relevant actual partial is zero by support.
This gives honest linear field maps for every weight exponent.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {f g : PolarPoint → ℝ}

theorem scalar_coordinatePartials_add
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hg : ContDiffOn ℝ ∞ g (annularOpen D))
    (hzeroF : ∀ p, p ∉ annularOpen D → f p = 0)
    (hzeroG : ∀ p, p ∉ annularOpen D → g p = 0) :
    radialPartial (fun p => f p + g p) = (fun p => radialPartial f p + radialPartial g p) ∧
    angularPartial (fun p => f p + g p) = (fun p => angularPartial f p + angularPartial g p) := by
  have hpoint (p : PolarPoint) :
      radialPartial (fun q => f q + g q) p = radialPartial f p + radialPartial g p ∧
      angularPartial (fun q => f q + g q) p = angularPartial f p + angularPartial g p := by
    by_cases hp : p ∈ annularOpen D
    · have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
      have hdf := (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
      have hdg := (hg.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
      exact ⟨radialPartial_add hdf hdg, angularPartial_add hdf hdg⟩
    · have hz : ∀ q, q ∉ annularOpen D → f q + g q = 0 := by
        intro q hq
        rw [hzeroF q hq, hzeroG q hq, add_zero]
      have hsum := scalar_coordinatePartials_zero_outside hz p hp
      have hF := scalar_coordinatePartials_zero_outside hzeroF p hp
      have hG := scalar_coordinatePartials_zero_outside hzeroG p hp
      simp only [hsum.1, hsum.2, hF.1, hF.2, hG.1, hG.2, add_zero, and_self]
  exact ⟨funext (fun p => (hpoint p).1), funext (fun p => (hpoint p).2)⟩

theorem scalar_coordinatePartials_const_mul
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hzero : ∀ p, p ∉ annularOpen D → f p = 0) (c : ℝ) :
    radialPartial (fun p => c * f p) = (fun p => c * radialPartial f p) ∧
    angularPartial (fun p => c * f p) = (fun p => c * angularPartial f p) := by
  have hpoint (p : PolarPoint) :
      radialPartial (fun q => c * f q) p = c * radialPartial f p ∧
      angularPartial (fun q => c * f q) p = c * angularPartial f p := by
    by_cases hp : p ∈ annularOpen D
    · have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
      have hdf := (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
      constructor
      · simpa only [radialPartial_const, zero_mul, zero_add] using
          radialPartial_mul (differentiableAt_const c) hdf
      · simpa only [angularPartial_const, zero_mul, zero_add] using
          angularPartial_mul (differentiableAt_const c) hdf
    · have hz : ∀ q, q ∉ annularOpen D → c * f q = 0 := by
        intro q hq
        rw [hzero q hq, mul_zero]
      have hprod := scalar_coordinatePartials_zero_outside hz p hp
      have hF := scalar_coordinatePartials_zero_outside hzero p hp
      simp only [hprod.1, hprod.2, hF.1, hF.2, mul_zero, and_self]
  exact ⟨funext (fun p => (hpoint p).1), funext (fun p => (hpoint p).2)⟩

theorem scalar_angularPartial_twice_add
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hg : ContDiffOn ℝ ∞ g (annularOpen D))
    (hzeroF : ∀ p, p ∉ annularOpen D → f p = 0)
    (hzeroG : ∀ p, p ∉ annularOpen D → g p = 0) :
    angularPartial (angularPartial (fun p => f p + g p)) =
      fun p => angularPartial (angularPartial f) p + angularPartial (angularPartial g) p := by
  rw [(scalar_coordinatePartials_add hf hg hzeroF hzeroG).2]
  exact (scalar_coordinatePartials_add
    (scalar_contDiffOn_angularPartial (isOpen_Ioo.prod isOpen_univ) hf)
    (scalar_contDiffOn_angularPartial (isOpen_Ioo.prod isOpen_univ) hg)
    (fun p hp => (scalar_coordinatePartials_zero_outside hzeroF p hp).2)
    (fun p hp => (scalar_coordinatePartials_zero_outside hzeroG p hp).2)).2

theorem scalar_angularPartial_twice_const_mul
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hzero : ∀ p, p ∉ annularOpen D → f p = 0) (c : ℝ) :
    angularPartial (angularPartial (fun p => c * f p)) =
      fun p => c * angularPartial (angularPartial f) p := by
  rw [(scalar_coordinatePartials_const_mul hf hzero c).2]
  exact (scalar_coordinatePartials_const_mul
    (scalar_contDiffOn_angularPartial (isOpen_Ioo.prod isOpen_univ) hf)
    (fun p hp => (scalar_coordinatePartials_zero_outside hzero p hp).2) c).2

namespace SobolevModelData

variable {T : MaterialData} {γ : ℝ} {A : SobolevModelData}

/-- The actual radial derivative of the decoder is linear on the given
physical Sobolev model. -/
def radialFieldLinear (hA : IsSobolevModel D T γ A) :
    A.Space →ₗ[ℝ] (PolarPoint → ℝ) where
  toFun := fun u => radialPartial (A.decode u)
  map_add' := by
    intro u v
    simp only [map_add]
    exact (scalar_coordinatePartials_add (hA.2.2.2.1 u).1 (hA.2.2.2.1 v).1
      (hA.2.2.2.1 u).2.2.2.1 (hA.2.2.2.1 v).2.2.2.1).1
  map_smul' := by
    intro c u
    have he : A.decode (c • u) = fun p => c * A.decode u p := by
      funext p
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    rw [he]
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact congrFun (scalar_coordinatePartials_const_mul (hA.2.2.2.1 u).1
      (hA.2.2.2.1 u).2.2.2.1 c).1 p

theorem radialFieldLinear_apply (hA : IsSobolevModel D T γ A) (u : A.Space) :
    radialFieldLinear hA u = radialPartial (A.decode u) := rfl

/-- Taking two actual angular derivatives preserves the even field space. -/
def angularSecondFieldLinear (hA : IsSobolevModel D T γ A) :
    A.Space →ₗ[ℝ] (PolarPoint → ℝ) where
  toFun := fun u => angularPartial (angularPartial (A.decode u))
  map_add' := by
    intro u v
    simp only [map_add]
    exact scalar_angularPartial_twice_add (hA.2.2.2.1 u).1 (hA.2.2.2.1 v).1
      (hA.2.2.2.1 u).2.2.2.1 (hA.2.2.2.1 v).2.2.2.1
  map_smul' := by
    intro c u
    have he : A.decode (c • u) = fun p => c * A.decode u p := by
      funext p
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    rw [he]
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact congrFun (scalar_angularPartial_twice_const_mul (hA.2.2.2.1 u).1
      (hA.2.2.2.1 u).2.2.2.1 c) p

theorem angularSecondFieldLinear_apply (hA : IsSobolevModel D T γ A) (u : A.Space) :
    angularSecondFieldLinear hA u = angularPartial (angularPartial (A.decode u)) := rfl

end SobolevModelData

end ContinuousFlexibility.Statements
