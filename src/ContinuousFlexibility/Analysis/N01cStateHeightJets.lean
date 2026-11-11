import ContinuousFlexibility.Analysis.N01cPhysicalHeightJets
import ContinuousFlexibility.Analysis.MaterialHeightRegularity

/-!
# Continuous-linear physical jets of the actual state height direction

The state direction is exactly the decoded physical height plus the scalar
left cutoff.  Its physical mixed derivatives therefore combine the proved
height-jet functionals with the scalar coordinate.  The five polar inputs
needed by the nonlinear coefficient formula are obtained by the actual
coordinate differentiation and quotient rules.  Their parameter towers
are defined on the full joint state/real-parameter space.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem smooth_actualStateU
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (x : AnnularState S) :
    ContDiff ℝ ∞ (stateU S x) :=
  physical_height_with_cutoff_contDiff hT hS (by norm_num : (0 : ℝ) < 3 / 4) x.1.1 x.1.2

/-- Mixed jets of the cutoff are zero as soon as an angular derivative is
taken; the remaining jets are its ordinary radial derivatives. -/
theorem mixedDerivative_radialFunction (f : ℝ → ℝ) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q : PolarPoint => f q.1) p =
      if b = 0 then iteratedDeriv a f p.1 else 0 := by
  by_cases hb : b = 0
  · subst b
    simp only [mixedDerivative, iteratedDeriv_zero, if_pos rfl]
  · simp only [mixedDerivative, iteratedDeriv_const, if_neg hb, ite_self]

/-- Exact physical jets of the state direction, including the scalar cutoff
coordinate of `HeightPair`. -/
theorem mixedDerivative_stateU
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (a b : ℕ) (p : PolarPoint) (x : AnnularState S) :
    mixedDerivative a b (stateU S x) p =
      mixedDerivative a b ((S.height (3 / 4 : ℝ)).decode x.1.1) p +
        x.1.2 * (if b = 0 then iteratedDeriv a S.chiLeft p.1 else 0) := by
  change mixedDerivative a b
    (fun q => (S.height (3 / 4 : ℝ)).decode x.1.1 q + x.1.2 * S.chiLeft q.1) p = _
  rw [mixedDerivative_add_of_contDiff
    (physical_height_contDiff_and_flatJets hT hS
      (by norm_num : (0 : ℝ) < 3 / 4) x.1.1).1
    (contDiff_const.mul (hS.2.2.1.1.comp contDiff_fst)),
    mixedDerivative_const_mul, mixedDerivative_radialFunction]

/-- Projection onto the decoded height component of the actual state. -/
def statePhysicalHeightCLM (S : PhysicalSpacesData) :
    AnnularState S →L[ℝ] (S.height (3 / 4 : ℝ)).Space :=
  (ContinuousLinearMap.fst ℝ (S.height (3 / 4 : ℝ)).Space ℝ).comp
    (ContinuousLinearMap.fst ℝ (HeightPair S) (ℝ × (CircleSpace S × CircleSpace S)))

/-- Projection onto the scalar left-height coordinate. -/
def stateLeftHeightCLM (S : PhysicalSpacesData) : AnnularState S →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ (S.height (3 / 4 : ℝ)).Space ℝ).comp
    (ContinuousLinearMap.fst ℝ (HeightPair S) (ℝ × (CircleSpace S × CircleSpace S)))

theorem statePhysicalHeightCLM_apply (S : PhysicalSpacesData) (x : AnnularState S) :
    statePhysicalHeightCLM S x = x.1.1 := rfl

theorem stateLeftHeightCLM_apply (S : PhysicalSpacesData) (x : AnnularState S) :
    stateLeftHeightCLM S x = x.1.2 := rfl

/-- A physical jet of the complete state direction is a finite linear
combination of the decoded-height jet and its cutoff coordinate. -/
def stateUJetCLM
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    AnnularState S →L[ℝ] ℝ :=
  (heightPhysicalJetCLM hT (hS.1 (3 / 4 : ℝ)) a b p hp).comp
      (statePhysicalHeightCLM S) +
    (if b = 0 then iteratedDeriv a S.chiLeft p.1 else 0) • stateLeftHeightCLM S

theorem stateUJetCLM_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) (x : AnnularState S) :
    stateUJetCLM hT hS a b p hp x = mixedDerivative a b (stateU S x) p := by
  rw [mixedDerivative_stateU hT hS]
  simp only [stateUJetCLM, add_apply, ContinuousLinearMap.comp_apply,
    statePhysicalHeightCLM_apply, stateLeftHeightCLM_apply, smul_apply, smul_eq_mul,
    heightPhysicalJetCLM_apply]
  ring

private theorem mixedDerivative_zero_zero (f : PolarPoint → ℝ) :
    mixedDerivative 0 0 f = f := by
  funext p
  simp only [mixedDerivative, iteratedDeriv_zero]

private theorem radialPartial_eq_firstMixedJet {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) : radialPartial f = mixedDerivative 1 0 f := by
  simpa only [mixedDerivative_zero_zero, zero_add] using radialPartial_mixedDerivative hf 0 0

private theorem angularPartial_eq_firstMixedJet {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) : angularPartial f = mixedDerivative 0 1 f := by
  simpa only [mixedDerivative_zero_zero, zero_add] using angularPartial_mixedDerivative hf 0 0

theorem heightRadial_eq_firstMixedJet {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (p : PolarPoint) :
    heightRadial f p = mixedDerivative 1 0 f p :=
  congrFun (radialPartial_eq_firstMixedJet hf) p

theorem heightAngular_eq_firstMixedJet {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (p : PolarPoint) :
    heightAngular f p = mixedDerivative 0 1 f p / p.1 := by
  rw [heightAngular, angularPartial_eq_firstMixedJet hf]

theorem radialPartial_heightRadial_eq_secondMixedJet {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (p : PolarPoint) :
    radialPartial (heightRadial f) p = mixedDerivative 2 0 f p := by
  rw [heightRadial, radialPartial_eq_firstMixedJet hf,
    radialPartial_mixedDerivative hf 1 0]

/-- The normalization `p = f_θ/r` contributes the exact derivative of `1/r`. -/
theorem radialPartial_heightAngular_eq_mixedJets {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) {p : PolarPoint} (hr : p.1 ≠ 0) :
    radialPartial (heightAngular f) p =
      mixedDerivative 1 1 f p / p.1 - mixedDerivative 0 1 f p / p.1 ^ 2 := by
  have hθ : DifferentiableAt ℝ (angularPartial f) p :=
    (contDiffAt_angularPartial hf.contDiffAt (m := 1) (by simp)).differentiableAt one_ne_zero
  unfold heightAngular
  rw [radialPartial_div hθ differentiableAt_fst hr, radialPartial_fst,
    angularPartial_eq_firstMixedJet hf, radialPartial_mixedDerivative hf 0 1]
  field_simp [hr]
  ring

theorem angularPartial_heightAngular_eq_secondMixedJet {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) {p : PolarPoint} (hr : p.1 ≠ 0) :
    angularPartial (heightAngular f) p = mixedDerivative 0 2 f p / p.1 := by
  have hθ : DifferentiableAt ℝ (angularPartial f) p :=
    (contDiffAt_angularPartial hf.contDiffAt (m := 1) (by simp)).differentiableAt one_ne_zero
  unfold heightAngular
  rw [angularPartial_div hθ differentiableAt_fst hr, angularPartial_fst,
    angularPartial_eq_firstMixedJet hf, angularPartial_mixedDerivative hf 0 1]
  field_simp [hr]
  ring

def stateUHeightRadialCLM
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (p : PolarPoint) (hp : p ∈ annularOpen D) : AnnularState S →L[ℝ] ℝ :=
  stateUJetCLM hT hS 1 0 p hp

def stateUHeightAngularCLM
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (p : PolarPoint) (hp : p ∈ annularOpen D) : AnnularState S →L[ℝ] ℝ :=
  p.1⁻¹ • stateUJetCLM hT hS 0 1 p hp

def stateURadialHeightRadialCLM
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (p : PolarPoint) (hp : p ∈ annularOpen D) : AnnularState S →L[ℝ] ℝ :=
  stateUJetCLM hT hS 2 0 p hp

def stateURadialHeightAngularCLM
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (p : PolarPoint) (hp : p ∈ annularOpen D) : AnnularState S →L[ℝ] ℝ :=
  p.1⁻¹ • stateUJetCLM hT hS 1 1 p hp -
    (p.1 ^ 2)⁻¹ • stateUJetCLM hT hS 0 1 p hp

def stateUAngularHeightAngularCLM
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (p : PolarPoint) (hp : p ∈ annularOpen D) : AnnularState S →L[ℝ] ℝ :=
  p.1⁻¹ • stateUJetCLM hT hS 0 2 p hp

theorem stateUHeightRadialCLM_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (p : PolarPoint) (hp : p ∈ annularOpen D) (x : AnnularState S) :
    stateUHeightRadialCLM hT hS p hp x = heightRadial (stateU S x) p := by
  rw [heightRadial_eq_firstMixedJet (smooth_actualStateU hT hS x)]
  exact stateUJetCLM_apply hT hS 1 0 p hp x

theorem stateUHeightAngularCLM_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (p : PolarPoint) (hp : p ∈ annularOpen D) (x : AnnularState S) :
    stateUHeightAngularCLM hT hS p hp x = heightAngular (stateU S x) p := by
  rw [heightAngular_eq_firstMixedJet (smooth_actualStateU hT hS x)]
  simp only [stateUHeightAngularCLM, smul_apply, smul_eq_mul, stateUJetCLM_apply,
    div_eq_mul_inv, mul_comm]

theorem stateURadialHeightRadialCLM_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (p : PolarPoint) (hp : p ∈ annularOpen D) (x : AnnularState S) :
    stateURadialHeightRadialCLM hT hS p hp x =
      radialPartial (heightRadial (stateU S x)) p := by
  rw [radialPartial_heightRadial_eq_secondMixedJet (smooth_actualStateU hT hS x)]
  exact stateUJetCLM_apply hT hS 2 0 p hp x

theorem stateURadialHeightAngularCLM_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (p : PolarPoint) (hp : p ∈ annularOpen D) (hr : p.1 ≠ 0) (x : AnnularState S) :
    stateURadialHeightAngularCLM hT hS p hp x =
      radialPartial (heightAngular (stateU S x)) p := by
  rw [radialPartial_heightAngular_eq_mixedJets (smooth_actualStateU hT hS x) hr]
  simp only [stateURadialHeightAngularCLM, sub_apply, smul_apply, smul_eq_mul,
    stateUJetCLM_apply, div_eq_mul_inv, mul_comm]

theorem stateUAngularHeightAngularCLM_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (p : PolarPoint) (hp : p ∈ annularOpen D) (hr : p.1 ≠ 0) (x : AnnularState S) :
    stateUAngularHeightAngularCLM hT hS p hp x =
      angularPartial (heightAngular (stateU S x)) p := by
  rw [angularPartial_heightAngular_eq_secondMixedJet (smooth_actualStateU hT hS x) hr]
  simp only [stateUAngularHeightAngularCLM, smul_apply, smul_eq_mul,
    stateUJetCLM_apply, div_eq_mul_inv, mul_comm]

private def jointStateFunctionalSmoothDirections {S : PhysicalSpacesData}
    {f : AnnularState S → ℝ} (L : AnnularState S →L[ℝ] ℝ)
    (hL : ∀ x, L x = f x) :
    SmoothDirections univ (fun z : AnnularState S × ℝ => f z.1) :=
  (smoothDirectionsLinear (L.comp (ContinuousLinearMap.fst ℝ (AnnularState S) ℝ))).congr
    (fun z _ => by
      change L z.1 = f z.1
      exact hL z.1)

def jointStateUJetSmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    SmoothDirections univ (fun z : AnnularState S × ℝ =>
      mixedDerivative a b (stateU S z.1) p) :=
  jointStateFunctionalSmoothDirections (stateUJetCLM hT hS a b p hp)
    (stateUJetCLM_apply hT hS a b p hp)

def stateUHeightRadialSmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (p : PolarPoint) (hp : p ∈ annularOpen D) :
    SmoothDirections univ (fun z : AnnularState S × ℝ => heightRadial (stateU S z.1) p) :=
  jointStateFunctionalSmoothDirections (stateUHeightRadialCLM hT hS p hp)
    (stateUHeightRadialCLM_apply hT hS p hp)

def stateUHeightAngularSmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (p : PolarPoint) (hp : p ∈ annularOpen D) :
    SmoothDirections univ (fun z : AnnularState S × ℝ => heightAngular (stateU S z.1) p) :=
  jointStateFunctionalSmoothDirections (stateUHeightAngularCLM hT hS p hp)
    (stateUHeightAngularCLM_apply hT hS p hp)

def stateURadialHeightRadialSmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (p : PolarPoint) (hp : p ∈ annularOpen D) :
    SmoothDirections univ (fun z : AnnularState S × ℝ =>
      radialPartial (heightRadial (stateU S z.1)) p) :=
  jointStateFunctionalSmoothDirections (stateURadialHeightRadialCLM hT hS p hp)
    (stateURadialHeightRadialCLM_apply hT hS p hp)

def stateURadialHeightAngularSmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (p : PolarPoint) (hp : p ∈ annularOpen D) (hr : p.1 ≠ 0) :
    SmoothDirections univ (fun z : AnnularState S × ℝ =>
      radialPartial (heightAngular (stateU S z.1)) p) :=
  jointStateFunctionalSmoothDirections (stateURadialHeightAngularCLM hT hS p hp)
    (stateURadialHeightAngularCLM_apply hT hS p hp hr)

def stateUAngularHeightAngularSmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (p : PolarPoint) (hp : p ∈ annularOpen D) (hr : p.1 ≠ 0) :
    SmoothDirections univ (fun z : AnnularState S × ℝ =>
      angularPartial (heightAngular (stateU S z.1)) p) :=
  jointStateFunctionalSmoothDirections (stateUAngularHeightAngularCLM hT hS p hp)
    (stateUAngularHeightAngularCLM_apply hT hS p hp hr)

end ContinuousFlexibility.Statements
