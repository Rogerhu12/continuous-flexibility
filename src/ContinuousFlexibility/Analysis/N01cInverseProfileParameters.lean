module

public import ContinuousFlexibility.Analysis.N01cProfileRadialBounds
public import ContinuousFlexibility.Analysis.N01cSpatialParameterComposition

/-!
# Actual parameter towers for reciprocal radial profiles

On the open radial core, linearity of the true profile exponent identifies
the reciprocal profile with the reflected profile times the fixed square
of the inverse reference profile.  Ordinary Leibniz differentiation then
uses only finitely many already constructed radial profile towers.

No inverse reference profile is assumed smooth at an endpoint.  The
spatial equality is transferred through a genuine neighbourhood germ.
The reflected base state and all reflected parameter directions remain
explicit in the exact tower formula.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem inverse_scaledExp_reflection (w e : ℝ) :
    (w * Real.exp e)⁻¹ = (w⁻¹ * w⁻¹) * (w * Real.exp (-e)) := by
  by_cases hw : w = 0
  · simp only [hw, zero_mul, inv_zero]
  · rw [Real.exp_neg]
    field_simp [hw, Real.exp_ne_zero] <;> ring

private theorem inverse_scaledExpLinear_reflection
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (w : ℝ) (L : E →L[ℝ] ℝ) (x : E) :
    (w * Real.exp (L x))⁻¹ =
      (w⁻¹ * w⁻¹) * (w * Real.exp (L (-x))) := by
  simpa only [map_neg] using inverse_scaledExp_reflection w (L x)

section ReflectedFiniteSum

variable {E ι : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [Fintype ι]

/-- Fixed scalar coefficients and reflection preserve the actual tower.
The generic construction keeps projective-state instance reduction out
of the concrete reciprocal-profile wrapper. -/
private def reflectedWeightedSumSmoothDirections
    (c : ι → ℝ) {f : ι → E → ℝ}
    (J : ∀ i, SmoothDirections univ (f i)) :
    SmoothDirections univ (fun x : E => ∑ i, c i * f i (-x)) := by
  let L : E →L[ℝ] E := -(ContinuousLinearMap.id ℝ E)
  let A : ι → ℝ →L[ℝ] ℝ := fun i => c i • ContinuousLinearMap.id ℝ ℝ
  let K : ∀ i, SmoothDirections univ (fun x : E => c i * f i (-x)) :=
    fun i => (smoothDirections_postcompCLM
      (smoothDirections_precompCLM (J i) L) (A i)).congr (fun x _ => by
        simp only [Function.comp_apply, L, A, smul_apply, neg_apply,
          ContinuousLinearMap.id_apply, smul_eq_mul])
  exact smoothDirections_finiteSum isOpen_univ K

private theorem reflectedWeightedSumSmoothDirections_D_apply
    (c : ι → ℝ) {f : ι → E → ℝ}
    (J : ∀ i, SmoothDirections univ (f i))
    (k : ℕ) (x : E) (v : Fin k → E) :
    (reflectedWeightedSumSmoothDirections c J).D k x v =
      ∑ i, c i * (J i).D k (-x) (fun j => -(v j)) := by
  change (∑ i, (c i • ContinuousLinearMap.id ℝ ℝ).compContinuousMultilinearMap
      (((J i).D k ((-(ContinuousLinearMap.id ℝ E)) x)).compContinuousLinearMap
        (fun _ : Fin k => -(ContinuousLinearMap.id ℝ E)))) v = _
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    smul_apply, neg_apply, ContinuousLinearMap.id_apply, smul_eq_mul]

end ReflectedFiniteSum

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency true

private abbrev inverseProfileStateTopology (S : PhysicalSpacesData) :
    TopologicalSpace (AnnularState S) := inferInstance
attribute [local instance] inverseProfileStateTopology

private abbrev inverseProfileStateGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := inferInstance
attribute [local instance] inverseProfileStateGroup

private abbrev inverseProfileStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := inferInstance
attribute [local instance] inverseProfileStateModule

private abbrev inverseProfileStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) :=
  (inverseProfileStateModule S).toDistribMulAction.toDistribSMul.toSMul
attribute [local instance] inverseProfileStateSMul

private abbrev inverseProfileStateTopologicalAddGroup (S : PhysicalSpacesData) :
    IsTopologicalAddGroup (AnnularState S) := inferInstance
attribute [local instance] inverseProfileStateTopologicalAddGroup

/-- The actual reciprocal profile is a fixed radial multiplier times the
actual profile at the reflected state.  Only exponent linearity is used. -/
theorem stateProfile_inverse_eq_reflected
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) (x : AnnularState S) :
    (stateProfile D S C x r)⁻¹ =
      ((D.w r)⁻¹ * (D.w r)⁻¹) * stateProfile D S C (-x) r := by
  let L : AnnularState S →L[ℝ] ℝ := stateProfileExponentCLM hS hT hRef hC r hr
  calc
    (stateProfile D S C x r)⁻¹ = (D.w r * Real.exp (L x))⁻¹ :=
      congrArg (fun a : ℝ => a⁻¹) (stateProfile_eq_exp_exponentCLM hS hT hRef hC r hr x)
    _ = ((D.w r)⁻¹ * (D.w r)⁻¹) * (D.w r * Real.exp (L (-x))) :=
      inverse_scaledExpLinear_reflection (D.w r) L x
    _ = ((D.w r)⁻¹ * (D.w r)⁻¹) * stateProfile D S C (-x) r :=
      congrArg (fun a : ℝ => ((D.w r)⁻¹ * (D.w r)⁻¹) * a)
        (stateProfile_eq_exp_exponentCLM hS hT hRef hC r hr (-x)).symm

/-- The reflection formula holds on a full neighbourhood of every core
radius, so it identifies all ordinary radial derivatives there. -/
theorem stateProfile_inverse_eventuallyEq_reflected
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) (x : AnnularState S) :
    (fun s => (stateProfile D S C x s)⁻¹) =ᶠ[𝓝 r]
      (fun s => ((D.w s)⁻¹ * (D.w s)⁻¹) * stateProfile D S C (-x) s) := by
  filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
  exact stateProfile_inverse_eq_reflected hS hT hRef hC s hs x

/-- A finite ordinary Leibniz expansion for every actual reciprocal
profile jet.  Smoothness of the inverse reference is used only at r. -/
theorem iteratedDeriv_stateProfile_inverse_eq_reflected_sum
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hD : RadialProfileGeometry D)
    (hC : controlGeometryConditions D S C) (hχ : ContDiff ℝ ∞ D.chi)
    (n : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b) (x : AnnularState S) :
    iteratedDeriv n (fun s => (stateProfile D S C x s)⁻¹) r =
      ∑ a : Fin (n + 1), (n.choose a.val : ℝ) *
        iteratedDeriv a.val (fun s => (D.w s)⁻¹ * (D.w s)⁻¹) r *
          iteratedDeriv (n - a.val) (stateProfile D S C (-x)) r := by
  have hInv : ContDiffAt ℝ ∞ (fun s => (D.w s)⁻¹) r :=
    hD.2.2.1.1.contDiffAt.inv (hD.2.2.2.2.1 r hr).ne'
  have hProfile : ContDiffAt ℝ ∞ (stateProfile D S C (-x)) r :=
    (contDiffOn_stateProfile hD hχ hC (-x)).contDiffAt (isOpen_Ioo.mem_nhds hr)
  let term (a : ℕ) : ℝ := (n.choose a : ℝ) *
    iteratedDeriv a (fun s => (D.w s)⁻¹ * (D.w s)⁻¹) r *
      iteratedDeriv (n - a) (stateProfile D S C (-x)) r
  calc
    _ = iteratedDeriv n
        (fun s => ((D.w s)⁻¹ * (D.w s)⁻¹) * stateProfile D S C (-x) s) r :=
      (stateProfile_inverse_eventuallyEq_reflected hS hT hRef hC r hr x).iteratedDeriv_eq n
    _ = ∑ a : Fin (n + 1), term a.val := by
      rw [Fin.sum_univ_eq_sum_range term]
      exact iteratedDeriv_fun_mul ((hInv.mul hInv).of_le (by simp))
        (hProfile.of_le (by simp))

/-- Every radial reciprocal-profile jet has a genuine parameter tower on
the original projective state space.  Its finite construction uses only
the already verified radial towers, reflection, and fixed scalar sums. -/
def stateInverseProfileRadialJetSmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hD : RadialProfileGeometry D)
    (hC : controlGeometryConditions D S C) (hχ : ContDiff ℝ ∞ D.chi)
    (n : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b) :
    SmoothDirections univ
      (fun x : AnnularState S => iteratedDeriv n (fun s => (stateProfile D S C x s)⁻¹) r) := by
  let J := reflectedWeightedSumSmoothDirections (E := AnnularState S)
    (fun a : Fin (n + 1) => (n.choose a.val : ℝ) *
      iteratedDeriv a.val (fun s => (D.w s)⁻¹ * (D.w s)⁻¹) r)
    (fun a : Fin (n + 1) =>
      stateProfileRadialJetSmoothDirections hS hT hRef hD hC hχ (n - a.val) r hr)
  exact J.congr (fun x _ =>
    (iteratedDeriv_stateProfile_inverse_eq_reflected_sum hS hT hRef hD hC hχ n r hr x).symm)

/-- The actual parameter derivative is the finite sum of reflected
profile derivatives, with the same reflected direction in every slot.
This exact identity includes parameter order zero. -/
theorem stateInverseProfileRadialJetSmoothDirections_D_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hD : RadialProfileGeometry D)
    (hC : controlGeometryConditions D S C) (hχ : ContDiff ℝ ∞ D.chi)
    (n k : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b)
    (x : AnnularState S) (v : Fin k → AnnularState S) :
    (stateInverseProfileRadialJetSmoothDirections hS hT hRef hD hC hχ n r hr).D k x v =
      ∑ a : Fin (n + 1), (n.choose a.val : ℝ) *
        iteratedDeriv a.val (fun s => (D.w s)⁻¹ * (D.w s)⁻¹) r *
          (stateProfileRadialJetSmoothDirections
            hS hT hRef hD hC hχ (n - a.val) r hr).D k (-x) (fun i => -(v i)) := by
  exact reflectedWeightedSumSmoothDirections_D_apply (E := AnnularState S)
    (fun a : Fin (n + 1) => (n.choose a.val : ℝ) *
      iteratedDeriv a.val (fun s => (D.w s)⁻¹ * (D.w s)⁻¹) r)
    (fun a : Fin (n + 1) =>
      stateProfileRadialJetSmoothDirections hS hT hRef hD hC hχ (n - a.val) r hr) k x v

end ContinuousFlexibility.Statements
