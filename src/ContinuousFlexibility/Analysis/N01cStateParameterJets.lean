import ContinuousFlexibility.Analysis.N01cStateSeminorms
import ContinuousFlexibility.Analysis.N01cLinearContinuity
import ContinuousFlexibility.Analysis.N01cCoefficientJetCalculus
import ContinuousFlexibility.Analysis.StateProfileRegularity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Parameter derivatives of the actual controlled profile

The mean of each decoded circle is a continuous linear functional of the
actual state.  Local finiteness then makes evaluation of the control sum
a finite sum of these functionals.  The controlled profile at a fixed
interior radius is the exponential of the resulting continuous linear
functional, multiplied by the reference profile.

The directional towers below are explicit continuous multilinear maps.
Their derivative identities are proved by ordinary real differentiation
along affine lines; neither parameter smoothness nor a tame bound is an
input hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

section ExponentialJets

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

/-- The continuous multilinear product of one scalar functional in all slots. -/
def scalarFunctionalProduct (L : E →L[ℝ] ℝ) (n : ℕ) : E [×n]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
    (fun _ => L)

theorem scalarFunctionalProduct_apply (L : E →L[ℝ] ℝ) (n : ℕ) (v : Fin n → E) :
    scalarFunctionalProduct L n v = ∏ i, L (v i) := by
  simp only [scalarFunctionalProduct, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]

/-- The explicit all-order parameter jets of a scaled exponential. -/
def scaledExpLinearJets (a : ℝ) (L : E →L[ℝ] ℝ) (n : ℕ) (x : E) :
    E [×n]→L[ℝ] ℝ :=
  (a * Real.exp (L x)) • scalarFunctionalProduct L n

theorem scaledExpLinearJets_apply (a : ℝ) (L : E →L[ℝ] ℝ)
    (n : ℕ) (x : E) (v : Fin n → E) :
    scaledExpLinearJets a L n x v = a * Real.exp (L x) * ∏ i, L (v i) := by
  simp only [scaledExpLinearJets, smul_apply, smul_eq_mul, scalarFunctionalProduct_apply]

/-- The elementary real exponential rule, before linear precomposition. -/
private theorem hasProjectiveLineDerivAt_scaledScalarExp
    (a b x w : ℝ) :
    HasProjectiveLineDerivAt (fun y : ℝ => a * Real.exp y * b)
      ((a * (Real.exp x * w)) * b) x w := by
  have hline : HasDerivAt (fun t : ℝ => x + t * w) w (0 : ℝ) := by
    simpa only [one_mul, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).mul_const w).const_add x
  have hcurve : HasDerivAt (fun t : ℝ => a * Real.exp (x + t * w) * b)
      ((a * (Real.exp x * w)) * b) (0 : ℝ) := by
    simpa only [zero_mul, add_zero] using
      ((hline.exp.const_mul a).mul_const b)
  simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt, smul_eq_mul] using
    hcurve.tendsto_slope_zero

private theorem scaledExpLinearJets_hasLineDerivAt
    (a : ℝ) (L : E →L[ℝ] ℝ) (n : ℕ) (x : E) (v : Fin n → E) (w : E) :
    HasProjectiveLineDerivAt (fun y : E => scaledExpLinearJets a L n y v)
      (scaledExpLinearJets a L (n + 1) x (Fin.cons w v)) x w := by
  have hd : HasProjectiveLineDerivAt
      (fun y : E => a * Real.exp (L y) * ∏ i, L (v i))
      ((a * (Real.exp (L x) * L w)) * ∏ i, L (v i)) x w :=
    (hasProjectiveLineDerivAt_scaledScalarExp a (∏ i, L (v i)) (L x) (L w)).comp_linear
      L.toLinearMap
  have hvalue : ((a * (Real.exp (L x) * L w)) * ∏ i, L (v i)) =
      scaledExpLinearJets a L (n + 1) x (Fin.cons w v) := by
    rw [scaledExpLinearJets_apply, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    ring
  have hd' : HasProjectiveLineDerivAt
      (fun y : E => a * Real.exp (L y) * ∏ i, L (v i))
      (scaledExpLinearJets a L (n + 1) x (Fin.cons w v)) x w := hvalue ▸ hd
  simpa only [scaledExpLinearJets_apply] using hd'

/-- The scaled-exponential tower consists of genuine topological line
derivatives, on the entire parameter space. -/
def smoothDirections_scaledExpLinear (a : ℝ) (L : E →L[ℝ] ℝ) :
    SmoothDirections univ (fun x : E => a * Real.exp (L x)) where
  open_domain := isOpen_univ
  D := scaledExpLinearJets a L
  zero := by
    intro x _
    simp only [scaledExpLinearJets_apply, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  continuous := by
    intro n
    simp only [scaledExpLinearJets, smul_apply, smul_eq_mul]
    have hL : Continuous (fun z : E × (Fin n → E) => L z.1) :=
      L.continuous.comp continuous_fst
    have hExp : Continuous (fun z : E × (Fin n → E) => Real.exp (L z.1)) :=
      Real.continuous_exp.comp hL
    have hProd : Continuous (fun z : E × (Fin n → E) =>
        scalarFunctionalProduct L n z.2) :=
      (scalarFunctionalProduct L n).cont.comp continuous_snd
    exact ((continuous_const.mul hExp).mul hProd).continuousOn
  derivative := by
    intro n x _ v w
    exact scaledExpLinearJets_hasLineDerivAt a L n x v w

end ExponentialJets

section ParametricRadialDerivatives

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Ordinary differentiation in one scalar variable preserves joint
smoothness with respect to normed parameters, at every finite order. -/
theorem contDiff_uncurry_iteratedDeriv {f : P → ℝ → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (n : ℕ) :
    ContDiff ℝ ∞ (fun y : P × ℝ => iteratedDeriv n (f y.1) y.2) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hf
  | succ n ih =>
      have haux : ContDiff ℝ ∞ (fun z : (P × ℝ) × ℝ =>
          iteratedDeriv n (f z.1.1) z.2) :=
        ih.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
      have hderiv : ContDiff ℝ ∞ (fun y : P × ℝ =>
          fderiv ℝ (fun s => iteratedDeriv n (f y.1) s) y.2) :=
        haux.fderiv contDiff_snd (by simp)
      have hvalue : ContDiff ℝ ∞ (fun y : P × ℝ =>
          fderiv ℝ (fun s => iteratedDeriv n (f y.1) s) y.2 (1 : ℝ)) :=
        hderiv.clm_apply contDiff_const
      simpa only [iteratedDeriv_succ, fderiv_apply_one_eq_deriv] using hvalue

end ParametricRadialDerivatives

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency true

/- Cache the actual product instances before elaborating state operations. -/
private abbrev n01cStateTopology (S : PhysicalSpacesData) :
    TopologicalSpace (AnnularState S) := inferInstance
attribute [local instance] n01cStateTopology

private abbrev n01cStateGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := inferInstance
attribute [local instance] n01cStateGroup

private abbrev n01cStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := inferInstance
attribute [local instance] n01cStateModule

private abbrev n01cStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) :=
  (n01cStateModule S).toDistribMulAction.toDistribSMul.toSMul
attribute [local instance] n01cStateSMul

private theorem scalarMean_add {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume 0 Real.pi)
    (hg : IntervalIntegrable g MeasureTheory.volume 0 Real.pi) :
    angularMean (fun t => f t + g t) = angularMean f + angularMean g := by
  unfold angularMean
  rw [intervalIntegral.integral_add hf hg]
  ring

private theorem scalarMean_const_mul (c : ℝ) (f : ℝ → ℝ) :
    angularMean (fun t => c * f t) = c * angularMean f := by
  unfold angularMean
  rw [intervalIntegral.integral_const_mul]
  ring

private theorem scalarLinearMean_add {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : E →ₗ[ℝ] (ℝ → ℝ)) (x y : E)
    (hx : IntervalIntegrable (L x) MeasureTheory.volume 0 Real.pi)
    (hy : IntervalIntegrable (L y) MeasureTheory.volume 0 Real.pi) :
    angularMean (L (x + y)) = angularMean (L x) + angularMean (L y) := by
  have heq : L (x + y) = (fun t => L x t + L y t) := by
    funext t
    simpa only [Pi.add_apply] using congrFun (map_add L x y) t
  exact (congrArg angularMean heq).trans (scalarMean_add hx hy)

private theorem scalarLinearMean_smul {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : E →ₗ[ℝ] (ℝ → ℝ)) (c : ℝ) (x : E) :
    angularMean (L (c • x)) = c * angularMean (L x) := by
  have heq : L (c • x) = (fun t => c * L x t) := by
    funext t
    simpa only [Pi.smul_apply, smul_eq_mul] using congrFun (map_smul L c x) t
  exact (congrArg angularMean heq).trans (scalarMean_const_mul c (L x))

private theorem scalarCLMSum_apply {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (I : Finset ℕ) (a : ℕ → ℝ) (L : ℕ → E →L[ℝ] ℝ) (x : E) :
    (∑ m ∈ I, a m • L m) x = ∑ m ∈ I, a m * L m x := by
  simp only [sum_apply, smul_apply, smul_eq_mul]

private theorem scalarCLMSmulAdd_apply {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (a : ℝ) (L M : E →L[ℝ] ℝ) (x : E) :
    (a • L + M) x = a * L x + M x := by
  simp only [add_apply, smul_apply, smul_eq_mul]

private theorem profile_derivative_reassociate (e a b c : ℝ) :
    a * Real.exp e + b * (Real.exp e * c) = Real.exp e * (a + b * c) := by
  ring

private def stateControlDecodeLinear (S : PhysicalSpacesData) (m : ℕ) :
    AnnularState S →ₗ[ℝ] (ℝ → ℝ) :=
  (LinearMap.proj m).comp ((S.circle (3 / 4 : ℝ)).decode.comp
    ((LinearMap.fst ℝ (CircleSpace S) (CircleSpace S)).comp
      ((LinearMap.snd ℝ ℝ (CircleSpace S × CircleSpace S)).comp
        (LinearMap.snd ℝ (HeightPair S) (ℝ × (CircleSpace S × CircleSpace S))))))

private theorem stateControlDecodeLinear_apply (S : PhysicalSpacesData) (m : ℕ)
    (x : AnnularState S) :
    stateControlDecodeLinear S m x = (S.circle (3 / 4 : ℝ)).decode x.2.2.1 m := by
  simp only [stateControlDecodeLinear, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.fst_apply, LinearMap.snd_apply]

private theorem stateKappa_eq_scalarMean (S : PhysicalSpacesData)
    (x : AnnularState S) (m : ℕ) :
    stateKappa S x m = angularMean (stateControlDecodeLinear S m x) :=
  congrArg angularMean (stateControlDecodeLinear_apply S m x).symm


private theorem decodedControl_intervalIntegrable {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S)
    (x : AnnularState S) (m : ℕ) :
    IntervalIntegrable ((S.circle (3 / 4 : ℝ)).decode x.2.2.1 m)
      MeasureTheory.volume 0 Real.pi :=
  (((hS.2.1 (3 / 4 : ℝ)).2.2.2.1 x.2.2.1).1 m).1.continuous.intervalIntegrable _ _

theorem stateKappa_add {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (x y : AnnularState S) (m : ℕ) :
    stateKappa S (x + y : AnnularState S) m = stateKappa S x m + stateKappa S y m := by
  have hx : IntervalIntegrable (stateControlDecodeLinear S m x)
      MeasureTheory.volume 0 Real.pi :=
    (stateControlDecodeLinear_apply S m x).symm ▸ decodedControl_intervalIntegrable hS x m
  have hy : IntervalIntegrable (stateControlDecodeLinear S m y)
      MeasureTheory.volume 0 Real.pi :=
    (stateControlDecodeLinear_apply S m y).symm ▸ decodedControl_intervalIntegrable hS y m
  exact (stateKappa_eq_scalarMean S (x + y) m).trans
    ((scalarLinearMean_add (stateControlDecodeLinear S m) x y hx hy).trans
      (congrArg₂ (· + ·) (stateKappa_eq_scalarMean S x m).symm
        (stateKappa_eq_scalarMean S y m).symm))

theorem stateKappa_smul (S : PhysicalSpacesData) (c : ℝ)
    (x : AnnularState S) (m : ℕ) :
    stateKappa S (c • x : AnnularState S) m = c * stateKappa S x m := by
  exact (stateKappa_eq_scalarMean S (c • x) m).trans
    ((scalarLinearMean_smul (stateControlDecodeLinear S m) c x).trans
      (congrArg (fun t : ℝ => c * t) (stateKappa_eq_scalarMean S x m).symm))

/-- The actual decoded control mean, bundled as a linear functional. -/
def stateKappaLinear {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (m : ℕ) : AnnularState S →ₗ[ℝ] ℝ where
  toFun x := stateKappa S x m
  map_add' x y := stateKappa_add hS x y m
  map_smul' c x := by
    simpa only [smul_eq_mul, RingHom.id_apply] using stateKappa_smul S c x m

theorem stateKappaLinear_apply {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S) (m : ℕ)
    (x : AnnularState S) : stateKappaLinear hS m x = stateKappa S x m := rfl

/-- Continuity follows from the genuine level-zero weighted estimate. -/
theorem continuous_stateKappa {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (m : ℕ) :
    Continuous (fun x : AnnularState S => stateKappa S x m) := by
  let L : AnnularState S →ₗ[ℝ] ℝ := stateKappaLinear hS m
  let K : ℝ := ((1 / Real.pi) * Real.sqrt Real.pi) *
    T.H (T.sample m) ^ (3 / 4 : ℝ)
  have hbound (x : AnnularState S) : ‖L x‖ ≤ K * stateGrading S 0 x := by
    calc
      ‖L x‖ = |stateKappa S x m| := by
        simp only [L, stateKappaLinear_apply, Real.norm_eq_abs]
      _ ≤ (((1 / Real.pi) * Real.sqrt Real.pi) * stateGrading S 0 x) *
          T.H (T.sample m) ^ (3 / 4 : ℝ) :=
        abs_stateKappa_le_stateGrading_of_accumulatingProfile hS hT hRef x 0 m
      _ = K * stateGrading S 0 x := by
        dsimp only [K]
        ring
  exact continuous_linear_of_seminorm_bound L (stateGrading S 0)
    (continuous_stateGrading S 0) K hbound

/-- The continuous scalar evaluation of a control component of the state. -/
def stateKappaCLM {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (m : ℕ) : AnnularState S →L[ℝ] ℝ where
  toLinearMap := stateKappaLinear hS m
  cont := continuous_stateKappa hS hT hRef m

theorem stateKappaCLM_apply {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (m : ℕ) (x : AnnularState S) :
    stateKappaCLM hS hT hRef m x = stateKappa S x m := rfl

/-- Only finitely many controls are active at an interior radius. -/
theorem finite_activeControls {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hC : controlGeometryConditions D S C)
    {r : ℝ} (hr : r ∈ Ioo D.a D.b) : Set.Finite {m : ℕ | C.control m r ≠ 0} := by
  obtain ⟨_, _, _, _, _, _, hfinite, _⟩ := hC
  exact hfinite.point_finite ⟨r, hr⟩

/-- Evaluation of the actual locally finite sum is a finite sum of continuous
linear control evaluations. -/
def stateControlEvalCLM {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) : AnnularState S →L[ℝ] ℝ :=
  ∑ m ∈ (finite_activeControls hC hr).toFinset,
    C.control m r • stateKappaCLM hS hT hRef m

theorem stateControlEvalCLM_apply {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) (x : AnnularState S) :
    stateControlEvalCLM hS hT hRef hC r hr x = stateControlSum C x r := by
  classical
  have hsum : stateControlSum C x r =
      ∑ m ∈ (finite_activeControls hC hr).toFinset, stateKappa S x m * C.control m r := by
    unfold stateControlSum
    apply tsum_eq_sum
    intro m hm
    have hz : C.control m r = 0 := by
      by_contra hne
      exact hm ((finite_activeControls hC hr).mem_toFinset.mpr hne)
    rw [hz, mul_zero]
  have heval : stateControlEvalCLM hS hT hRef hC r hr x =
      ∑ m ∈ (finite_activeControls hC hr).toFinset, C.control m r * stateKappa S x m := by
    exact (scalarCLMSum_apply (finite_activeControls hC hr).toFinset
      (fun m => C.control m r) (stateKappaCLM hS hT hRef) x).trans
        (Finset.sum_congr rfl (fun m _ =>
          congrArg (fun t : ℝ => C.control m r * t) (stateKappaCLM_apply hS hT hRef m x)))
  exact heval.trans ((Finset.sum_congr rfl (fun m _ => mul_comm _ _)).trans hsum.symm)

/-- The compact scalar component of the actual annular state. -/
def stateNuCLM (S : PhysicalSpacesData) : AnnularState S →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (CircleSpace S × CircleSpace S)).comp
    (ContinuousLinearMap.snd ℝ (HeightPair S) (ℝ × (CircleSpace S × CircleSpace S)))

theorem stateNuCLM_apply (S : PhysicalSpacesData) (x : AnnularState S) :
    stateNuCLM S x = x.2.1 := by
  simp only [stateNuCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']

/-- The exponent defining the controlled radial profile at one fixed radius. -/
def stateProfileExponentCLM {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) : AnnularState S →L[ℝ] ℝ :=
  D.chi r • stateNuCLM S + stateControlEvalCLM hS hT hRef hC r hr

theorem stateProfileExponentCLM_apply {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) (x : AnnularState S) :
    stateProfileExponentCLM hS hT hRef hC r hr x =
      x.2.1 * D.chi r + stateControlSum C x r := by
  simp only [stateProfileExponentCLM, add_apply, smul_apply, smul_eq_mul,
    stateNuCLM_apply, stateControlEvalCLM_apply]
  rw [mul_comm (D.chi r)]

theorem stateProfile_eq_exp_exponentCLM {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) (x : AnnularState S) :
    stateProfile D S C x r =
      D.w r * Real.exp (stateProfileExponentCLM hS hT hRef hC r hr x) := by
  rw [stateProfileExponentCLM_apply]
  exact rfl

/-- All parameter derivatives of the actual profile, at the fixed radius,
on the entire actual state space. -/
def stateProfileSmoothDirections {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) :
    SmoothDirections univ (fun x : AnnularState S => stateProfile D S C x r) where
  open_domain := isOpen_univ
  D := scaledExpLinearJets (D.w r) (stateProfileExponentCLM hS hT hRef hC r hr)
  zero := by
    intro x _
    rw [scaledExpLinearJets_apply]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    exact (stateProfile_eq_exp_exponentCLM hS hT hRef hC r hr x).symm
  continuous :=
    (smoothDirections_scaledExpLinear (D.w r)
      (stateProfileExponentCLM hS hT hRef hC r hr)).continuous
  derivative :=
    (smoothDirections_scaledExpLinear (D.w r)
      (stateProfileExponentCLM hS hT hRef hC r hr)).derivative

theorem stateProfileSmoothDirections_apply {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) (n : ℕ) (x : AnnularState S)
    (v : Fin n → AnnularState S) :
    (stateProfileSmoothDirections hS hT hRef hC r hr).D n x v =
      stateProfile D S C x r * ∏ i, stateProfileExponentCLM hS hT hRef hC r hr (v i) := by
  calc
    (stateProfileSmoothDirections hS hT hRef hC r hr).D n x v =
        (D.w r * Real.exp (stateProfileExponentCLM hS hT hRef hC r hr x)) *
          ∏ i, stateProfileExponentCLM hS hT hRef hC r hr (v i) :=
      scaledExpLinearJets_apply _ _ _ _ _
    _ = stateProfile D S C x r *
        ∏ i, stateProfileExponentCLM hS hT hRef hC r hr (v i) :=
      congrArg (fun a : ℝ => a *
        ∏ i, stateProfileExponentCLM hS hT hRef hC r hr (v i))
        (stateProfile_eq_exp_exponentCLM hS hT hRef hC r hr x).symm

/-- A finite collection of controls represents the actual control sum on a
neighbourhood of the radius, simultaneously for all states. -/
theorem exists_stateControlLocalIndices {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hC : controlGeometryConditions D S C)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) :
    ∃ indices : Finset ℕ, ∀ x : AnnularState S,
      stateControlSum C x =ᶠ[𝓝 r]
        (fun s => ∑ m ∈ indices, stateKappa S x m * C.control m s) := by
  classical
  obtain ⟨_, _, _, _, _, _, hfinite, _⟩ := hC
  obtain ⟨t, ht, htf⟩ := hfinite ⟨r, hr⟩
  refine ⟨htf.toFinset, ?_⟩
  intro x
  have hn : (Subtype.val : Ioo D.a D.b → ℝ) '' t ∈ 𝓝 r :=
    isOpen_Ioo.isOpenMap_subtype_val.image_mem_nhds ht
  filter_upwards [hn] with s hs
  obtain ⟨z, hzt, rfl⟩ := hs
  unfold stateControlSum
  apply tsum_eq_sum
  intro m hm
  have hz : C.control m z = 0 := by
    by_contra hne
    exact hm (htf.mem_toFinset.mpr ⟨z, hne, hzt⟩)
  rw [hz, mul_zero]

/-- The locally finite index set is chosen once for all derivative orders
and all states at this radius. -/
def stateControlLocalIndices {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hC : controlGeometryConditions D S C)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) : Finset ℕ :=
  Classical.choose (exists_stateControlLocalIndices hC r hr)

theorem stateControlLocalIndices_eventuallyEq {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hC : controlGeometryConditions D S C)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) (x : AnnularState S) :
    stateControlSum C x =ᶠ[𝓝 r]
      (fun s => ∑ m ∈ stateControlLocalIndices hC r hr,
        stateKappa S x m * C.control m s) :=
  Classical.choose_spec (exists_stateControlLocalIndices hC r hr) x

/-- Every radial derivative of the actual control sum is a continuous
linear functional of the same state, with the same finite local index set. -/
def stateControlJetEvalCLM {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (n : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b) : AnnularState S →L[ℝ] ℝ :=
  ∑ m ∈ stateControlLocalIndices hC r hr,
    iteratedDeriv n (C.control m) r • stateKappaCLM hS hT hRef m

theorem stateControlJetEvalCLM_apply {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (n : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b) (x : AnnularState S) :
    stateControlJetEvalCLM hS hT hRef hC n r hr x =
      iteratedDeriv n (stateControlSum C x) r := by
  classical
  have hcontrol := hC.2.2.2.2.2.1
  have hd (m : ℕ) : ContDiffAt ℝ n
      (fun s => stateKappa S x m * C.control m s) r :=
    (contDiffAt_const.mul (hcontrol m).1.contDiffAt).of_le (by simp)
  have hsum : iteratedDeriv n (stateControlSum C x) r =
      ∑ m ∈ stateControlLocalIndices hC r hr,
        stateKappa S x m * iteratedDeriv n (C.control m) r := by
    exact ((stateControlLocalIndices_eventuallyEq hC r hr x).iteratedDeriv_eq n).trans
      ((iteratedDeriv_fun_sum (fun m _ => hd m)).trans
        (Finset.sum_congr rfl (fun m _ =>
          iteratedDeriv_const_mul_field (n := n) (x := r) (stateKappa S x m) (C.control m))))
  have heval : stateControlJetEvalCLM hS hT hRef hC n r hr x =
      ∑ m ∈ stateControlLocalIndices hC r hr,
        iteratedDeriv n (C.control m) r * stateKappa S x m := by
    exact (scalarCLMSum_apply (stateControlLocalIndices hC r hr)
      (fun m => iteratedDeriv n (C.control m) r) (stateKappaCLM hS hT hRef) x).trans
        (Finset.sum_congr rfl (fun m _ =>
          congrArg (fun t : ℝ => iteratedDeriv n (C.control m) r * t)
            (stateKappaCLM_apply hS hT hRef m x)))
  exact heval.trans ((Finset.sum_congr rfl (fun m _ => mul_comm _ _)).trans hsum.symm)

/-- Evaluation of any radial jet of the actual profile exponent. -/
def stateProfileExponentJetCLM {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (n : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b) : AnnularState S →L[ℝ] ℝ :=
  iteratedDeriv n D.chi r • stateNuCLM S + stateControlJetEvalCLM hS hT hRef hC n r hr

theorem stateProfileExponentJetCLM_apply {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (hχ : ContDiff ℝ ∞ D.chi) (n : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b)
    (x : AnnularState S) :
    stateProfileExponentJetCLM hS hT hRef hC n r hr x =
      iteratedDeriv n (fun s => x.2.1 * D.chi s + stateControlSum C x s) r := by
  have hleft : ContDiffAt ℝ n (fun s => x.2.1 * D.chi s) r :=
    (contDiffAt_const.mul hχ.contDiffAt).of_le (by simp)
  have hright : ContDiffAt ℝ n (stateControlSum C x) r :=
    ((contDiffOn_stateControlSum hC x).contDiffAt (isOpen_Ioo.mem_nhds hr)).of_le
      (by simp)
  have hderiv :
      iteratedDeriv n (fun s => x.2.1 * D.chi s + stateControlSum C x s) r =
        x.2.1 * iteratedDeriv n D.chi r + iteratedDeriv n (stateControlSum C x) r := by
    exact (iteratedDeriv_fun_add hleft hright).trans
      (congrArg (fun t : ℝ => t + iteratedDeriv n (stateControlSum C x) r)
        (iteratedDeriv_const_mul_field (n := n) (x := r) x.2.1 D.chi))
  have heval : stateProfileExponentJetCLM hS hT hRef hC n r hr x =
      iteratedDeriv n D.chi r * x.2.1 + iteratedDeriv n (stateControlSum C x) r := by
    exact (scalarCLMSmulAdd_apply (iteratedDeriv n D.chi r) (stateNuCLM S)
      (stateControlJetEvalCLM hS hT hRef hC n r hr) x).trans
        (congrArg₂ (· + ·)
          (congrArg (fun t : ℝ => iteratedDeriv n D.chi r * t) (stateNuCLM_apply S x))
          (stateControlJetEvalCLM_apply hS hT hRef hC n r hr x))
  exact heval.trans ((congrArg (fun t : ℝ =>
    t + iteratedDeriv n (stateControlSum C x) r) (mul_comm _ _)).trans hderiv.symm)

/-- The radial jets of the exponent have their genuine linear parameter
towers, in the original topology of the state space. -/
def stateProfileExponentJetSmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (hχ : ContDiff ℝ ∞ D.chi) (n : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b) :
    SmoothDirections univ (fun x : AnnularState S =>
      iteratedDeriv n (fun s => x.2.1 * D.chi s + stateControlSum C x s) r) :=
  (smoothDirectionsLinear (stateProfileExponentJetCLM hS hT hRef hC n r hr)).congr
    (fun x _ => stateProfileExponentJetCLM_apply hS hT hRef hC hχ n r hr x)

/-- The first actual radial profile derivative is an affine polynomial in
the first exponent jet, multiplied by the exponential of its zeroth jet. -/
theorem deriv_stateProfile_eq_exp_exponentJets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hD : RadialProfileGeometry D)
    (hC : controlGeometryConditions D S C) (hχ : ContDiff ℝ ∞ D.chi)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) (x : AnnularState S) :
    deriv (stateProfile D S C x) r =
      Real.exp (stateProfileExponentCLM hS hT hRef hC r hr x) *
        (deriv D.w r + D.w r * stateProfileExponentJetCLM hS hT hRef hC 1 r hr x) := by
  have hW : HasDerivAt D.w (deriv D.w r) r :=
    (hD.2.2.1.1.contDiffAt.differentiableAt (by simp)).hasDerivAt
  let e : ℝ → ℝ := fun s => x.2.1 * D.chi s + stateControlSum C x s
  have hE : ContDiffAt ℝ ∞ e r :=
    (contDiffAt_const.mul hχ.contDiffAt).add
      ((contDiffOn_stateControlSum hC x).contDiffAt (isOpen_Ioo.mem_nhds hr))
  have hE' : HasDerivAt e (deriv e r) r :=
    (hE.differentiableAt (by simp)).hasDerivAt
  have hjet : stateProfileExponentJetCLM hS hT hRef hC 1 r hr x = deriv e r := by
    simpa only [iteratedDeriv_one] using
      stateProfileExponentJetCLM_apply hS hT hRef hC hχ 1 r hr x
  have hd : deriv (stateProfile D S C x) r =
      deriv D.w r * Real.exp (e r) + D.w r * (Real.exp (e r) * deriv e r) :=
    (hW.mul hE'.exp).deriv
  have hreplace :
      deriv D.w r * Real.exp (e r) + D.w r * (Real.exp (e r) * deriv e r) =
      deriv D.w r * Real.exp (e r) +
        D.w r * (Real.exp (e r) * stateProfileExponentJetCLM hS hT hRef hC 1 r hr x) :=
    congrArg (fun t : ℝ =>
      deriv D.w r * Real.exp (e r) + D.w r * (Real.exp (e r) * t)) hjet.symm
  have hbase : e r = stateProfileExponentCLM hS hT hRef hC r hr x :=
    (stateProfileExponentCLM_apply hS hT hRef hC r hr x).symm
  exact hd.trans (hreplace.trans
    ((profile_derivative_reassociate (e r) (deriv D.w r) (D.w r)
      (stateProfileExponentJetCLM hS hT hRef hC 1 r hr x)).trans
        (congrArg (fun t : ℝ => Real.exp t *
          (deriv D.w r + D.w r * stateProfileExponentJetCLM hS hT hRef hC 1 r hr x))
          hbase)))

/-- All parameter derivatives of the actual first radial profile jet. The
construction uses a smooth scalar function on the two actual exponent jets. -/
def stateProfileDerivSmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hD : RadialProfileGeometry D)
    (hC : controlGeometryConditions D S C) (hχ : ContDiff ℝ ∞ D.chi)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) :
    SmoothDirections univ (fun x : AnnularState S => deriv (stateProfile D S C x) r) := by
  let L : AnnularState S →L[ℝ] ℝ × ℝ :=
    (stateProfileExponentCLM hS hT hRef hC r hr).prod
      (stateProfileExponentJetCLM hS hT hRef hC 1 r hr)
  have hg : ContDiff ℝ ∞ (fun y : ℝ × ℝ =>
      Real.exp y.1 * (deriv D.w r + D.w r * y.2)) :=
    contDiff_fst.exp.mul (contDiff_const.add (contDiff_const.mul contDiff_snd))
  let J := smoothDirections_contDiff_comp (smoothDirectionsLinear L) isOpen_univ
    hg.contDiffOn (fun _ _ => mem_univ _)
  apply J.congr
  intro x _
  simpa only [Function.comp_apply, L, ContinuousLinearMap.prod_apply] using
    (deriv_stateProfile_eq_exp_exponentJets hS hT hRef hD hC hχ r hr x).symm

/-- The smooth finite profile formula seen on one locally finite control
patch. Its parameters are exactly the scalar state and the active means. -/
def finiteControlProfile (D : ReferenceData) {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (indices : Finset ℕ)
    (y : ℝ × (indices → ℝ)) (r : ℝ) : ℝ :=
  D.w r * Real.exp (y.1 * D.chi r + ∑ m : indices, y.2 m * C.control m r)

theorem contDiff_finiteControlProfile {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hD : RadialProfileGeometry D)
    (hC : controlGeometryConditions D S C) (hχ : ContDiff ℝ ∞ D.chi)
    (indices : Finset ℕ) : ContDiff ℝ ∞ (Function.uncurry (finiteControlProfile D C indices)) := by
  obtain ⟨_, _, _, _, _, hcontrol, _⟩ := hC
  have hsum : ContDiff ℝ ∞ (fun z : (ℝ × (indices → ℝ)) × ℝ =>
      ∑ m : indices, z.1.2 m * C.control m z.2) := by
    apply ContDiff.sum
    intro m _
    exact ((contDiff_apply ℝ ℝ m).comp (contDiff_snd.comp contDiff_fst)).mul
      ((hcontrol m).1.comp contDiff_snd)
  exact (hD.2.2.1.1.comp contDiff_snd).mul
    ((((contDiff_fst.comp contDiff_fst).mul (hχ.comp contDiff_snd)).add hsum).exp)

/-- All spatial jets of the finite profile formula are smooth functions of
the actual finite parameters. -/
theorem contDiff_finiteControlProfileJet {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hD : RadialProfileGeometry D)
    (hC : controlGeometryConditions D S C) (hχ : ContDiff ℝ ∞ D.chi)
    (indices : Finset ℕ) (n : ℕ) (r : ℝ) :
    ContDiff ℝ ∞ (fun y : ℝ × (indices → ℝ) =>
      iteratedDeriv n (finiteControlProfile D C indices y) r) :=
  (contDiff_uncurry_iteratedDeriv (contDiff_finiteControlProfile hD hC hχ indices) n).comp
    (contDiff_id.prodMk contDiff_const)

/-- The finite tuple consists of the actual scalar component and decoded
control means of the original state. -/
def stateFiniteControlCLM {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (indices : Finset ℕ) :
    AnnularState S →L[ℝ] ℝ × (indices → ℝ) :=
  (stateNuCLM S).prod (ContinuousLinearMap.pi (fun m : indices =>
    stateKappaCLM hS hT hRef m))

theorem stateFiniteControlCLM_apply {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (indices : Finset ℕ) (x : AnnularState S) :
    stateFiniteControlCLM hS hT hRef indices x =
      (x.2.1, fun m : indices => stateKappa S x m) := by
  simp only [stateFiniteControlCLM, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_pi', stateNuCLM_apply, stateKappaCLM_apply]

/-- The finite representation holds on a spatial neighbourhood of the
radius, so it identifies every actual radial derivative there. -/
theorem stateProfile_eventuallyEq_finiteControlProfile
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) (x : AnnularState S) :
    stateProfile D S C x =ᶠ[𝓝 r]
      finiteControlProfile D C (stateControlLocalIndices hC r hr)
        (stateFiniteControlCLM hS hT hRef (stateControlLocalIndices hC r hr) x) := by
  filter_upwards [stateControlLocalIndices_eventuallyEq hC r hr x] with s hs
  let I := stateControlLocalIndices hC r hr
  have hleft : stateProfile D S C x s =
      D.w s * Real.exp (x.2.1 * D.chi s + ∑ m ∈ I, stateKappa S x m * C.control m s) :=
    congrArg (fun t : ℝ => D.w s * Real.exp (x.2.1 * D.chi s + t)) hs
  have hright : finiteControlProfile D C I (stateFiniteControlCLM hS hT hRef I x) s =
      D.w s * Real.exp (x.2.1 * D.chi s + ∑ m ∈ I, stateKappa S x m * C.control m s) := by
    exact (congrArg (fun y : ℝ × (I → ℝ) => finiteControlProfile D C I y s)
      (stateFiniteControlCLM_apply hS hT hRef I x)).trans (by
        exact congrArg
          (fun t : ℝ => D.w s * Real.exp (x.2.1 * D.chi s + t))
          (Finset.sum_coe_sort I (fun m : ℕ => stateKappa S x m * C.control m s)))
  exact hleft.trans hright.symm

/-- Genuine parameter towers for every radial jet of the actual profile.
Local finiteness supplies a single finite formula before any spatial or
parameter differentiation is performed. -/
def stateProfileRadialJetSmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hD : RadialProfileGeometry D)
    (hC : controlGeometryConditions D S C) (hχ : ContDiff ℝ ∞ D.chi)
    (n : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b) :
    SmoothDirections univ (fun x : AnnularState S => iteratedDeriv n (stateProfile D S C x) r) := by
  let indices := stateControlLocalIndices hC r hr
  let L := stateFiniteControlCLM hS hT hRef indices
  let J := smoothDirections_contDiff_comp (smoothDirectionsLinear L) isOpen_univ
    (contDiff_finiteControlProfileJet hD hC hχ indices n r).contDiffOn
    (fun _ _ => mem_univ _)
  apply J.congr
  intro x _
  exact ((stateProfile_eventuallyEq_finiteControlProfile hS hT hRef hC r hr x).iteratedDeriv_eq n).symm

end ContinuousFlexibility.Statements
