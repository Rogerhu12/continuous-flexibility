import ContinuousFlexibility.Analysis.N01cStateParameterJets
import ContinuousFlexibility.Analysis.CylinderMixedJets
import ContinuousFlexibility.Radial.RadialHeight
import Mathlib.Order.Filter.Finite

/-!
# Actual mixed parameter and radial derivatives of the controlled profile

Scalar line derivatives identify every verified parameter tower.  On a
normed finite parameter space, they commute with arbitrary radial
derivatives by the existing mixed-coordinate derivative theorem.  Local
finiteness transfers this identity to the original projective state, and
a finite intersection of spatial germs identifies the resulting product
with the actual profile and actual control sums.

The final identity retains the same state, control functions, and
direction vectors.  No relation between a control's index and its physical
support cell is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

section ScalarLineJets

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Iteration of actual ordinary derivatives along the given parameter
directions, with the newest direction first. -/
def parameterLineJet (f : E → ℝ) : (k : ℕ) → (Fin k → E) → E → ℝ
  | 0, _, x => f x
  | k + 1, v, x =>
      deriv (fun t : ℝ => parameterLineJet f k (Fin.tail v) (x + t • v 0)) 0

theorem parameterLineJet_zero (f : E → ℝ) (v : Fin 0 → E) (x : E) :
    parameterLineJet f 0 v x = f x := rfl

theorem parameterLineJet_succ (f : E → ℝ) (k : ℕ)
    (v : Fin (k + 1) → E) (x : E) :
    parameterLineJet f (k + 1) v x =
      deriv (fun t : ℝ => parameterLineJet f k (Fin.tail v) (x + t • v 0)) 0 := rfl

variable [TopologicalSpace E]

/-- The recursion of a genuine tower determines its scalar evaluations. -/
theorem smoothDirections_D_eq_parameterLineJet {f : E → ℝ}
    (J : SmoothDirections univ f) (k : ℕ) :
    ∀ (v : Fin k → E) (x : E), J.D k x v = parameterLineJet f k v x := by
  induction k with
  | zero =>
      intro v x
      have hv : v = Fin.elim0 := Subsingleton.elim _ _
      exact (congrArg (fun w : Fin 0 → E => J.D 0 x w) hv).trans
        (J.zero x (mem_univ x))
  | succ k ih =>
      intro v x
      have hd : HasDerivAt
          (fun t : ℝ => J.D k (x + t • v 0) (Fin.tail v))
          (J.D (k + 1) x (Fin.cons (v 0) (Fin.tail v))) (0 : ℝ) :=
        hasDerivAt_iff_tendsto_slope_zero.mpr
          (J.derivative k x (mem_univ x) (Fin.tail v) (v 0))
      have hderiv : deriv (fun t : ℝ => J.D k (x + t • v 0) (Fin.tail v)) 0 =
          J.D (k + 1) x v := by
        simpa only [Fin.cons_self_tail] using hd.deriv
      have hfun : (fun t : ℝ => J.D k (x + t • v 0) (Fin.tail v)) =
          (fun t : ℝ => parameterLineJet f k (Fin.tail v) (x + t • v 0)) :=
        funext (fun t => ih (Fin.tail v) (x + t • v 0))
      exact hderiv.symm.trans (congrArg (fun g : ℝ → ℝ => deriv g 0) hfun)

/-- The explicit exponential formula is an equality for actual repeated
line differentiation, including the empty product at order zero. -/
theorem parameterLineJet_scaledExpLinear (a : ℝ) (L : E →L[ℝ] ℝ)
    (k : ℕ) (v : Fin k → E) (x : E) :
    parameterLineJet (fun y : E => a * Real.exp (L y)) k v x =
      a * Real.exp (L x) * ∏ i, L (v i) :=
  (smoothDirections_D_eq_parameterLineJet
    (smoothDirections_scaledExpLinear a L) k v x).symm.trans
      (scaledExpLinearJets_apply a L k x v)

end ScalarLineJets

section LinearPrecomposition

variable {E P : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup P] [Module ℝ P]

/-- A linear map transports the affine lines exactly, at every order. -/
theorem parameterLineJet_linear_comp (L : E →ₗ[ℝ] P) (f : P → ℝ) (k : ℕ) :
    ∀ (v : Fin k → E) (x : E),
      parameterLineJet (fun y : E => f (L y)) k v x =
        parameterLineJet f k (fun i => L (v i)) (L x) := by
  induction k with
  | zero => intro v x; rfl
  | succ k ih =>
      intro v x
      simp only [parameterLineJet_succ]
      apply congrArg (fun g : ℝ → ℝ => deriv g 0)
      funext t
      simpa only [map_add, map_smul, Fin.tail_def] using
        ih (Fin.tail v) (x + t • v 0)

end LinearPrecomposition

/-- The existing mixed-coordinate theorem exchanges one first-coordinate
derivative and any number of second-coordinate derivatives. -/
theorem deriv_iteratedDeriv_swap {f : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (t r : ℝ) :
    deriv (fun u => iteratedDeriv n (fun s => f (u, s)) r) t =
      iteratedDeriv n (fun s => deriv (fun u => f (u, s)) t) r := by
  have hpartial : (fun s => deriv (fun u => f (u, s)) t) =
      (fun s => radialPartial f (t, s)) := by
    funext s
    exact (Radial.hasDerivAt_radialSlice (x := (t, s))
      (hf.differentiable (by simp) (t, s))).deriv
  have hcomm := mixedDerivative_radialPartial isOpen_univ hf.contDiffOn 0 n
    (p := (t, r)) (mem_univ (t, r))
  have heq : iteratedDeriv n (fun s => radialPartial f (t, s)) r =
      deriv (fun u => iteratedDeriv n (fun s => f (u, s)) r) t := by
    simpa only [mixedDerivative, iteratedDeriv_zero, zero_add, iteratedDeriv_one] using hcomm
  exact heq.symm.trans
    (congrArg (fun g : ℝ → ℝ => iteratedDeriv n g r) hpartial.symm)

section NormedParameters

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Fixed directional line jets of a jointly smooth scalar family remain
jointly smooth in its normed parameters and radial variable. -/
theorem contDiff_parameterLineJet {f : P → ℝ → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) :
    ∀ v : Fin k → P,
      ContDiff ℝ ∞ (fun z : P × ℝ =>
        parameterLineJet (fun y : P => f y z.2) k v z.1) := by
  induction k with
  | zero =>
      intro v
      simpa only [parameterLineJet_zero, Function.uncurry_def] using hf
  | succ k ih =>
      intro v
      let g : (P × ℝ) → ℝ → ℝ := fun z t =>
        parameterLineJet (fun y : P => f y z.2) k (Fin.tail v) (z.1 + t • v 0)
      have hg : ContDiff ℝ ∞ (Function.uncurry g) :=
        (ih (Fin.tail v)).comp
          (((contDiff_fst.comp contDiff_fst).add
            (contDiff_snd.smul contDiff_const)).prodMk
              (contDiff_snd.comp contDiff_fst))
      have hj : ContDiff ℝ ∞ (fun z : P × ℝ => iteratedDeriv 1 (g z) (0 : ℝ)) :=
        (contDiff_uncurry_iteratedDeriv hg 1).comp
          (contDiff_id.prodMk contDiff_const)
      simpa only [iteratedDeriv_one, parameterLineJet_succ] using hj

/-- Every finite number of parameter line derivatives commutes with every
radial derivative of the jointly smooth family. -/
theorem parameterLineJet_iteratedDeriv {f : P → ℝ → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (n : ℕ) (r : ℝ) (k : ℕ) :
    ∀ (v : Fin k → P) (x : P),
      parameterLineJet (fun y : P => iteratedDeriv n (f y) r) k v x =
        iteratedDeriv n
          (fun s => parameterLineJet (fun y : P => f y s) k v x) r := by
  induction k with
  | zero => intro v x; rfl
  | succ k ih =>
      intro v x
      have hfun :
          (fun t : ℝ => parameterLineJet (fun y : P => iteratedDeriv n (f y) r)
            k (Fin.tail v) (x + t • v 0)) =
          (fun t : ℝ => iteratedDeriv n
            (fun s => parameterLineJet (fun y : P => f y s)
              k (Fin.tail v) (x + t • v 0)) r) :=
        funext (fun t => ih (Fin.tail v) (x + t • v 0))
      have hsmooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
          parameterLineJet (fun y : P => f y z.2) k (Fin.tail v) (x + z.1 • v 0)) :=
        (contDiff_parameterLineJet hf k (Fin.tail v)).comp
          ((contDiff_const.add (contDiff_fst.smul contDiff_const)).prodMk contDiff_snd)
      exact (congrArg (fun g : ℝ → ℝ => deriv g 0) hfun).trans
        (deriv_iteratedDeriv_swap hsmooth n 0 r)

end NormedParameters

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency true

/-- The exponent of the finite control formula is a genuine continuous
linear functional of its finite parameters. -/
def finiteControlExponentCLM (D : ReferenceData) {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (I : Finset ℕ) (r : ℝ) :
    (ℝ × (I → ℝ)) →L[ℝ] ℝ :=
  D.chi r • ContinuousLinearMap.fst ℝ ℝ (I → ℝ) +
    ∑ m : I, C.control m r •
      (ContinuousLinearMap.proj m).comp (ContinuousLinearMap.snd ℝ ℝ (I → ℝ))

theorem finiteControlExponentCLM_apply (D : ReferenceData) {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (I : Finset ℕ) (r : ℝ) (y : ℝ × (I → ℝ)) :
    finiteControlExponentCLM D C I r y =
      y.1 * D.chi r + ∑ m : I, y.2 m * C.control m r := by
  simp only [finiteControlExponentCLM, add_apply, sum_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  exact congrArg₂ (· + ·) (mul_comm _ _)
    (Finset.sum_congr rfl (fun _ _ => mul_comm _ _))

theorem parameterLineJet_finiteControlProfile (D : ReferenceData)
    {S : PhysicalSpacesData} (C : NonlinearGeometryData S) (I : Finset ℕ)
    (r : ℝ) (k : ℕ) (v : Fin k → ℝ × (I → ℝ)) (x : ℝ × (I → ℝ)) :
    parameterLineJet (fun y => finiteControlProfile D C I y r) k v x =
      finiteControlProfile D C I x r *
        ∏ i, finiteControlExponentCLM D C I r (v i) := by
  let L := finiteControlExponentCLM D C I r
  have hfun : (fun y : ℝ × (I → ℝ) => D.w r * Real.exp (L y)) =
      (fun y : ℝ × (I → ℝ) => finiteControlProfile D C I y r) := by
    funext y
    exact congrArg (fun t : ℝ => D.w r * Real.exp t)
      (finiteControlExponentCLM_apply D C I r y)
  calc
    parameterLineJet (fun y => finiteControlProfile D C I y r) k v x =
        parameterLineJet (fun y => D.w r * Real.exp (L y)) k v x :=
      congrArg (fun f : (ℝ × (I → ℝ)) → ℝ => parameterLineJet f k v x) hfun.symm
    _ = D.w r * Real.exp (L x) * ∏ i, L (v i) :=
      parameterLineJet_scaledExpLinear (D.w r) L k v x
    _ = finiteControlProfile D C I x r * ∏ i, L (v i) :=
      congrArg (fun t : ℝ => t * ∏ i, L (v i)) (congrFun hfun x)

/- Reuse the actual state instances, keeping elaboration at the public
product type when the finite-parameter identities are specialized. -/
private abbrev mixedStateTopology (S : PhysicalSpacesData) :
    TopologicalSpace (AnnularState S) := inferInstance
attribute [local instance] mixedStateTopology

private abbrev mixedStateGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := inferInstance
attribute [local instance] mixedStateGroup

private abbrev mixedStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := inferInstance
attribute [local instance] mixedStateModule

private abbrev mixedStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) :=
  (mixedStateModule S).toDistribMulAction.toDistribSMul.toSMul
attribute [local instance] mixedStateSMul

/-- Substituting the actual finite parameter tuple gives the original
finite sum of decoded control means. -/
theorem finiteControlExponentCLM_stateFiniteControlCLM
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (I : Finset ℕ) (s : ℝ) (x : AnnularState S) :
    finiteControlExponentCLM D C I s (stateFiniteControlCLM hS hT hRef I x) =
      x.2.1 * D.chi s + ∑ m ∈ I, stateKappa S x m * C.control m s := by
  have htuple := congrArg (finiteControlExponentCLM D C I s)
    (stateFiniteControlCLM_apply hS hT hRef I x)
  have heval := finiteControlExponentCLM_apply D C I s
    (x.2.1, fun m : I => stateKappa S x m)
  have hsum := congrArg (fun t : ℝ => x.2.1 * D.chi s + t)
    (Finset.sum_coe_sort I (fun m : ℕ => stateKappa S x m * C.control m s))
  exact htuple.trans (heval.trans hsum)

/-- The actual radial-jet tower equals radial differentiation of the
finite parameter line jets.  Both orders are arbitrary and independent. -/
theorem stateProfileRadialJetSmoothDirections_D_eq_finiteLineJet
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hD : RadialProfileGeometry D)
    (hC : controlGeometryConditions D S C) (hχ : ContDiff ℝ ∞ D.chi)
    (n k : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b)
    (x : AnnularState S) (v : Fin k → AnnularState S) :
    let I := stateControlLocalIndices hC r hr
    let L := stateFiniteControlCLM hS hT hRef I
    (stateProfileRadialJetSmoothDirections hS hT hRef hD hC hχ n r hr).D k x v =
      iteratedDeriv n
        (fun s => parameterLineJet (fun y => finiteControlProfile D C I y s)
          k (fun i => L (v i)) (L x)) r := by
  let I := stateControlLocalIndices hC r hr
  let L := stateFiniteControlCLM hS hT hRef I
  have hfun : (fun y : AnnularState S => iteratedDeriv n (stateProfile D S C y) r) =
      (fun y : AnnularState S => iteratedDeriv n (finiteControlProfile D C I (L y)) r) :=
    funext (fun y =>
      (stateProfile_eventuallyEq_finiteControlProfile hS hT hRef hC r hr y).iteratedDeriv_eq n)
  calc
    (stateProfileRadialJetSmoothDirections hS hT hRef hD hC hχ n r hr).D k x v =
        parameterLineJet (fun y : AnnularState S =>
          iteratedDeriv n (stateProfile D S C y) r) k v x :=
      smoothDirections_D_eq_parameterLineJet
        (stateProfileRadialJetSmoothDirections hS hT hRef hD hC hχ n r hr) k v x
    _ = parameterLineJet (fun y : AnnularState S =>
          iteratedDeriv n (finiteControlProfile D C I (L y)) r) k v x :=
      congrArg (fun f : AnnularState S → ℝ => parameterLineJet f k v x) hfun
    _ = parameterLineJet (fun y : ℝ × (I → ℝ) =>
          iteratedDeriv n (finiteControlProfile D C I y) r) k (fun i => L (v i)) (L x) :=
      parameterLineJet_linear_comp L.toLinearMap
        (fun y => iteratedDeriv n (finiteControlProfile D C I y) r) k v x
    _ = iteratedDeriv n
        (fun s => parameterLineJet (fun y => finiteControlProfile D C I y s)
          k (fun i => L (v i)) (L x)) r :=
      parameterLineJet_iteratedDeriv (contDiff_finiteControlProfile hD hC hχ I)
        n r k (fun i => L (v i)) (L x)

/-- Only the fixed base state and the finitely many given direction states
are needed to compare the product on a spatial neighbourhood. -/
theorem stateProfileParameterProduct_eventuallyEq_finiteProduct
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (k : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b)
    (x : AnnularState S) (v : Fin k → AnnularState S) :
    let I := stateControlLocalIndices hC r hr
    let L := stateFiniteControlCLM hS hT hRef I
    (fun s => stateProfile D S C x s *
      ∏ i, ((v i).2.1 * D.chi s + stateControlSum C (v i) s)) =ᶠ[𝓝 r]
    (fun s => finiteControlProfile D C I (L x) s *
      ∏ i, finiteControlExponentCLM D C I s (L (v i))) := by
  let I := stateControlLocalIndices hC r hr
  let L := stateFiniteControlCLM hS hT hRef I
  have hexponent (i : Fin k) :
      (fun s => (v i).2.1 * D.chi s + stateControlSum C (v i) s) =ᶠ[𝓝 r]
      (fun s => finiteControlExponentCLM D C I s (L (v i))) := by
    filter_upwards [stateControlLocalIndices_eventuallyEq hC r hr (v i)] with s hs
    exact (congrArg (fun t : ℝ => (v i).2.1 * D.chi s + t) hs).trans
      (finiteControlExponentCLM_stateFiniteControlCLM hS hT hRef I s (v i)).symm
  have hdirections : ∀ᶠ s in 𝓝 r, ∀ i : Fin k,
      (v i).2.1 * D.chi s + stateControlSum C (v i) s =
        finiteControlExponentCLM D C I s (L (v i)) :=
    Filter.eventually_all.2 hexponent
  filter_upwards [stateProfile_eventuallyEq_finiteControlProfile hS hT hRef hC r hr x,
    hdirections] with s hprofile hdir
  exact congrArg₂ (· * ·) hprofile (Finset.prod_congr rfl (fun i _ => hdir i))

/-- Exact all-order mixed derivative identity for the actual controlled
profile.  The right side contains its genuine profile and genuine exponent
direction factors, with no independently supplied derivative fields. -/
theorem stateProfileRadialJetSmoothDirections_D_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hD : RadialProfileGeometry D)
    (hC : controlGeometryConditions D S C) (hχ : ContDiff ℝ ∞ D.chi)
    (n k : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b)
    (x : AnnularState S) (v : Fin k → AnnularState S) :
    (stateProfileRadialJetSmoothDirections hS hT hRef hD hC hχ n r hr).D k x v =
      iteratedDeriv n (fun s => stateProfile D S C x s *
        ∏ i, ((v i).2.1 * D.chi s + stateControlSum C (v i) s)) r := by
  let I := stateControlLocalIndices hC r hr
  let L := stateFiniteControlCLM hS hT hRef I
  have hformula :
      (fun s => parameterLineJet (fun y => finiteControlProfile D C I y s)
        k (fun i => L (v i)) (L x)) =
      (fun s => finiteControlProfile D C I (L x) s *
        ∏ i, finiteControlExponentCLM D C I s (L (v i))) :=
    funext (fun s => parameterLineJet_finiteControlProfile D C I s k
      (fun i => L (v i)) (L x))
  have hfinite := stateProfileRadialJetSmoothDirections_D_eq_finiteLineJet
    hS hT hRef hD hC hχ n k r hr x v
  have hactual := stateProfileParameterProduct_eventuallyEq_finiteProduct
    hS hT hRef hC k r hr x v
  exact hfinite.trans ((congrArg (fun f : ℝ → ℝ => iteratedDeriv n f r) hformula).trans
    (hactual.iteratedDeriv_eq n).symm)

end ContinuousFlexibility.Statements
