module

public import ContinuousFlexibility.Analysis.CoupledStateScalarAction
public import ContinuousFlexibility.Analysis.SolveCircleProjection
public import ContinuousFlexibility.Analysis.StateProfileRegularity

/-!
# Actual linear logarithmic profiles and their parameter derivatives

Disjoint control supports make the defining series a finite sum at each
radial point. Angular averaging is the actual continuous circle projection.
Together these facts give a continuous linear logarithmic profile in the
pointwise topology and the exact exponential derivative of the physical
profile. No weighted height realization is assumed in this construction.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem coupled_sum_smul_clm_apply {E I : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (s : Finset I) (a : I → ℝ) (L : I → E →L[ℝ] ℝ) (x : E) :
    (∑ i ∈ s, a i • L i) x = ∑ i ∈ s, a i * L i x := by
  simp only [sum_apply, smul_apply, smul_eq_mul]

private theorem coupled_clm_affine {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (L : E →L[ℝ] ℝ) (x v : E) (t : ℝ) :
    L (x + coupledScalarAction t v) = L x + t * L v := by
  simp only [coupledScalarAction, map_add, map_smul, smul_eq_mul]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S}

private def coupled_circleDecodeCLM (hS : IsPhysicalSpaces D T S) :
    CircleSpace S →L[ℝ] (ℕ → ℝ → ℝ) where
  toLinearMap := (S.circle (3 / 4 : ℝ)).decode
  cont := (hS.2.1 (3 / 4 : ℝ)).2.2.1

private def coupled_stateControlCoordinate (S : PhysicalSpacesData) :
    AnnularState S →L[ℝ] CircleSpace S :=
  (ContinuousLinearMap.fst ℝ (CircleSpace S) (CircleSpace S)).comp
    ((ContinuousLinearMap.snd ℝ ℝ (CircleSpace S × CircleSpace S)).comp
      (ContinuousLinearMap.snd ℝ (HeightPair S) (ℝ × (CircleSpace S × CircleSpace S))))

private def coupled_stateNuCoordinate (S : PhysicalSpacesData) : AnnularState S →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (CircleSpace S × CircleSpace S)).comp
    (ContinuousLinearMap.snd ℝ (HeightPair S) (ℝ × (CircleSpace S × CircleSpace S)))

/-- The actual unweighted mean of one control coordinate is continuous linear. -/
def coupled_stateKappaEvalCLM (hS : IsPhysicalSpaces D T S) (m : ℕ) :
    AnnularState S →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (0 : ℝ)).comp
    ((ContinuousLinearMap.proj m).comp
      ((coupled_circleDecodeCLM hS).comp
        ((circleAngularMeanProjection (hS.2.1 (3 / 4 : ℝ))).comp
          (coupled_stateControlCoordinate S))))

theorem coupled_stateKappaEvalCLM_apply (hS : IsPhysicalSpaces D T S)
    (m : ℕ) (x : AnnularState S) :
    coupled_stateKappaEvalCLM hS m x = stateKappa S x m :=
  circleAngularMeanProjection_decode (hS.2.1 (3 / 4 : ℝ)) x.2.2.1 m 0

theorem coupled_stateKappa_add (hS : IsPhysicalSpaces D T S)
    (x y : AnnularState S) (m : ℕ) :
    stateKappa S (x + y) m = stateKappa S x m + stateKappa S y m := by
  simpa only [coupled_stateKappaEvalCLM_apply] using (coupled_stateKappaEvalCLM hS m).map_add x y

theorem coupled_stateKappa_smul (hS : IsPhysicalSpaces D T S)
    (a : ℝ) (x : AnnularState S) (m : ℕ) :
    stateKappa S (coupledScalarAction (E := AnnularState S) a x) m = a * stateKappa S x m := by
  simpa only [ContinuousLinearMap.coe_coe, coupled_stateKappaEvalCLM_apply,
    coupledScalarAction_real] using
    coupledScalarAction_map (coupled_stateKappaEvalCLM hS m).toLinearMap a x

/-- At a fixed radial point, at most one control is nonzero. -/
theorem coupled_controlActive_subsingleton (hC : controlGeometryConditions D S C) (r : ℝ) :
    Set.Subsingleton {m : ℕ | C.control m r ≠ 0} := by
  intro i hi j hj
  by_contra hij
  have hdisjoint := hC.2.2.1 i j hij
  exact Set.disjoint_left.mp hdisjoint (hC.support_subset i hi) (hC.support_subset j hj)

private def coupled_controlActive (hC : controlGeometryConditions D S C) (r : ℝ) : Finset ℕ :=
  (coupled_controlActive_subsingleton hC r).finite.toFinset

private theorem coupled_mem_controlActive (hC : controlGeometryConditions D S C) (r : ℝ) (m : ℕ) :
    m ∈ coupled_controlActive hC r ↔ C.control m r ≠ 0 :=
  Set.Finite.mem_toFinset _

/-- The defining infinite series agrees with its actual finite active sum. -/
theorem coupled_stateControlSum_eq_sum (hC : controlGeometryConditions D S C)
    (x : AnnularState S) (r : ℝ) :
    stateControlSum C x r =
      ∑ m ∈ coupled_controlActive hC r, C.control m r * stateKappa S x m := by
  classical
  unfold stateControlSum
  rw [tsum_eq_sum (s := coupled_controlActive hC r) (fun m hm => by
    have hz : C.control m r = 0 := not_not.mp (mt (coupled_mem_controlActive hC r m).mpr hm)
    rw [hz, mul_zero])]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- Evaluation of the actual control series, without a summability assumption. -/
def coupled_stateControlEvalCLM (hS : IsPhysicalSpaces D T S)
    (hC : controlGeometryConditions D S C) (r : ℝ) : AnnularState S →L[ℝ] ℝ :=
  ∑ m ∈ coupled_controlActive hC r, C.control m r • coupled_stateKappaEvalCLM hS m

theorem coupled_stateControlEvalCLM_apply (hS : IsPhysicalSpaces D T S)
    (hC : controlGeometryConditions D S C) (r : ℝ) (x : AnnularState S) :
    coupled_stateControlEvalCLM hS hC r x = stateControlSum C x r := by
  calc
    _ = ∑ m ∈ coupled_controlActive hC r, C.control m r * coupled_stateKappaEvalCLM hS m x :=
      coupled_sum_smul_clm_apply (coupled_controlActive hC r) (fun m => C.control m r)
        (coupled_stateKappaEvalCLM hS) x
    _ = ∑ m ∈ coupled_controlActive hC r, C.control m r * stateKappa S x m :=
      Finset.sum_congr rfl (fun m _ =>
        congrArg (fun a : ℝ => C.control m r * a) (coupled_stateKappaEvalCLM_apply hS m x))
    _ = stateControlSum C x r := (coupled_stateControlSum_eq_sum hC x r).symm

/-- The literal logarithmic perturbation used in `stateProfile`. -/
def coupled_stateLogProfile (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (x : AnnularState S) (r : ℝ) : ℝ :=
  x.2.1 * D.chi r + stateControlSum C x r

def coupled_logProfileEvalCLM (hS : IsPhysicalSpaces D T S)
    (hC : controlGeometryConditions D S C) (r : ℝ) : AnnularState S →L[ℝ] ℝ :=
  D.chi r • coupled_stateNuCoordinate S + coupled_stateControlEvalCLM hS hC r

theorem coupled_logProfileEvalCLM_apply (hS : IsPhysicalSpaces D T S)
    (hC : controlGeometryConditions D S C) (r : ℝ) (x : AnnularState S) :
    coupled_logProfileEvalCLM hS hC r x = coupled_stateLogProfile D S C x r := by
  simp only [coupled_logProfileEvalCLM, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, coupled_stateControlEvalCLM_apply]
  change D.chi r * x.2.1 + stateControlSum C x r =
    x.2.1 * D.chi r + stateControlSum C x r
  rw [mul_comm (D.chi r)]

/-- The logarithmic profile as an actual continuous linear map to the
pointwise function space; weighted realization is a separate estimate. -/
def coupled_logProfilePointwiseCLM (hS : IsPhysicalSpaces D T S)
    (hC : controlGeometryConditions D S C) : AnnularState S →L[ℝ] (ℝ → ℝ) :=
  ContinuousLinearMap.pi (fun r => coupled_logProfileEvalCLM hS hC r)

theorem coupled_logProfilePointwiseCLM_apply (hS : IsPhysicalSpaces D T S)
    (hC : controlGeometryConditions D S C) (x : AnnularState S) (r : ℝ) :
    coupled_logProfilePointwiseCLM hS hC x r = coupled_stateLogProfile D S C x r :=
  coupled_logProfileEvalCLM_apply hS hC r x

theorem coupled_stateLogProfile_affine (hS : IsPhysicalSpaces D T S)
    (hC : controlGeometryConditions D S C) (x v : AnnularState S) (t r : ℝ) :
    coupled_stateLogProfile D S C (x + coupledScalarAction (E := AnnularState S) t v) r =
      coupled_stateLogProfile D S C x r + t * coupled_stateLogProfile D S C v r := by
  simpa only [coupled_logProfileEvalCLM_apply] using
    coupled_clm_affine (coupled_logProfileEvalCLM hS hC r) x v t

theorem coupled_stateProfile_affine (hS : IsPhysicalSpaces D T S)
    (hC : controlGeometryConditions D S C) (x v : AnnularState S) (t r : ℝ) :
    stateProfile D S C (x + coupledScalarAction (E := AnnularState S) t v) r =
      stateProfile D S C x r * Real.exp (t * coupled_stateLogProfile D S C v r) := by
  change D.w r * Real.exp (coupled_stateLogProfile D S C
      (x + coupledScalarAction (E := AnnularState S) t v) r) =
    (D.w r * Real.exp (coupled_stateLogProfile D S C x r)) *
      Real.exp (t * coupled_stateLogProfile D S C v r)
  rw [coupled_stateLogProfile_affine hS hC, Real.exp_add, mul_assoc]

/-- This is the derivative of the actual infinite-control physical profile,
including every circle direction and every state outside the sector. -/
theorem coupled_stateProfile_hasDerivAt (hS : IsPhysicalSpaces D T S)
    (hC : controlGeometryConditions D S C) (x v : AnnularState S) (r : ℝ) :
    HasDerivAt (fun t : ℝ => stateProfile D S C (x + coupledScalarAction (E := AnnularState S) t v) r)
      (stateProfile D S C x r * coupled_stateLogProfile D S C v r) 0 := by
  have h : HasDerivAt
      (fun t : ℝ => Real.exp (t * coupled_stateLogProfile D S C v r))
      (coupled_stateLogProfile D S C v r) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (coupled_stateLogProfile D S C v r)).exp
  simpa only [coupled_stateProfile_affine hS hC] using h.const_mul (stateProfile D S C x r)

end ContinuousFlexibility.Statements
