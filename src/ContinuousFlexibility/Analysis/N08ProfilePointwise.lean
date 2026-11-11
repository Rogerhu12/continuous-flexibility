import ContinuousFlexibility.Analysis.N08StateProjection
import ContinuousFlexibility.Analysis.StateProfileRegularity

/-!
# Actual linear logarithmic profiles and their parameter derivatives

Disjoint control supports make the defining series a finite sum at each
radial point. Angular averaging is the actual continuous circle projection.
Together these facts give a continuous linear logarithmic profile in the
pointwise topology and the exact exponential derivative of the physical
profile. No weighted height realization is assumed in this construction.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S}

private def n08_circleDecodeCLM (hS : IsPhysicalSpaces D T S) :
    CircleSpace S →L[ℝ] (ℕ → ℝ → ℝ) where
  toLinearMap := (S.circle (3 / 4 : ℝ)).decode
  cont := (hS.2.1 (3 / 4 : ℝ)).2.2.1

private def n08_stateControlCoordinate (S : PhysicalSpacesData) :
    AnnularState S →L[ℝ] CircleSpace S :=
  (ContinuousLinearMap.fst ℝ (CircleSpace S) (CircleSpace S)).comp
    ((ContinuousLinearMap.snd ℝ ℝ (CircleSpace S × CircleSpace S)).comp
      (ContinuousLinearMap.snd ℝ (HeightPair S) (ℝ × (CircleSpace S × CircleSpace S))))

private def n08_stateNuCoordinate (S : PhysicalSpacesData) : AnnularState S →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (CircleSpace S × CircleSpace S)).comp
    (ContinuousLinearMap.snd ℝ (HeightPair S) (ℝ × (CircleSpace S × CircleSpace S)))

/-- The actual unweighted mean of one control coordinate is continuous linear. -/
def n08_stateKappaEvalCLM (hS : IsPhysicalSpaces D T S) (m : ℕ) :
    AnnularState S →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (0 : ℝ)).comp
    ((ContinuousLinearMap.proj m).comp
      ((n08_circleDecodeCLM hS).comp
        ((circleAngularMeanProjection (hS.2.1 (3 / 4 : ℝ))).comp
          (n08_stateControlCoordinate S))))

theorem n08_stateKappaEvalCLM_apply (hS : IsPhysicalSpaces D T S)
    (m : ℕ) (x : AnnularState S) :
    n08_stateKappaEvalCLM hS m x = stateKappa S x m :=
  circleAngularMeanProjection_decode (hS.2.1 (3 / 4 : ℝ)) x.2.2.1 m 0

theorem n08_stateKappa_add (hS : IsPhysicalSpaces D T S)
    (x y : AnnularState S) (m : ℕ) :
    stateKappa S (x + y) m = stateKappa S x m + stateKappa S y m := by
  simpa only [n08_stateKappaEvalCLM_apply] using (n08_stateKappaEvalCLM hS m).map_add x y

theorem n08_stateKappa_smul (hS : IsPhysicalSpaces D T S)
    (a : ℝ) (x : AnnularState S) (m : ℕ) :
    stateKappa S (a • x) m = a * stateKappa S x m := by
  simpa only [n08_stateKappaEvalCLM_apply, smul_eq_mul] using
    (n08_stateKappaEvalCLM hS m).map_smul a x

/-- At a fixed radial point, at most one control is nonzero. -/
theorem n08_controlActive_subsingleton (hC : controlGeometryConditions D S C) (r : ℝ) :
    Set.Subsingleton {m : ℕ | C.control m r ≠ 0} := by
  intro i hi j hj
  by_contra hij
  have hdisjoint := hC.2.2.1 i j hij
  have hsupport := hC.2.2.2.2.2.1
  exact Set.disjoint_left.mp hdisjoint ((hsupport i).2.2 hi) ((hsupport j).2.2 hj)

private def n08_controlActive (hC : controlGeometryConditions D S C) (r : ℝ) : Finset ℕ :=
  (n08_controlActive_subsingleton hC r).finite.toFinset

private theorem n08_mem_controlActive (hC : controlGeometryConditions D S C) (r : ℝ) (m : ℕ) :
    m ∈ n08_controlActive hC r ↔ C.control m r ≠ 0 :=
  Set.Finite.mem_toFinset _

/-- The defining infinite series agrees with its actual finite active sum. -/
theorem n08_stateControlSum_eq_sum (hC : controlGeometryConditions D S C)
    (x : AnnularState S) (r : ℝ) :
    stateControlSum C x r =
      ∑ m ∈ n08_controlActive hC r, C.control m r * stateKappa S x m := by
  classical
  unfold stateControlSum
  rw [tsum_eq_sum (s := n08_controlActive hC r) (fun m hm => by
    have hz : C.control m r = 0 := not_not.mp (mt (n08_mem_controlActive hC r m).mpr hm)
    rw [hz, mul_zero])]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- Evaluation of the actual control series, without a summability assumption. -/
def n08_stateControlEvalCLM (hS : IsPhysicalSpaces D T S)
    (hC : controlGeometryConditions D S C) (r : ℝ) : AnnularState S →L[ℝ] ℝ :=
  ∑ m ∈ n08_controlActive hC r, C.control m r • n08_stateKappaEvalCLM hS m

theorem n08_stateControlEvalCLM_apply (hS : IsPhysicalSpaces D T S)
    (hC : controlGeometryConditions D S C) (r : ℝ) (x : AnnularState S) :
    n08_stateControlEvalCLM hS hC r x = stateControlSum C x r := by
  rw [n08_stateControlSum_eq_sum hC]
  simp only [n08_stateControlEvalCLM, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, n08_stateKappaEvalCLM_apply]

/-- The literal logarithmic perturbation used in `stateProfile`. -/
def n08_stateLogProfile (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (x : AnnularState S) (r : ℝ) : ℝ :=
  x.2.1 * D.chi r + stateControlSum C x r

def n08_logProfileEvalCLM (hS : IsPhysicalSpaces D T S)
    (hC : controlGeometryConditions D S C) (r : ℝ) : AnnularState S →L[ℝ] ℝ :=
  D.chi r • n08_stateNuCoordinate S + n08_stateControlEvalCLM hS hC r

theorem n08_logProfileEvalCLM_apply (hS : IsPhysicalSpaces D T S)
    (hC : controlGeometryConditions D S C) (r : ℝ) (x : AnnularState S) :
    n08_logProfileEvalCLM hS hC r x = n08_stateLogProfile D S C x r := by
  simp only [n08_logProfileEvalCLM, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, n08_stateControlEvalCLM_apply]
  change D.chi r * x.2.1 + stateControlSum C x r =
    x.2.1 * D.chi r + stateControlSum C x r
  rw [mul_comm (D.chi r)]

/-- The logarithmic profile as an actual continuous linear map to the
pointwise function space; weighted realization is a separate estimate. -/
def n08_logProfilePointwiseCLM (hS : IsPhysicalSpaces D T S)
    (hC : controlGeometryConditions D S C) : AnnularState S →L[ℝ] (ℝ → ℝ) :=
  ContinuousLinearMap.pi (fun r => n08_logProfileEvalCLM hS hC r)

theorem n08_logProfilePointwiseCLM_apply (hS : IsPhysicalSpaces D T S)
    (hC : controlGeometryConditions D S C) (x : AnnularState S) (r : ℝ) :
    n08_logProfilePointwiseCLM hS hC x r = n08_stateLogProfile D S C x r :=
  n08_logProfileEvalCLM_apply hS hC r x

theorem n08_stateLogProfile_affine (hS : IsPhysicalSpaces D T S)
    (hC : controlGeometryConditions D S C) (x v : AnnularState S) (t r : ℝ) :
    n08_stateLogProfile D S C (x + t • v) r =
      n08_stateLogProfile D S C x r + t * n08_stateLogProfile D S C v r := by
  simp only [← n08_logProfileEvalCLM_apply hS hC, map_add, map_smul, smul_eq_mul]

theorem n08_stateProfile_affine (hS : IsPhysicalSpaces D T S)
    (hC : controlGeometryConditions D S C) (x v : AnnularState S) (t r : ℝ) :
    stateProfile D S C (x + t • v) r =
      stateProfile D S C x r * Real.exp (t * n08_stateLogProfile D S C v r) := by
  change D.w r * Real.exp (n08_stateLogProfile D S C (x + t • v) r) =
    (D.w r * Real.exp (n08_stateLogProfile D S C x r)) *
      Real.exp (t * n08_stateLogProfile D S C v r)
  rw [n08_stateLogProfile_affine hS hC, Real.exp_add, mul_assoc]

/-- This is the derivative of the actual infinite-control physical profile,
including every circle direction and every state outside the sector. -/
theorem n08_stateProfile_hasDerivAt (hS : IsPhysicalSpaces D T S)
    (hC : controlGeometryConditions D S C) (x v : AnnularState S) (r : ℝ) :
    HasDerivAt (fun t : ℝ => stateProfile D S C (x + t • v) r)
      (stateProfile D S C x r * n08_stateLogProfile D S C v r) 0 := by
  have h : HasDerivAt
      (fun t : ℝ => Real.exp (t * n08_stateLogProfile D S C v r))
      (n08_stateLogProfile D S C v r) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (n08_stateLogProfile D S C v r)).exp
  simpa only [n08_stateProfile_affine hS hC] using h.const_mul (stateProfile D S C x r)

theorem n08_stateLogProfile_nuDirection (a : ℝ) (r : ℝ) :
    n08_stateLogProfile D S C (0, a, 0, 0) r = a * D.chi r := by
  simp only [n08_stateLogProfile, stateControlSum, stateKappa, map_zero,
    Pi.zero_apply, angularMean, intervalIntegral.integral_zero, mul_zero, zero_mul,
    tsum_zero, add_zero]

theorem n08_stateLogProfile_kappaDirection (u : CircleSpace S) (r : ℝ) :
    n08_stateLogProfile D S C (0, 0, u, 0) r =
      ∑' m, angularMean ((S.circle (3 / 4 : ℝ)).decode u m) * C.control m r := by
  simp only [n08_stateLogProfile, stateControlSum, stateKappa, zero_mul, zero_add]

end ContinuousFlexibility.Statements
