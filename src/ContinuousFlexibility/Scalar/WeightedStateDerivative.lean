import ContinuousFlexibility.Scalar.WeightedConservation
import ContinuousFlexibility.Scalar.WeightedStateRegularity
import ContinuousFlexibility.Scalar.S05StateDerivative

/-!
# The actual projective height-state derivative

The finite-dimensional corrected residual identity is compared with point
evaluation of the genuine residual tower.  Decoder injectivity then
identifies the derivative in the original projective topology.  The
normalizing parameter remains independent of the height direction, so the
argument also applies at parameter zero.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem scalarStateProfile_add_heightDirection
    (x : ScalarWeightedState S) (u : ScalarCommonHeight S) (t : ℝ) :
    scalarStateProfile D S (x + t • scalarHeightDirection S u) = scalarStateProfile D S x := by
  funext r
  simp only [scalarStateProfile, scalarHeightDirection, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_zero, add_zero]

theorem scalarStatePrimitive_add_heightDirection
    (x : ScalarWeightedState S) (u : ScalarCommonHeight S) (t : ℝ) :
    scalarStatePrimitive D S (x + t • scalarHeightDirection S u) =
      scalarStatePrimitive D S x := by
  unfold scalarStatePrimitive
  rw [scalarStateProfile_add_heightDirection]

theorem scalarStateIncrement_add_heightDirection
    (x : ScalarWeightedState S) (u : ScalarCommonHeight S) (t : ℝ) :
    scalarStateIncrement S (x + t • scalarHeightDirection S u) =
      heightFamily (scalarStateIncrement S x) (scalarCommonHeightDecode S u) t := by
  funext p
  simp only [scalarStateIncrement, scalarCommonHeightDecode, scalarHeightDirection,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, map_add, map_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, heightFamily]
  ring

theorem scalarStateResidual_add_heightDirection
    (x : ScalarWeightedState S) (u : ScalarCommonHeight S) (t : ℝ) :
    scalarStateResidual D S (x + t • scalarHeightDirection S u) =
      normalizedResidual (scalarStateProfile D S x) (scalarStatePrimitive D S x)
        (heightFamily (scalarStateIncrement S x) (scalarCommonHeightDecode S u) t) x.2 := by
  rw [scalarStateResidual, scalarStateProfile_add_heightDirection,
    scalarStatePrimitive_add_heightDirection, scalarStateIncrement_add_heightDirection]
  simp only [scalarHeightDirection, Prod.snd_add, Prod.smul_snd, smul_zero, add_zero]

/-- The exact corrected formula holds pointwise at every interior physical
point, including at zero value of the independent parameter. -/
theorem hasDerivAt_scalarStateResidual_heightDirection
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {x : ScalarWeightedState S}
    (hg : ScalarStateGeometry D S x) (u : ScalarCommonHeight S)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    HasDerivAt (fun t : ℝ => scalarStateResidual D S (x + t • scalarHeightDirection S u) p)
      (scalarStateOperator D S x u p + x.2 *
        scalarCorrectionError (scalarStateTypeB D S x) (scalarStateResidual D S x)
          (scalarCommonHeightDecode S u) p) 0 := by
  obtain ⟨hw, hh, hu, hhw, _, _, _, _, _, hpositive⟩ := hg
  have hr : p.1 ≠ 0 := (hD.choose_spec.1.1.trans hp.1.1).ne'
  have hdisc : 0 < polarDiscriminant (scalarStateProfile D S x) (scalarStateHeight D S x) p :=
    lt_of_lt_of_le (by norm_num) ((hpositive p.1 hp.1).2 p.2).1
  have hQ : heightQ (profileEnergy (scalarStateProfile D S x) p)
      (heightRadial (scalarStateHeight D S x) p)
      (angularPartial (heightAngular (scalarStateHeight D S x)) p) ≠ 0 :=
    (lt_of_lt_of_le
      (mul_pos (by norm_num : (0 : ℝ) < 7 / 8) (hpositive p.1 hp.1).1)
      ((hpositive p.1 hp.1).2 p.2).2).ne'
  simpa only [scalarStateResidual_add_heightDirection] using
    hasDerivAt_normalizedResidual_corrected hw hh hu
      (scalarCommonHeightDecode_contDiff hT hS u) hhw x.2 hr hdisc hQ

/-- The exact projective derivative clause in `IsWeightedS05` is forced by
the actual residual tower and the three prescribed decoding identities.
No further differentiability hypothesis for a different residual map is
introduced. -/
theorem weightedScalar_stateDerivative_clause
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (W : WeightedScalarData S)
    {U : Set (ScalarWeightedState S)} (J : SmoothDirections U W.residual)
    (hgeometry : ∀ x ∈ U, ScalarStateGeometry D S x)
    (hresidual : ∀ x ∈ U, ∀ p,
      (S.height scalarBeta).decode (W.residual x) p = scalarStateResidual D S x p)
    (hlinear : ∀ x ∈ U, ∀ u p,
      (S.height scalarBeta).decode (W.linear x u) p = scalarStateOperator D S x u p)
    (herror : ∀ x ∈ U, ∀ R u p,
      (S.height scalarBeta).decode (W.error x R u) p =
        scalarCorrectionError (scalarStateTypeB D S x) ((S.height scalarBeta).decode R)
          (scalarCommonHeightDecode S u) p) :
    ∀ x ∈ U, ∀ u,
      HasProjectiveLineDerivAt W.residual
        (W.linear x u + x.2 • W.error x (W.residual x) u) x (scalarHeightDirection S u) := by
  intro x hx u
  let direction : ScalarWeightedState S := scalarHeightDirection S u
  let d : ScalarHeightSpace S := J.D 1 x (Fin.cons direction Fin.elim0)
  have hJ : HasProjectiveLineDerivAt W.residual d x direction := by
    apply (J.derivative 0 x hx Fin.elim0 direction).congr_germ
    filter_upwards [J.open_domain.mem_nhds hx] with y hy
    exact (J.zero y hy).symm
  have hline : Tendsto (fun t : ℝ => x + t • direction) (𝓝 0) (𝓝 x) := by
    have ht : ContinuousAt (fun t : ℝ => x + t • direction) 0 :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
    simpa only [zero_smul, add_zero] using ht.tendsto
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, x + t • direction ∈ U :=
    hline.eventually (J.open_domain.mem_nhds hx)
  have hvalue : d = W.linear x u + x.2 • W.error x (W.residual x) u := by
    apply (hS.1 scalarBeta).2.2.2.2.2.1
    funext p
    by_cases hp : p ∈ annularOpen D
    · let L : ScalarHeightSpace S →L[ℝ] ℝ :=
        (S.height scalarBeta).evaluationCLM ((hS.1 scalarBeta).2.2.1) p
      have hscalar : HasDerivAt
          (fun t : ℝ => (S.height scalarBeta).decode (W.residual (x + t • direction)) p)
          ((S.height scalarBeta).decode d p) 0 := by
        simpa only [L, SobolevModelData.evaluationCLM_apply] using
          (hasDerivAt_iff_tendsto_slope_zero.mpr (hJ.clm_comp L))
      have hres : (S.height scalarBeta).decode (W.residual x) = scalarStateResidual D S x :=
        funext (hresidual x hx)
      have hcandidate :
          (S.height scalarBeta).decode (W.linear x u + x.2 • W.error x (W.residual x) u) p =
          scalarStateOperator D S x u p + x.2 *
            scalarCorrectionError (scalarStateTypeB D S x) (scalarStateResidual D S x)
              (scalarCommonHeightDecode S u) p := by
        simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [hlinear x hx u p, herror x hx (W.residual x) u p, hres]
      have hphysical := hasDerivAt_scalarStateResidual_heightDirection hD hT hS
        (hgeometry x hx) u hp
      have hcorrected : HasDerivAt
          (fun t : ℝ => (S.height scalarBeta).decode (W.residual (x + t • direction)) p)
          ((S.height scalarBeta).decode (W.linear x u + x.2 • W.error x (W.residual x) u) p) 0 := by
        apply (hphysical.congr_deriv hcandidate.symm).congr_of_eventuallyEq
        filter_upwards [hnear] with t ht
        exact hresidual (x + t • direction) ht p
      exact hscalar.unique hcorrected
    · rw [scalarHeight_decode_eq_zero_outside hS d hp,
        scalarHeight_decode_eq_zero_outside hS
          (W.linear x u + x.2 • W.error x (W.residual x) u) hp]
  simpa only [hvalue] using hJ

end ContinuousFlexibility.Statements
