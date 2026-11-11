import ContinuousFlexibility.Analysis.CircleAveragedComposition
import ContinuousFlexibility.Analysis.CircleDifferentialOperators

/-!
# The actual bilinear chart error in the supplied circle model

For a fixed decoded residual e, averaging v' along the segment
theta + travel + a e(theta) is a genuine linear circle operator.
Multiplication, angular differentiation, and the supplied parity
projections then realize the frozen chart-error formula bilinearly.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

def circleErrorAlgebraBilinear
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : E →ₗ[ℝ] E →ₗ[ℝ] E) (D A V Pe Po : E →ₗ[ℝ] E) :
    E →ₗ[ℝ] E →ₗ[ℝ] E where
  toFun r := Pe.comp ((P r).comp (A.comp D)) - (P (D r)).comp (Po.comp V)
  map_add' r s := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_add, LinearMap.add_apply]
    abel
  map_smul' c r := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_smul,
      LinearMap.smul_apply, RingHom.id_apply, smul_sub]

theorem circleErrorAlgebraBilinear_apply
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : E →ₗ[ℝ] E →ₗ[ℝ] E) (D A V Pe Po : E →ₗ[ℝ] E)
    (r v : E) :
    circleErrorAlgebraBilinear P D A V Pe Po r v =
      Pe (P r (A (D v))) - P (D r) (Po (V v)) := rfl

section FixedResidual

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}
  (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
  (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
  (travel : ℕ → ℝ) (e : S.Space)
  (Pe Po : S.Space →L[ℝ] S.Space)

def circleFixedErrorBilinear : S.Space →ₗ[ℝ] S.Space →ₗ[ℝ] S.Space :=
  circleErrorAlgebraBilinear (circleProductBilinear hS hT hD hγ)
    (circleDerivativeLinear hS)
    (circleAverageComposeLinear hS hT hD hγ travel e)
    (circleShiftedChartComposeLinear hS hT hD hγ travel e)
    Pe.toLinearMap Po.toLinearMap

theorem circleFixedErrorBilinear_decode
    (heven : ∀ u m θ, S.decode (Pe u) m θ = evenPart (S.decode u m) θ)
    (hodd : ∀ u m θ, S.decode (Po u) m θ = oddPart (S.decode u m) θ)
    (r v : S.Space) (m : ℕ) (θ : ℝ) :
    S.decode (circleFixedErrorBilinear hS hT hD hγ travel e Pe Po r v) m θ =
      evenPart (fun t => S.decode r m t *
        ∫ a in (0 : ℝ)..1, deriv (S.decode v m)
          (t + travel m + a * S.decode e m t)) θ -
      deriv (S.decode r m) θ *
        oddPart (fun t => S.decode v m (t + travel m + S.decode e m t)) θ := by
  change S.decode
    (Pe (circleProductBilinear hS hT hD hγ r
      (circleAverageComposeLinear hS hT hD hγ travel e (circleDerivativeLinear hS v))) -
      circleProductBilinear hS hT hD hγ (circleDerivativeLinear hS r)
        (Po (circleShiftedChartComposeLinear hS hT hD hγ travel e v))) m θ = _
  simp only [ContinuousLinearMap.coe_coe, map_sub, Pi.sub_apply,
    heven, circleProductBilinear_decode, circleAverageComposeLinear_decode,
    circleDerivativeLinear_decode, hodd, circleShiftedChartComposeLinear_decode,
    evenPart, oddPart]

end FixedResidual

/-- Once the actual residual has been realized in the circle model, its
frozen chart-error formula is represented by a genuine bilinear map. -/
theorem exists_circleChartErrorBilinear_of_residual
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D)
    (z : AnnularState S × ℝ) (e : CircleSpace S)
    (he : (S.circle (3 / 4 : ℝ)).decode e = returnResidualField S C z) :
    ∃ B : CircleSpace S →ₗ[ℝ] CircleSpace S →ₗ[ℝ] CircleSpace S,
      ∀ r v m θ, (S.circle (3 / 4 : ℝ)).decode (B r v) m θ =
        circleChartError S C z r v m θ := by
  let hparity := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (3 / 4 : ℝ)
  let Pe : CircleSpace S →L[ℝ] CircleSpace S := hparity.choose
  let Po : CircleSpace S →L[ℝ] CircleSpace S := hparity.choose_spec.choose
  have heven' (u : CircleSpace S) (n : ℕ) (t : ℝ) :
      (S.circle (3 / 4 : ℝ)).decode (Pe u) n t =
        evenPart ((S.circle (3 / 4 : ℝ)).decode u n) t := by
    simpa only [evenPart] using hparity.choose_spec.choose_spec.1 u n t
  have hodd' (u : CircleSpace S) (n : ℕ) (t : ℝ) :
      (S.circle (3 / 4 : ℝ)).decode (Po u) n t =
        oddPart ((S.circle (3 / 4 : ℝ)).decode u n) t := by
    simpa only [oddPart] using hparity.choose_spec.choose_spec.2.1 u n t
  let B : CircleSpace S →ₗ[ℝ] CircleSpace S →ₗ[ℝ] CircleSpace S :=
    circleFixedErrorBilinear (hS.2.1 (3 / 4 : ℝ)) hT hD
      (by norm_num : (0 : ℝ) < 3 / 4) C.travel e Pe Po
  have hpoint : ∀ (r v : CircleSpace S) (m : ℕ) (θ : ℝ),
      (S.circle (3 / 4 : ℝ)).decode (B r v) m θ =
        circleChartError S C z r v m θ := by
    intro r v m θ
    have hd := circleFixedErrorBilinear_decode (hS.2.1 (3 / 4 : ℝ)) hT hD
      (by norm_num : (0 : ℝ) < 3 / 4) C.travel e Pe Po heven' hodd' r v m θ
    simpa only [he, circleChartError] using hd
  exact Exists.intro B hpoint

end ContinuousFlexibility.Statements
