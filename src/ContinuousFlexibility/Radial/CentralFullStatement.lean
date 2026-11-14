module

public import ContinuousFlexibility.Radial.CentralStatementBridges
public import ContinuousFlexibility.Radial.CentralAuxiliaryBorder
public import ContinuousFlexibility.Radial.CentralRadialFlatTests

/-!
# The complete central-model statement

The output scalar is reflected to match the independently frozen target.
The larger radial test class is handled by the genuine flat-test extension.
All thirteen clauses of R03 retain their original quantifiers and domains.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false

def centralAuxiliaryScalarReflection (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : (E × ℝ) →L[ℝ] (E × ℝ) :=
  (ContinuousLinearMap.fst ℝ E ℝ).prod (-(ContinuousLinearMap.snd ℝ E ℝ))

theorem centralAuxiliaryScalarReflection_apply (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (u : E) (c : ℝ) :
    centralAuxiliaryScalarReflection E (u, c) = (u, -c) := rfl

theorem centralAuxiliaryScalarReflection_norm (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (p : E × ℝ) :
    ‖centralAuxiliaryScalarReflection E p‖ = ‖p‖ := by
  change max ‖p.1‖ ‖-p.2‖ = max ‖p.1‖ ‖p.2‖
  rw [norm_neg]

theorem centralAuxiliaryScalarReflection_involutive (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (p : E × ℝ) :
    centralAuxiliaryScalarReflection E (centralAuxiliaryScalarReflection E p) = p := by
  change (p.1, -(-p.2)) = p
  simp only [neg_neg, Prod.mk.eta]

/-- Only the output scalar is reflected; the prescribed row input is unchanged. -/
def centralAuxiliaryStatementInverse {scale : ℝ} (hscale : 0 < scale) :
    (CentralRadialHilbert scale × ℝ) →L[ℝ] (CentralRadialHilbert scale × ℝ) :=
  (centralAuxiliaryScalarReflection (CentralRadialHilbert scale)).comp
    (centralAuxiliaryPhysicalInverse hscale)

theorem centralAuxiliaryStatementInverse_solves {scale : ℝ} (hscale : 0 < scale)
    (F : CentralRadialHilbert scale) (t : ℝ) :
    CentralAuxiliaryPhysicalEquation hscale F t
      (centralAuxiliaryStatementInverse hscale (F, t)).1
      (-(centralAuxiliaryStatementInverse hscale (F, t)).2) := by
  change CentralAuxiliaryPhysicalEquation hscale F t
    (centralAuxiliaryPhysicalInverse hscale (F, t)).1
    (-(-(centralAuxiliaryPhysicalInverse hscale (F, t)).2))
  simpa only [neg_neg] using centralAuxiliaryPhysicalInverse_solves hscale F t

theorem centralAuxiliaryStatementInverse_unique {scale : ℝ} (hscale : 0 < scale)
    (F : CentralRadialHilbert scale) (t : ℝ) (u : CentralRadialHilbert scale) (c : ℝ)
    (hu : CentralAuxiliaryPhysicalEquation hscale F t u (-c)) :
    centralAuxiliaryStatementInverse hscale (F, t) = (u, c) := by
  have h := centralAuxiliaryPhysicalInverse_unique hscale F t u (-c) hu
  change centralAuxiliaryScalarReflection (CentralRadialHilbert scale)
    (centralAuxiliaryPhysicalInverse hscale (F, t)) = (u, c)
  rw [← h, centralAuxiliaryScalarReflection_apply, neg_neg]

theorem centralAuxiliaryStatementInverse_norm_le {scale : ℝ} (hscale : 0 < scale) :
    ‖centralAuxiliaryStatementInverse hscale‖ ≤ ‖centralAuxiliaryInverse‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro p
  calc
    ‖centralAuxiliaryStatementInverse hscale p‖ =
        ‖centralAuxiliaryPhysicalInverse hscale p‖ :=
      centralAuxiliaryScalarReflection_norm _ _
    _ = ‖centralAuxiliaryInverse (centralAuxiliaryPairEquiv hscale p)‖ := by
      rw [← (centralAuxiliaryPairEquiv hscale).norm_map,
        centralAuxiliaryPhysicalInverse_transform]
    _ ≤ ‖centralAuxiliaryInverse‖ * ‖centralAuxiliaryPairEquiv hscale p‖ :=
      centralAuxiliaryInverse.le_opNorm _
    _ = _ := by rw [(centralAuxiliaryPairEquiv hscale).norm_map]

/-- This change of variables is valid even when the Bochner integral is zero
by nonintegrability; no positivity or integrability premise on g is added. -/
theorem bridge_centralRadialSpectral_integral_density {scale : ℝ}
    (hscale : 0 < scale) (g : ℝ → ℝ) :
    (∫ r, g r ∂centralRadialSpectralMeasure scale) =
      ∫ r in Ioi 0, centralRadialVarpi scale r * g r := by
  rw [centralRadialSpectral_integral_change hscale, centralRadius_integral_change]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    dsimp only
    rw [← centralRadialVarpi_pullback_density]
    ring)

/-- Only the implication from the frozen larger test class to the strict
compact test class is used here. The output scalar has the reflected sign. -/
theorem centralAuxiliaryGraph_implies_physicalEquation {scale : ℝ}
    (hscale : 0 < scale)
    (U F : CentralRadialHilbert scale × ℝ)
    (hU : Statements.CentralAuxiliaryGraph scale
      (fun r => sqrt scale * centralAuxiliaryFunction r) U F) :
    CentralAuxiliaryPhysicalEquation hscale F.1 F.2 U.1 (-U.2) := by
  refine ⟨?_, hU.1⟩
  intro ψ hψs hψc hψp
  have hψsupport : Function.support ψ ⊆ Ioi 0 :=
    (subset_tsupport ψ).trans hψp
  have ht := hU.2 ψ hψs hψc hψsupport
  have hF := (centralRadial_distribution_test_integrable hscale 2
    (0 : CentralRadialHilbert scale) F.1 hψs hψc hψp).2
  have hCol := (centralRadial_distribution_test_integrable hscale 2
    (0 : CentralRadialHilbert scale) (centralAuxiliaryColumn hscale)
      hψs hψc hψp).2
  have hSource :
      (∫ r, (F.1 + (-U.2) • centralAuxiliaryColumn hscale) r * ψ r
        ∂centralRadialSpectralMeasure scale) =
      (∫ r, F.1 r * ψ r ∂centralRadialSpectralMeasure scale) +
        (-U.2) * (∫ r, centralAuxiliaryColumn hscale r * ψ r
          ∂centralRadialSpectralMeasure scale) := by
    have hae : (fun r => (F.1 + (-U.2) • centralAuxiliaryColumn hscale) r * ψ r)
        =ᵐ[centralRadialSpectralMeasure scale]
        (fun r => F.1 r * ψ r + (-U.2) * (centralAuxiliaryColumn hscale r * ψ r)) := by
      filter_upwards [Lp.coeFn_add F.1 ((-U.2) • centralAuxiliaryColumn hscale),
        Lp.coeFn_smul (-U.2) (centralAuxiliaryColumn hscale)] with r ha hs
      change (F.1 + (-U.2) • centralAuxiliaryColumn hscale) r =
        F.1 r + ((-U.2) • centralAuxiliaryColumn hscale) r at ha
      change ((-U.2) • centralAuxiliaryColumn hscale) r =
        (-U.2) * centralAuxiliaryColumn hscale r at hs
      rw [ha, hs, add_mul, mul_assoc]
    rw [integral_congr_ae hae, integral_add hF (hCol.const_mul (-U.2)), integral_const_mul]
  have hColPair :
      (∫ r, centralAuxiliaryColumn hscale r * ψ r ∂centralRadialSpectralMeasure scale) =
        ∫ r in Ioi 0, (sqrt scale * centralAuxiliaryFunction r) * ψ r := by
    have hae : (fun r => centralAuxiliaryColumn hscale r * ψ r)
        =ᵐ[centralRadialSpectralMeasure scale]
        (fun r => centralAuxiliaryColumnFunction scale r * ψ r) := by
      filter_upwards [(centralAuxiliaryColumnFunction_memLp hscale).coeFn_toLp] with r hr
      change centralAuxiliaryColumn hscale r = centralAuxiliaryColumnFunction scale r at hr
      rw [hr]
    rw [integral_congr_ae hae, bridge_centralRadialSpectral_integral_density hscale]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    unfold centralAuxiliaryColumnFunction
    calc
      centralRadialVarpi scale r *
          (sqrt scale * centralAuxiliaryFunction r / centralRadialVarpi scale r * ψ r) =
          (centralRadialVarpi scale r *
            (sqrt scale * centralAuxiliaryFunction r / centralRadialVarpi scale r)) * ψ r := by ring
      _ = _ := by
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ (centralRadialVarpi_pos hscale hr).ne']
  have hDensity :
      (∫ r, F.1 r * ψ r ∂centralRadialSpectralMeasure scale) =
        ∫ r in Ioi 0, centralRadialVarpi scale r * F.1 r * ψ r := by
    rw [bridge_centralRadialSpectral_integral_density hscale]
    congr 1
    funext r
    ring
  have hNeg :
      (∫ r in Ioi 0, U.1 r * (-radialJacobi 4 (centralRadialProfile scale) ψ r)) =
        -(∫ r in Ioi 0, U.1 r * radialJacobi 4 (centralRadialProfile scale) ψ r) := by
    simp only [mul_neg, integral_neg]
  rw [show (2 : ℝ) ^ 2 = 4 by norm_num, hSource, hColPair, hDensity, hNeg]
  change (∫ r in Ioi 0, U.1 r * radialJacobi 4 (centralRadialProfile scale) ψ r) -
    U.2 * (∫ r in Ioi 0, (sqrt scale * centralAuxiliaryFunction r) * ψ r) =
      -(∫ r in Ioi 0, centralRadialVarpi scale r * F.1 r * ψ r) at ht
  linarith only [ht]

private theorem bridge_L2_norm_sq {μ : Measure ℝ} (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ∫ r, f r ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext r
  simp only [RCLike.inner_apply, conj_trivial]
  ring

private theorem bridge_toLp_norm_sq {μ : Measure ℝ} {f : ℝ → ℝ}
    (hf : MemLp f 2 μ) : ‖hf.toLp f‖ ^ 2 = ∫ r, f r ^ 2 ∂μ := by
  rw [bridge_L2_norm_sq]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with r hr
  rw [hr]

private theorem bridge_weight_div_square (a b : ℝ) (hb : b ≠ 0) :
    b * (a / b) ^ 2 = a ^ 2 / b := by
  rw [div_pow, pow_two b, ← mul_div_assoc, mul_comm b (a ^ 2),
    mul_div_mul_right _ _ hb]

theorem centralAuxiliaryColumn_square_integrable {scale : ℝ} (hscale : 0 < scale) :
    IntegrableOn (fun r => (sqrt scale * centralAuxiliaryFunction r) ^ 2 /
      centralRadialVarpi scale r) (Ioi 0) := by
  rw [centralRadius_integrable_iff]
  have h := (centralRadialSpectral_integrable_iff hscale _).mp
    (centralAuxiliaryColumnFunction_memLp hscale).integrable_sq
  convert h using 1
  funext x
  rw [← centralRadialVarpi_pullback_density]
  unfold centralAuxiliaryColumnFunction
  rw [mul_assoc, bridge_weight_div_square _ _
    (centralRadialVarpi_pos hscale (centralRadius_pos x)).ne']

theorem centralAuxiliaryColumn_square_integral {scale : ℝ} (hscale : 0 < scale) :
    (∫ r in Ioi 0, (sqrt scale * centralAuxiliaryFunction r) ^ 2 /
      centralRadialVarpi scale r) = ‖centralAuxiliarySourceVector‖ ^ 2 := by
  rw [← centralAuxiliaryColumn_norm hscale]
  change _ = ‖(centralAuxiliaryColumnFunction_memLp hscale).toLp
    (centralAuxiliaryColumnFunction scale)‖ ^ 2
  rw [bridge_toLp_norm_sq, centralRadius_integral_change,
    centralRadialSpectral_integral_change hscale]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    dsimp only
    rw [← centralRadialVarpi_pullback_density]
    unfold centralAuxiliaryColumnFunction
    rw [mul_assoc, bridge_weight_div_square _ _
      (centralRadialVarpi_pos hscale (centralRadius_pos x)).ne'])

theorem centralAuxiliaryKernel_square_integrable {scale : ℝ} (hscale : 0 < scale) :
    IntegrableOn (fun r => centralRadialVarpi scale r *
      (centralKernelHeight r / sqrt scale) ^ 2) (Ioi 0) := by
  rw [centralRadius_integrable_iff]
  have h := (centralRadialSpectral_integrable_iff hscale _).mp
    (centralAuxiliaryKernelFunction_memLp hscale).integrable_sq
  convert h using 1
  funext x
  rw [← centralRadialVarpi_pullback_density]
  unfold centralAuxiliaryKernelFunction
  ring

theorem centralAuxiliaryKernel_square_integral {scale : ℝ} (hscale : 0 < scale) :
    (∫ r in Ioi 0, centralRadialVarpi scale r *
      (centralKernelHeight r / sqrt scale) ^ 2) = ‖centralAuxiliaryKernelVector‖ ^ 2 := by
  rw [← centralAuxiliaryKernel_norm hscale]
  change _ = ‖(centralAuxiliaryKernelFunction_memLp hscale).toLp
    (centralAuxiliaryKernelFunction scale)‖ ^ 2
  rw [bridge_toLp_norm_sq, centralRadius_integral_change,
    centralRadialSpectral_integral_change hscale]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    dsimp only
    rw [← centralRadialVarpi_pullback_density]
    unfold centralAuxiliaryKernelFunction
    ring)

theorem centralAuxiliaryStatement_uniform_estimates :
    ∃ C : ℝ, 0 < C ∧ ∀ (scale : ℝ) (hscale : 0 < scale),
      IntegrableOn (fun r => (sqrt scale * centralAuxiliaryFunction r) ^ 2 /
        centralRadialVarpi scale r) (Ioi 0) ∧
      IntegrableOn (fun r => centralRadialVarpi scale r *
        (centralKernelHeight r / sqrt scale) ^ 2) (Ioi 0) ∧
      (∫ r in Ioi 0, (sqrt scale * centralAuxiliaryFunction r) ^ 2 /
        centralRadialVarpi scale r) ≤ C ∧
      (∫ r in Ioi 0, centralRadialVarpi scale r *
        (centralKernelHeight r / sqrt scale) ^ 2) ≤ C ∧
      ‖centralAuxiliaryStatementInverse hscale‖ ≤ C := by
  let C : ℝ := 1 + ‖centralAuxiliarySourceVector‖ ^ 2 +
    ‖centralAuxiliaryKernelVector‖ ^ 2 + ‖centralAuxiliaryInverse‖
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro scale hscale
  refine ⟨centralAuxiliaryColumn_square_integrable hscale,
    centralAuxiliaryKernel_square_integrable hscale, ?_, ?_, ?_⟩
  · rw [centralAuxiliaryColumn_square_integral hscale]
    dsimp only [C]
    nlinarith [sq_nonneg ‖centralAuxiliaryKernelVector‖, norm_nonneg centralAuxiliaryInverse]
  · rw [centralAuxiliaryKernel_square_integral hscale]
    dsimp only [C]
    nlinarith [sq_nonneg ‖centralAuxiliarySourceVector‖, norm_nonneg centralAuxiliaryInverse]
  · apply (centralAuxiliaryStatementInverse_norm_le hscale).trans
    dsimp only [C]
    nlinarith [sq_nonneg ‖centralAuxiliarySourceVector‖, sq_nonneg ‖centralAuxiliaryKernelVector‖]

theorem centralAuxiliaryColumn_pairing_test {scale : ℝ} (hscale : 0 < scale)
    (ψ : ℝ → ℝ) :
    (∫ r, centralAuxiliaryColumn hscale r * ψ r ∂centralRadialSpectralMeasure scale) =
      ∫ r in Ioi 0, (sqrt scale * centralAuxiliaryFunction r) * ψ r := by
  have hae : (fun r => centralAuxiliaryColumn hscale r * ψ r)
      =ᵐ[centralRadialSpectralMeasure scale]
      (fun r => centralAuxiliaryColumnFunction scale r * ψ r) := by
    filter_upwards [(centralAuxiliaryColumnFunction_memLp hscale).coeFn_toLp] with r hr
    change centralAuxiliaryColumn hscale r = centralAuxiliaryColumnFunction scale r at hr
    rw [hr]
  rw [integral_congr_ae hae, bridge_centralRadialSpectral_integral_density hscale]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  unfold centralAuxiliaryColumnFunction
  calc
    centralRadialVarpi scale r *
        (sqrt scale * centralAuxiliaryFunction r / centralRadialVarpi scale r * ψ r) =
        (centralRadialVarpi scale r *
          (sqrt scale * centralAuxiliaryFunction r / centralRadialVarpi scale r)) * ψ r := by ring
    _ = _ := by
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ (centralRadialVarpi_pos hscale hr).ne']

theorem centralAuxiliaryPhysicalEquation_implies_statement {scale : ℝ}
    (hscale : 0 < scale) (U F : CentralRadialHilbert scale × ℝ)
    (hU : CentralAuxiliaryPhysicalEquation hscale F.1 F.2 U.1 (-U.2)) :
    Statements.CentralAuxiliaryGraph scale
      (fun r => sqrt scale * centralAuxiliaryFunction r) U F := by
  refine ⟨hU.2, ?_⟩
  intro ψ hψs hψc hψp
  have hFlat := centralRadialDistributionEquation_flat_test hscale U.1
    (F.1 + (-U.2) • centralAuxiliaryColumn hscale) hU.1 ψ hψs hψc hψp
  have hF := (centralRadial_flat_test_integrable hscale
    (0 : CentralRadialHilbert scale) F.1 ψ hψs hψc hψp).2
  have hCol := (centralRadial_flat_test_integrable hscale
    (0 : CentralRadialHilbert scale) (centralAuxiliaryColumn hscale)
      ψ hψs hψc hψp).2
  have hSource :
      (∫ r, (F.1 + (-U.2) • centralAuxiliaryColumn hscale) r * ψ r
        ∂centralRadialSpectralMeasure scale) =
      (∫ r, F.1 r * ψ r ∂centralRadialSpectralMeasure scale) +
        (-U.2) * (∫ r, centralAuxiliaryColumn hscale r * ψ r
          ∂centralRadialSpectralMeasure scale) := by
    have hae : (fun r => (F.1 + (-U.2) • centralAuxiliaryColumn hscale) r * ψ r)
        =ᵐ[centralRadialSpectralMeasure scale]
        (fun r => F.1 r * ψ r + (-U.2) * (centralAuxiliaryColumn hscale r * ψ r)) := by
      filter_upwards [Lp.coeFn_add F.1 ((-U.2) • centralAuxiliaryColumn hscale),
        Lp.coeFn_smul (-U.2) (centralAuxiliaryColumn hscale)] with r ha hs
      change (F.1 + (-U.2) • centralAuxiliaryColumn hscale) r =
        F.1 r + ((-U.2) • centralAuxiliaryColumn hscale) r at ha
      change ((-U.2) • centralAuxiliaryColumn hscale) r =
        (-U.2) * centralAuxiliaryColumn hscale r at hs
      rw [ha, hs, add_mul, mul_assoc]
    rw [integral_congr_ae hae, integral_add hF (hCol.const_mul (-U.2)), integral_const_mul]
  have hDensity :
      (∫ r, F.1 r * ψ r ∂centralRadialSpectralMeasure scale) =
        ∫ r in Ioi 0, centralRadialVarpi scale r * F.1 r * ψ r := by
    rw [bridge_centralRadialSpectral_integral_density hscale]
    congr 1
    funext r
    ring
  have hNeg :
      (∫ r in Ioi 0, U.1 r * (-radialJacobi 4 (centralRadialProfile scale) ψ r)) =
        -(∫ r in Ioi 0, U.1 r * radialJacobi 4 (centralRadialProfile scale) ψ r) := by
    simp only [mul_neg, integral_neg]
  have heq := hFlat.2.2
  rw [hSource, centralAuxiliaryColumn_pairing_test hscale ψ, hDensity, hNeg] at heq
  change (∫ r in Ioi 0, U.1 r * radialJacobi 4 (centralRadialProfile scale) ψ r) -
    U.2 * (∫ r in Ioi 0, (sqrt scale * centralAuxiliaryFunction r) * ψ r) =
      -(∫ r in Ioi 0, centralRadialVarpi scale r * F.1 r * ψ r)
  linarith only [heq]

theorem centralCompactAuxiliaryBorder_statement :
    Statements.CentralCompactAuxiliaryBorderStatement := by
  obtain ⟨C, hC, hEstimate⟩ := centralAuxiliaryStatement_uniform_estimates
  refine ⟨centralAuxiliaryFunction, contDiff_centralAuxiliaryFunction,
    centralAuxiliaryFunction_hasCompactSupport,
    (subset_tsupport _).trans centralAuxiliaryFunction_tsupport_positive,
    centralAuxiliaryFunction_pairing_positive, C, hC, ?_⟩
  intro scale hscale
  obtain ⟨hcol, hkernel, hcolC, hkernelC, hop⟩ := hEstimate scale hscale
  refine ⟨hcol, hkernel, hcolC, hkernelC,
    centralAuxiliaryStatementInverse hscale, hop, ?_, ?_⟩
  · intro F
    exact centralAuxiliaryPhysicalEquation_implies_statement hscale _ _
      (centralAuxiliaryStatementInverse_solves hscale F.1 F.2)
  · intro U F hU
    exact centralAuxiliaryStatementInverse_unique hscale F.1 F.2 U.1 U.2
      (centralAuxiliaryGraph_implies_physicalEquation hscale U F hU)

/-- All clauses of the frozen central-model target, without extra hypotheses. -/
theorem centralR03_statement : Statements.R03Statement := by
  refine ⟨centralFullDifferentialSpectrum_statement, centralReducedInverse_statement,
    centralWeightedInverseBounds_statement, centralAllOrderAsymptotics_statement,
    centralCompactAuxiliaryBorder_statement, centralRadialContact_statement,
    centralWeakResolventBound_statement, centralWeakKernel_statement, ?_, ?_, ?_, ?_,
    central_travel_integral_small_divisor⟩
  · intro scale hscale
    exact ⟨contDiffOn_centralRadialProfile scale,
      fun _ hr => centralRadialProfile_pos hscale hr⟩
  · intro x
    exact ⟨deriv_centralRadius_pos x, centralRadius_liouvilleRho x⟩
  · intro c hc r hr hz
    exact centralRadialProfile_simple_turning hc hr hz
  · rw [central_travel_integral_eq]
    rfl

end ContinuousFlexibility.Radial
