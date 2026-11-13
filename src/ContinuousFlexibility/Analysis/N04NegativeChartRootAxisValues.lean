import ContinuousFlexibility.Analysis.N04NegativeChartRootIdentification
import ContinuousFlexibility.Analysis.ReturnChartUniformBounds

/-!
# Actual root-axis lower bounds at the retained sample

The normalized denominator bounds and the actual optical square control
the speed reciprocal. The retained forward angular slopes control the
actual odd return label. Their exact inverse-flow formula gives the
axis coefficient, with an explicit polynomial cost for the chosen scale.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

private theorem normalizedSpeed_lower_of_n01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    (1 / 4 : ℝ) ≤ normalizedSpeedFactor D S C 1 z p := by
  have hB : N01PartB D S C base ε :=
    ⟨hN.2.2.2.2.2.2.1, hN.2.2.2.2.2.2.2.1,
      hN.2.2.2.2.2.2.2.2.1, hN.2.2.2.2.2.2.2.2.2.1,
      hN.2.2.2.2.2.2.2.2.2.2.1⟩
  have hb := n01PartB_denominator_bounds hS hN.2.2.1 hB hz hp
  let D₀ := polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p
  let Q := heightQ (profileEnergy (stateProfile D S C z.1) p)
    (heightRadial (stateHeight D S C z) p)
    (angularPartial (heightAngular (stateHeight D S C z)) p) / stateProfile D S C z.1 p.1
  have hD : (1 / 2 : ℝ) ≤ D₀ := hb.2.2.2.2.1
  have hQlo : (7 / 8 : ℝ) ≤ Q := hb.2.2.1
  have hQhi : Q ≤ (9 / 8 : ℝ) := hb.2.2.2.1
  have hQ : 0 < Q := lt_of_lt_of_le (by norm_num) hQlo
  have hDs : (1 / 2 : ℝ) ≤ Real.sqrt D₀ := by
    have hD0 : 0 ≤ D₀ := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hD
    nlinarith only [Real.sqrt_nonneg D₀, Real.sq_sqrt hD0, hD]
  change (1 / 4 : ℝ) ≤ Real.sqrt D₀ / Q
  apply (le_div_iff₀ hQ).2
  nlinarith only [hQhi, hDs]

private theorem factoredSqrt_inverse_bound {q f B E A : ℝ}
    (hq : 0 < q) (hf : (1 / 4 : ℝ) ≤ f)
    (hB : 0 < B) (hE : 1 ≤ E) (hA : 0 ≤ A) (hi : q⁻¹ ≤ B * E ^ A) :
    0 < Real.sqrt q * f ∧ (Real.sqrt q * f)⁻¹ ≤ 4 * (1 + B) * E ^ A := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hf0 : 0 < f := lt_of_lt_of_le (by norm_num) hf
  have hlo : Real.sqrt q / 4 ≤ Real.sqrt q * f := by
    simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hf hs.le
  have hsi : (Real.sqrt q)⁻¹ ≤ 1 + q⁻¹ := by
    rw [← Real.sqrt_inv]
    have hsq := Real.sq_sqrt (inv_nonneg.mpr hq.le)
    nlinarith only [hsq, sq_nonneg (Real.sqrt q⁻¹ - 1 / 2)]
  have hsum : 1 + q⁻¹ ≤ (1 + B) * E ^ A := by
    have hh := add_le_add (Real.one_le_rpow hE hA) hi
    nlinarith only [hh]
  refine ⟨mul_pos hs hf0, ?_⟩
  calc
    _ ≤ (Real.sqrt q / 4)⁻¹ := inv_anti₀ (div_pos hs (by norm_num)) hlo
    _ = 4 * (Real.sqrt q)⁻¹ := by rw [inv_div, div_eq_mul_inv]
    _ ≤ 4 * ((1 + B) * E ^ A) :=
      mul_le_mul_of_nonneg_left (hsi.trans hsum) (by norm_num)
    _ = _ := by ring

private theorem scaledOdd_inverse_bound {δ c a B : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hc : 0 < c)
    (ha : (1 / 4 : ℝ) ≤ a) (hi : c⁻¹ ≤ B) :
    0 < ((2 : ℝ) / 3) * δ * Real.sqrt δ * c * a ∧
      (((2 : ℝ) / 3) * δ * Real.sqrt δ * c * a)⁻¹ ≤
        6 * (δ⁻¹) ^ 2 * B := by
  have hs := Real.sqrt_pos.mpr hδ
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hsone : Real.sqrt δ ≤ 1 := by
    nlinarith only [hs.le, Real.sq_sqrt hδ.le, hδone]
  have hδs : δ ≤ Real.sqrt δ := by
    have hh := mul_le_mul_of_nonneg_left hsone hs.le
    simpa only [Real.mul_self_sqrt hδ.le, mul_one] using hh
  have hlow : δ ^ 2 * c / 6 ≤ ((2 : ℝ) / 3) * δ * Real.sqrt δ * c * a := by
    have h₁ := mul_le_mul_of_nonneg_left ha
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) hδ.le) hs.le) hc.le)
    have h₂ := mul_le_mul_of_nonneg_left hδs (mul_nonneg hδ.le hc.le)
    nlinarith only [h₁, h₂]
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ (δ ^ 2 * c / 6)⁻¹ := inv_anti₀ (by positivity) hlow
    _ = 6 * (δ⁻¹) ^ 2 * c⁻¹ := by
      simp only [inv_div, mul_inv_rev, inv_pow, div_eq_mul_inv]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hi (by positivity)

namespace NegativeChartRootFlowData

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {d c : P × PolarPoint → ℝ} {δ : ℝ} (A : NegativeChartRootFlowData d c δ)

theorem inverse_eq_invFun (y : P) (v : ℝ × ℝ) (θ : ℝ) :
    A.inverse y v 1 θ = Function.invFun (A.flow y v 1) θ := by
  have hinj : Function.Injective (A.flow y v 1) :=
    Function.LeftInverse.injective (fun η => (A.endpoint_inverse y v η).2)
  have hh := Function.leftInverse_invFun hinj (A.inverse y v 1 θ)
  rw [(A.endpoint_inverse y v θ).1] at hh
  exact hh.symm

end NegativeChartRootFlowData

namespace N04RealizationStart

variable (W : N04RealizationStart)

theorem negativeRootLabel_deriv_bounds
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C W.base W.ε)
    (hs : stateSector W.S z.1) (m : ℕ) (side : Bool) (θ : ℝ) :
    deriv (n01RootLabel W.S W.C z m side) θ ∈ Icc (1 / 4 : ℝ) 4 := by
  have hflow (i : ℕ) (η : ℝ) := W.cutoff.flow_slope z hz hs i (W.C.right i)
    ⟨(W.through03.1.1.2.2.2.1.1 i).2.1.le, le_rfl⟩ η
  cases side
  · have hh := W.through03.1.1.2.2.2.2.2.2.2.1 z hz hs m θ
    exact ⟨(by norm_num : (1 / 4 : ℝ) ≤ 1 / 2).trans hh.1,
      hh.2.1.trans (by norm_num : (2 : ℝ) ≤ 4)⟩
  · have hh := W.through03.1.1.rightChartCandidate_deriv_bounds hz hs hflow m θ
    exact ⟨(by norm_num : (1 / 4 : ℝ) ≤ 1 / 3).trans hh.1, hh.2⟩

theorem negativeRootInverseCoordinate_eq_scaled
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {d c : P × PolarPoint → ℝ} {δ : ℝ} (A : NegativeChartRootFlowData d c δ)
    (z : AnnularState W.S × ℝ) (m : ℕ) (side : Bool) (y : P) :
    W.negativeRootInverseCoordinate A z m side y =
      rootScaledInverseCoordinate (A.flow y) (n01RootLabel W.S W.C z m side) (Real.sqrt δ) := by
  funext q
  change n01RootLabel W.S W.C z m side
    (A.inverse y (q.1, Real.sqrt δ * q.2.1) 1 q.2.2) =
    n01RootLabel W.S W.C z m side
      (Function.invFun (A.flow y (q.1, Real.sqrt δ * q.2.1) 1) q.2.2)
  rw [A.inverse_eq_invFun]

theorem negativeRootInverseCoordinate_regular
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {d c : P × PolarPoint → ℝ} {δ : ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdp : ∀ y r, Function.Periodic (fun θ => d (y, (r, θ))) Real.pi)
    (hcp : ∀ y r, Function.Periodic (fun θ => c (y, (r, θ))) Real.pi)
    (A : NegativeChartRootFlowData d c δ) (y : P)
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C W.base W.ε)
    (hs : stateSector W.S z.1) (m : ℕ) (side : Bool) :
    ContDiff ℝ ∞ (W.negativeRootInverseCoordinate A z m side y) ∧
      ∀ x ζ θ, W.negativeRootInverseCoordinate A z m side y (x, ζ, θ + Real.pi) =
        W.negativeRootInverseCoordinate A z m side y (x, ζ, θ) + Real.pi := by
  rw [W.negativeRootInverseCoordinate_eq_scaled]
  exact rootScaledInverseCoordinate_regular
    (hd.comp (contDiff_const.prodMk contDiff_id))
    (hc.comp (contDiff_const.prodMk contDiff_id)) (hdp y) (hcp y) (A.flow_equations y)
    (n01RootLabel_contDiff W.hS W.hT W.through03.1.1 hz hs m side)
    (n01RootLabel_period_add W.through03.1.1 hz hs m side) (Real.sqrt δ)

namespace NegativeOpticalFactors

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  (F : NegativeOpticalFactors W e)

theorem fullHalfSpeed_inverse_material :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ z ∈ stateNeighborhood W.S W.C W.base (W.ε / 2), ∀ m side (p : PolarPoint),
        p.1 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) →
        0 < F.fullHalfSpeed z m side p ∧ (F.fullHalfSpeed z m side p)⁻¹ ≤
          B * W.T.E0 (W.negativeHalfSample e m side) ^ A := by
  have hSquare := F.stateSquare_inverse_material
  let B := hSquare.choose
  let A := hSquare.choose_spec.choose
  have hB := hSquare.choose_spec.choose_spec.1
  have hA := hSquare.choose_spec.choose_spec.2.1
  have hb := hSquare.choose_spec.choose_spec.2.2
  refine ⟨4 * (1 + B), A, by positivity, hA, fun z hz m side p hp => ?_⟩
  have hz' : z ∈ stateNeighborhood W.S W.C W.base W.ε :=
    stateNeighborhood_mono W.S W.C le_rfl (by linarith only [W.ε_pos]) hz
  exact factoredSqrt_inverse_bound (F.stateSquare_pos hz m side hp)
    (normalizedSpeed_lower_of_n01 W.hS W.through03.1.1 hz'
      (W.negativeInwardPoint_mem_annular m side (p := p) hp)) hB (W.floor _) hA.le
    (hb z hz m side p.1 hp)

/-- The constants precede the finite plot, its dimension, and the
actual state. No lower bound for the target odd coefficient is supplied. -/
theorem fullHalfFields_root_axis_inverse_material :
    ∃ B p : ℝ, 0 < B ∧ 0 < p ∧ ∀ n : ℕ,
      ∀ d c : (Fin n → ℝ) × PolarPoint → ℝ,
      ContDiff ℝ ∞ d → ContDiff ℝ ∞ c →
      (∀ y r, Function.Periodic (fun θ => d (y, (r, θ))) Real.pi) →
      (∀ y r, Function.Periodic (fun θ => c (y, (r, θ))) Real.pi) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ A : NegativeChartRootFlowData d c δ,
      ∀ (y : Fin n → ℝ) (z : AnnularState W.S × ℝ),
      z ∈ stateNeighborhood W.S W.C W.base (W.ε / 2) → stateSector W.S z.1 →
      ∀ m side, (∀ θ, c (y, (0, θ)) = F.fullHalfSpeed z m side (0, θ)) → ∀ θ,
        let χ := rootOddCoefficient (W.negativeRootInverseCoordinate A z m side y) (0, θ)
        0 < χ ∧ χ⁻¹ ≤ B * (δ⁻¹) ^ 2 * W.T.E0 (W.negativeHalfSample e m side) ^ p := by
  have hSpeed := F.fullHalfSpeed_inverse_material
  let B := hSpeed.choose
  let p := hSpeed.choose_spec.choose
  have hB := hSpeed.choose_spec.choose_spec.1
  have hp := hSpeed.choose_spec.choose_spec.2.1
  have hb := hSpeed.choose_spec.choose_spec.2.2
  refine ⟨6 * B, p, by positivity, hp, ?_⟩
  intro n d c hd hc hdp hcp δ hδ hδone A y z hz hs m side hrep θ
  have hz' : z ∈ stateNeighborhood W.S W.C W.base W.ε :=
    stateNeighborhood_mono W.S W.C le_rfl (by linarith only [W.ε_pos]) hz
  have hzero : (0 : ℝ) ∈ Icc 0 (W.negativeOpticalWidth m side) :=
    ⟨le_rfl, (W.negativeOpticalWidth_pos m side).le⟩
  have hcval := hb z hz m side (0, θ) hzero
  have hlabel := W.negativeRootLabel_deriv_bounds hz' hs m side θ
  have he := (rootScaledInverseCoordinate_zero_and_odd
    (hd.comp (contDiff_const.prodMk contDiff_id))
    (hc.comp (contDiff_const.prodMk contDiff_id)) (hdp y) (hcp y) (A.flow_equations y)
    (n01RootLabel_contDiff W.hS W.hT W.through03.1.1 hz' hs m side) (Real.sqrt δ) θ).2
  rw [← W.negativeRootInverseCoordinate_eq_scaled A z m side y, hrep θ] at he
  dsimp only
  rw [he]
  have hh := scaledOdd_inverse_bound hδ hδone hcval.1 hlabel.1 hcval.2
  exact ⟨hh.1, hh.2.trans_eq (by ring)⟩

end NegativeOpticalFactors
end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.fullHalfFields_root_axis_inverse_material'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.fullHalfFields_root_axis_inverse_material
