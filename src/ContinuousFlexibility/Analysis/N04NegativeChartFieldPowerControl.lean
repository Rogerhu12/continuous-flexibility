import ContinuousFlexibility.Analysis.N04NegativeChartInwardPower

/-!
# Actual root coefficients with one common interpolation base

The original normalized factors and the genuine divided optical root
are combined in their existing power algebra. A single neighborhood
and loss precede every spatial and state order. Every positive state
jet retains one height factor at the selected negative-half sample.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

/-- Multiplication by a fixed unit sign changes no jet norm. -/
private def endpointPowerControl_unitSign
    {X I : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ}
    {U : Set X} {Ω : I → Set PolarPoint} {δ H E : I → PolarPoint → ℝ}
    {f : I → X → PolarPoint → ℝ}
    (F : EndpointPowerControl p center base loss U Ω δ H E f)
    (σ : I → ℝ) (hσ : ∀ i, |σ i| = 1) :
    EndpointPowerControl p center base loss U Ω δ H E
      (fun i x q => σ i * f i x q) := by
  let R (i : I) : MixedJetRegularity U (Ω i) (fun x q => σ i * f i x q) := {
    spatial := fun x hx => contDiffOn_const.mul ((F.regular i).spatial x hx)
    parameter := fun a b q hq =>
      (smoothDirections_postcompCLM ((F.regular i).parameter a b q hq)
        (σ i • ContinuousLinearMap.id ℝ ℝ)).congr (fun x hx => by
          simpa only [Function.comp_apply, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul] using
            (mixedDerivative_const_mul (σ i) (f i x) a b q).symm) }
  refine ⟨R, ?_⟩
  intro K s
  obtain ⟨C, A, hC, hA, hb⟩ := F.bounds K s
  refine ⟨C, A, hC, hA, ?_⟩
  intro i k hk a b hab q hq J x hx hlow v hv R₀ hR₀ hhigh hvhigh
  let J0 := (F.regular i).parameter a b q hq
  have he : J.D k x v = σ i * J0.D k x v := by
    apply (congrArg (fun A : X [×k]→L[ℝ] ℝ => A v)
      (J.unique ((R i).parameter a b q hq) k x hx)).trans
    change (smoothDirections_postcompCLM J0 (σ i • ContinuousLinearMap.id ℝ ℝ)).D k x v = _
    simp only [smoothDirections_postcompCLM_D_apply, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
  have hnorm : ‖J.D k x v‖ = ‖J0.D k x v‖ := by
    rw [he, norm_mul, Real.norm_eq_abs, hσ i, one_mul]
  rw [hnorm]
  exact hb i k hk a b hab q hq J0 x hx hlow v hv R₀ hR₀ hhigh hvhigh

namespace N04RealizationStart

abbrev negativeHalfStateRadius (W : N04RealizationStart) : ℝ := min (W.ε / 2) (1 / 2 : ℝ)

namespace NegativeOpticalFactors

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  (F : NegativeOpticalFactors W e)

/-- Controls of the two literal fields on the same full inward half. -/
def FullHalfFieldPowerControl (base loss : ℕ) : Type :=
  EndpointPowerControl (pairGrading (stateGrading W.S) realGrading)
    (W.C.referenceState, 0) base loss
    (stateNeighborhood W.S W.C base W.negativeHalfStateRadius)
    (fun i : ℕ × Bool => Ioo (0 : ℝ) (W.negativeOpticalWidth i.1 i.2) ×ˢ univ)
    (fun _ _ => 1)
    (fun i _ => W.T.H (W.negativeHalfSample e i.1 i.2) ^ (3 / 4 : ℝ))
    (fun i _ => W.T.E0 (W.negativeHalfSample e i.1 i.2))
    (fun i z q => F.fullHalfDrift z i.1 i.2 q) ×
  EndpointPowerControl (pairGrading (stateGrading W.S) realGrading)
    (W.C.referenceState, 0) base loss
    (stateNeighborhood W.S W.C base W.negativeHalfStateRadius)
    (fun i : ℕ × Bool => Ioo (0 : ℝ) (W.negativeOpticalWidth i.1 i.2) ×ˢ univ)
    (fun _ _ => 1)
    (fun i _ => W.T.H (W.negativeHalfSample e i.1 i.2) ^ (3 / 4 : ℝ))
    (fun i _ => W.T.E0 (W.negativeHalfSample e i.1 i.2))
    (fun i z q => F.fullHalfSpeed z i.1 i.2 q)

private theorem fullHalfFields_of_interpolation
    (base loss : ℕ) (hb : W.base ≤ base)
    (hI : ∀ s : ℕ, ∃ B : ℝ, 1 ≤ B ∧
      ∀ n : ℕ, n ≤ s → ∀ x : AnnularState W.S × ℝ,
      pairGrading (stateGrading W.S) realGrading base x ≤ 1 →
      ∀ R : ℝ, 1 ≤ R → pairGrading (stateGrading W.S) realGrading (s + loss) x ≤ R →
        pairGrading (stateGrading W.S) realGrading (n + 4) x ≤
          B * R ^ ((n : ℝ) / ((s : ℝ) + 1))) :
    Nonempty (F.FullHalfFieldPowerControl base loss) := by
  have h01 := W.through03.1.1
  have hA : N01PartA W.D W.T W.S W.C :=
    ⟨h01.1, h01.2.2.1, h01.2.2.2.1, h01.2.2.2.2.1, h01.2.2.2.2.2.1⟩
  have hB : N01PartB W.D W.S W.C W.base W.ε :=
    ⟨h01.2.2.2.2.2.2.1, h01.2.2.2.2.2.2.2.1,
      h01.2.2.2.2.2.2.2.2.1, h01.2.2.2.2.2.2.2.2.2.1,
      h01.2.2.2.2.2.2.2.2.2.2.1⟩
  have hr : 0 < W.negativeHalfStateRadius := lt_min (by linarith [W.ε_pos]) (by norm_num)
  have hrε : W.negativeHalfStateRadius ≤ W.ε :=
    (min_le_left _ _).trans (by linarith [W.ε_pos])
  have hr1 : W.negativeHalfStateRadius ≤ 1 :=
    (min_le_right _ _).trans (by norm_num)
  let U := stateNeighborhood W.S W.C base W.negativeHalfStateRadius
  have hU : IsOpen U := isOpen_stateNeighborhood W.S W.C base W.negativeHalfStateRadius
  have hsub : U ⊆ stateNeighborhood W.S W.C W.base (W.ε / 2) :=
    stateNeighborhood_mono W.S W.C hb (min_le_left _ _)
  have hB' : N01PartB W.D W.S W.C base W.negativeHalfStateRadius :=
    n01PartB_mono hB hb hrε
  have hNF (i : Fin 2) := n04NegativeGeometry_normalizedFactor_regular_bounds
    (D := W.D) (T := W.T) (S := W.S) (C := W.C) W.hS W.hT hA hr hr1 hB'
    (fun r _ => W.floor r) W.primitive.1 W.primitive.2.1 hI i
  obtain ⟨R₀, h₀⟩ := hNF 0
  obtain ⟨R₁, h₁⟩ := hNF 1
  let A₀ := W.negativeHalf_inward_powerControl e R₀ h₀
  let A₁ := W.negativeHalf_inward_powerControl e R₁ h₁
  let Q := F.opticalSpeed_half_powerControl hU hsub base loss
  let Ω : ℕ × Bool → Set PolarPoint := fun i =>
    Ioo 0 (W.negativeOpticalWidth i.1 i.2) ×ˢ univ
  have hΩ (i : ℕ × Bool) : IsOpen (Ω i) := isOpen_Ioo.prod isOpen_univ
  obtain ⟨M, hM, hMb⟩ := materialHeight_E0_weight_bounded W.hT
    (γ := (3 / 4 : ℝ)) (by norm_num) 0
  have hH (i : ℕ × Bool) (q : PolarPoint) (_hq : q ∈ Ω i) :
      0 ≤ W.T.H (W.negativeHalfSample e i.1 i.2) ^ (3 / 4 : ℝ) ∧
        W.T.H (W.negativeHalfSample e i.1 i.2) ^ (3 / 4 : ℝ) ≤ M := by
    have hs := materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1
      ((W.A e).cell (e.symm (.inl i)))
    refine ⟨Real.rpow_nonneg (W.hT.2.1 _ hs).2.1.le _, ?_⟩
    simpa only [Real.rpow_zero, mul_one] using hMb _ hs
  let DC := endpointPowerControl_unitSign A₀
    (fun i => -n01ComponentRootOrientation i.2) (fun i => by
      cases i.2 <;> norm_num [n01ComponentRootOrientation])
  let RC (i : ℕ × Bool) := (Q.regular i).mul (A₁.regular i) hU (hΩ i)
  have hC := Q.bounds.mul A₁.bounds Q.regular A₁.regular hΩ
    (fun _ _ _ => (by norm_num : (0 : ℝ) ≤ 1)) (fun i _ _ => W.floor _) hH
  exact ⟨⟨DC, ⟨RC, hC⟩⟩⟩

/-- The actual retained geometry supplies the complete field controls.
The base and radius are chosen before every state and spatial order. -/
theorem fullHalfFields_powerControl :
    ∃ base loss : ℕ, W.base ≤ base ∧ Nonempty (F.FullHalfFieldPowerControl base loss) :=
  exists_base_ge_of_spatialPower_continuation
    (pairGrading (stateGrading W.S) realGrading) (jointStateGrading_monotone W.S)
    (jointStateGrading_hasInterpolation W.hS) W.base 4
    (fun base loss => Nonempty (F.FullHalfFieldPowerControl base loss))
    (F.fullHalfFields_of_interpolation)

end NegativeOpticalFactors
end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.fullHalfFields_powerControl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.fullHalfFields_powerControl
