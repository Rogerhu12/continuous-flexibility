import ContinuousFlexibility.Analysis.N08FlowParameterIntegral
import ContinuousFlexibility.Analysis.N08RadialFlow

/-!
# Uniform parameter control of the given ordinary flows

N01's genuine first jets give a parameter Lipschitz constant independent
of the interior radius. This supplies domination for the ordinary integral
identity, including integration up to the continuous left endpoint.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology Interval BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- Any of the supplied towers identifies the actual parameter derivative
of the unnormalized flow, since its reference subtraction is constant. -/
theorem n08_minusFlow_parameter_hasDerivAt
    {m : ℕ} {r θ : ℝ}
    (J : SmoothDirections (stateNeighborhood S C base ε)
      (ordinaryFlowFamily S C m 0 0 (r, θ)))
    {x : AnnularState S} {q : ℝ} (hz : (x, q) ∈ stateNeighborhood S C base ε) :
    HasDerivAt (fun t : ℝ => C.minusFlow (x, t) m r θ)
      (J.D 1 (x, q) (Fin.cons ((0 : AnnularState S), (1 : ℝ)) Fin.elim0)) q := by
  have hd := n08_hasDerivAt_parameterSlice J hz
  simpa only [ordinaryFlowFamily, mixedDerivative, iteratedDeriv_zero, sub_add_cancel] using
    hd.add_const (C.minusFlow (C.referenceState, 0) m r θ)

private theorem n08_oneHigh_parameter
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (x x0 : E) (q : ℝ) :
    oneHighVariationWeight (pairGrading p realGrading) base high
      ((x, q) - (x0, 0)) (Fin.cons ((0 : E), (1 : ℝ)) Fin.elim0) =
      2 + p high (x - x0) + |q| := by
  simp [oneHighVariationWeight, pairGrading, realGrading] <;> ring

/-- The parameter interval stays strictly inside N01's original domain.
The same finite constant works at every interior radius of this cell. -/
theorem n08_minusFlow_parameter_lipschitz
    (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (m : ℕ) (θ : ℝ) :
    ∃ K : ℝ≥0, ∀ r ∈ Ioo (C.left m) (C.right m),
      LipschitzOnWith K (fun q : ℝ => C.minusFlow (x, q) m r θ)
        (Icc (-(ε / 2)) (ε / 2)) := by
  have hdata := hN
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hflow⟩ := hdata
  obtain ⟨B, _, hBj⟩ := hflow 1 0
  let A : ℝ := B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
    T.E0 (T.sample (C.cell m)) ^ B
  let M : ℝ := |A| * (2 + stateGrading S loss (x - C.referenceState) + ε)
  have hgrade : 0 ≤ stateGrading S loss (x - C.referenceState) :=
    (stateGrading S loss).nonneg _
  have hM : 0 ≤ M := mul_nonneg (abs_nonneg A) (by linarith [hN.2.1])
  refine ⟨⟨M, hM⟩, ?_⟩
  intro r hr
  obtain ⟨J, hJ⟩ := hBj m 0 0 (r, θ) (by simp) hr
  have hmem (q : ℝ) (hq : q ∈ Icc (-(ε / 2)) (ε / 2)) :
      (x, q) ∈ stateNeighborhood S C base ε := by
    refine ⟨hx.1, ?_⟩
    exact (abs_le.mpr hq).trans_lt (by linarith [hN.2.1])
  refine (convex_Icc (-(ε / 2)) (ε / 2)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun q => J.D 1 (x, q)
      (Fin.cons ((0 : AnnularState S), (1 : ℝ)) Fin.elim0))
    (fun q hq => (n08_minusFlow_parameter_hasDerivAt J (hmem q hq)).hasDerivWithinAt) ?_
  intro q hq
  have hqabs : |q| ≤ ε / 2 := abs_le.mpr hq
  have hbound : |J.D 1 (x, q)
      (Fin.cons ((0 : AnnularState S), (1 : ℝ)) Fin.elim0)| ≤
      A * (2 + stateGrading S loss (x - C.referenceState) + |q|) := by
    simpa only [pow_zero, one_mul, Nat.zero_add, n08_oneHigh_parameter] using
      hJ (x, q) (hmem q hq) (Fin.cons ((0 : AnnularState S), (1 : ℝ)) Fin.elim0)
  have hreal : |J.D 1 (x, q)
      (Fin.cons ((0 : AnnularState S), (1 : ℝ)) Fin.elim0)| ≤ M := by
    calc
      _ ≤ A * (2 + stateGrading S loss (x - C.referenceState) + |q|) := hbound
      _ ≤ |A| * (2 + stateGrading S loss (x - C.referenceState) + |q|) :=
        mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
      _ ≤ M := mul_le_mul_of_nonneg_left (by linarith [hN.2.1]) (abs_nonneg A)
  simpa only [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs] using hreal

end ContinuousFlexibility.Statements
