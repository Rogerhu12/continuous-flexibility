import ContinuousFlexibility.Analysis.N01RadialFlow
import ContinuousFlexibility.Analysis.SmoothDirectionsMixedScalarLine
import ContinuousFlexibility.Analysis.ScalarFlowParameterVariation
import ContinuousFlexibility.Analysis.TameLocalCalculus

/-!
# Actual parameter derivatives of the N01 ordinary flow

The N01 directional tower gives the ordinary derivative in the external
parameter at every interior radius, together with a bound uniform in
that radius and in the initial angle. A dominated integral argument then
identifies the derivative at the terminal radius from actual derivatives
of the characteristic speed. The speed hypotheses concern concrete
functions and their ordinary finite-dimensional derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

-- Use the canonical product action directly, avoiding a costly search
-- through the abstract models that make up the state space.
local instance (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul
local instance : NormedSpace ℝ ℝ := NormedField.toNormedSpace

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff BigOperators

theorem stateExternalParameterLine (S : PhysicalSpacesData)
    (x : AnnularState S) (q : ℝ) :
    (x, (0 : ℝ)) + q • ((0 : AnnularState S), (1 : ℝ)) = (x, q) := by
  change (x + q • (0 : AnnularState S), (0 : ℝ) + q • (1 : ℝ)) = (x, q)
  simp only [smul_zero, add_zero, smul_eq_mul, mul_one, zero_add]

theorem oneHighVariationWeight_finOne
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (z v : E) :
    oneHighVariationWeight p base high z (fun _ : Fin 1 => v) =
      (1 + p high z) * p base v + p high v := by
  classical
  have hu : (Finset.univ : Finset (Fin 1)) = {0} := by
    ext i
    simp [Subsingleton.elim i (0 : Fin 1)]
  simp only [oneHighVariationWeight, hu, Finset.prod_singleton,
    Finset.sum_singleton, Finset.erase_singleton, Finset.prod_empty, mul_one]

theorem oneHighVariationWeight_externalParameter
    (S : PhysicalSpacesData) (base high : ℕ) (x : AnnularState S) (q : ℝ) :
    oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
      base high (x, q) (fun _ : Fin 1 => ((0 : AnnularState S), (1 : ℝ))) =
        2 + stateGrading S high x + |q| := by
  have hunit (n : ℕ) :
      pairGrading (stateGrading S) realGrading n ((0 : AnnularState S), (1 : ℝ)) = 1 := by
    change stateGrading S n (0 : AnnularState S) + realGrading n (1 : ℝ) = 1
    have hr : realGrading n (1 : ℝ) = 1 := by change |(1 : ℝ)| = 1; norm_num
    exact (congrArg₂ (fun a b : ℝ => a + b) (stateGrading S n).map_zero' hr).trans
      (zero_add 1)
  have he := oneHighVariationWeight_finOne (pairGrading (stateGrading S) realGrading)
    base high (x, q) ((0 : AnnularState S), (1 : ℝ))
  apply he.trans
  have hpair : pairGrading (stateGrading S) realGrading high (x, q) =
      stateGrading S high x + |q| := rfl
  calc
    _ = (1 + (stateGrading S high x + |q|)) * 1 + 1 :=
      congrArg₂ (fun a b : ℝ => a + b)
        (congrArg₂ (fun a b : ℝ => a * b)
          (congrArg (fun t : ℝ => 1 + t) hpair) (hunit base)) (hunit high)
    _ = _ := by ring

/-- The two-dimensional chain rule is normalized before any physical
state data are substituted. -/
theorem hasDerivAt_composed_velocity_coprod
    {F : ℝ → ℝ → ℝ} {Y : ℝ → ℝ} {q a b y : ℝ}
    (hF : HasFDerivAt (fun p : ℝ × ℝ => F p.1 p.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ a).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ b)) (q, Y q))
    (hY : HasDerivAt Y y q) :
    HasDerivAt (fun t : ℝ => F t (Y t)) (a + b * y) q := by
  have hd := hF.comp_hasDerivAt q ((hasDerivAt_id q).prodMk hY)
  simpa only [Function.comp_def, id_eq, ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul, mul_comm y b] using hd

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- A zero-spatial-jet tower differentiates the actual flow, including
the reference value that was subtracted in the tower's definition. -/
theorem ordinaryFlow_q_hasDerivAt_of_tower
    {m : ℕ} {r θ : ℝ}
    (J : SmoothDirections (stateNeighborhood S C base ε)
      (ordinaryFlowFamily S C m 0 0 (r, θ)))
    {x : AnnularState S} {q : ℝ}
    (hxq : (x, q) ∈ stateNeighborhood S C base ε) :
    HasDerivAt (fun t : ℝ => C.minusFlow (x, t) m r θ)
      (J.D 1 (x, q) (fun _ : Fin 1 => ((0 : AnnularState S), (1 : ℝ)))) q := by
  have h := J.hasDerivAt_line (x, (0 : ℝ))
    ((0 : AnnularState S), (1 : ℝ))
    (t := q) (by simpa only [stateExternalParameterLine] using hxq)
  simp only [stateExternalParameterLine, ordinaryFlowFamily, mixedDerivative,
    iteratedDeriv_zero] at h
  simpa only [sub_add_cancel] using
    h.add_const (C.minusFlow (C.referenceState, 0) m r θ)

/-- The actual scalar derivative exists at every interior radial point. -/
theorem N01Properties.minusFlow_q_hasDerivAt
    (hN : N01Properties D T S C base loss ε)
    {x : AnnularState S} {q : ℝ}
    (hxq : (x, q) ∈ stateNeighborhood S C base ε)
    (m : ℕ) {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => C.minusFlow (x, t) m r θ)
      (deriv (fun t : ℝ => C.minusFlow (x, t) m r θ) q) q := by
  have hdata := hN
  rcases hdata with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hflow⟩
  obtain ⟨_, _, hb⟩ := hflow 1 0
  obtain ⟨J, _⟩ := hb m 0 0 (r, θ) (by norm_num) hr
  exact (ordinaryFlow_q_hasDerivAt_of_tower J hxq).differentiableAt.hasDerivAt

theorem ordinaryFlow_q_derivative_bound_of_tower
    {m high : ℕ} {r θ : ℝ}
    (J : SmoothDirections (stateNeighborhood S C base ε)
      (ordinaryFlowFamily S C m 0 0 (r, θ)))
    {x : AnnularState S} {q A : ℝ}
    (hxq : (x, q) ∈ stateNeighborhood S C base ε)
    (hbound : |J.D 1 (x, q)
      (fun _ : Fin 1 => ((0 : AnnularState S), (1 : ℝ)))| ≤
      A * oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
        base high ((x, q) - (C.referenceState, 0))
          (fun _ : Fin 1 => ((0 : AnnularState S), (1 : ℝ)))) :
    |deriv (fun t : ℝ => C.minusFlow (x, t) m r θ) q| ≤
      A * (2 + stateGrading S high (x - C.referenceState) + |q|) := by
  have hd := (ordinaryFlow_q_hasDerivAt_of_tower J hxq).deriv
  have hweight :
      oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
        base high ((x, q) - (C.referenceState, 0))
          (fun _ : Fin 1 => ((0 : AnnularState S), (1 : ℝ))) =
        2 + stateGrading S high (x - C.referenceState) + |q| := by
    change oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
      base high (x - C.referenceState, q - 0)
        (fun _ : Fin 1 => ((0 : AnnularState S), (1 : ℝ))) = _
    simpa only [sub_zero] using
      oneHighVariationWeight_externalParameter S base high (x - C.referenceState) q
  exact (congrArg abs hd).trans_le
    (hbound.trans_eq (congrArg (fun t : ℝ => A * t) hweight))

/-- The true external-parameter derivative inherits the exact N01 weight. -/
theorem N01Properties.minusFlow_q_derivative_weight_bound
    (hN : N01Properties D T S C base loss ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : AnnularState S, ∀ q : ℝ,
      (x, q) ∈ stateNeighborhood S C base ε → ∀ m r θ,
      r ∈ Ioo (C.left m) (C.right m) →
      |deriv (fun t : ℝ => C.minusFlow (x, t) m r θ) q| ≤
        B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          (2 + stateGrading S loss (x - C.referenceState) + |q|) := by
  let hdata := hN.2.2.2.2.2.2.2.2.2.2.2.2 1 0
  let B : ℝ := hdata.choose
  have hB : 0 < B := hdata.choose_spec.1
  have hpoint : ∀ (x : AnnularState S) (q : ℝ),
      (x, q) ∈ stateNeighborhood S C base ε → ∀ (m : ℕ) (r θ : ℝ),
      r ∈ Ioo (C.left m) (C.right m) →
      |deriv (fun t : ℝ => C.minusFlow (x, t) m r θ) q| ≤
        B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          (2 + stateGrading S loss (x - C.referenceState) + |q|) := by
    intro x q hxq m r θ hr
    let htower := hdata.choose_spec.2 m 0 0 (r, θ) (by norm_num) hr
    let J := htower.choose
    apply ordinaryFlow_q_derivative_bound_of_tower (high := loss) J hxq
    simpa only [pow_zero, one_mul, zero_add] using
      htower.choose_spec (x, q) hxq (fun _ : Fin 1 => ((0 : AnnularState S), (1 : ℝ)))
  exact Exists.intro B (And.intro hB hpoint)

/-- For a fixed state and component, the derivative bound is uniform in
the radial point, the external parameter in the N01 neighborhood, and
the initial angle. No endpoint derivative is used. -/
theorem N01Properties.minusFlow_q_derivative_bounded
    (hN : N01Properties D T S C base loss ε)
    {x : AnnularState S} (hx : stateGrading S base (x - C.referenceState) < ε)
    (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q : ℝ, |q| < ε → ∀ r θ,
      r ∈ Ioo (C.left m) (C.right m) →
      |deriv (fun t : ℝ => C.minusFlow (x, t) m r θ) q| ≤ K := by
  obtain ⟨B, _, hb⟩ := hN.minusFlow_q_derivative_weight_bound
  let A := B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
    T.E0 (T.sample (C.cell m)) ^ B
  let K := |A| * (2 + stateGrading S loss (x - C.referenceState) + ε)
  have hp : 0 ≤ stateGrading S loss (x - C.referenceState) :=
    apply_nonneg _ _
  have hε : 0 < ε := hN.2.1
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, fun q hq r θ hr => ?_⟩
  have hfactor : 0 ≤ 2 + stateGrading S loss (x - C.referenceState) + |q| := by
    positivity
  exact (hb x q ⟨hx, hq⟩ m r θ hr).trans
    ((mul_le_mul_of_nonneg_right (le_abs_self A) hfactor).trans
      (mul_le_mul_of_nonneg_left (by linarith only [hq]) (abs_nonneg A)))

/-- The actual endpoint parameter derivative is the integral of the
actual parameter derivative of the speed when its angular derivative
vanishes at the radial base state. The uniform derivative bound supplied
by N01 provides domination for the trajectory term. -/
theorem N01Properties.minusFlow_q_zero_hasDerivAt_of_speed
    (hN : N01Properties D T S C base loss ε)
    {x : AnnularState S}
    (hx : stateGrading S base (x - C.referenceState) < ε)
    (m : ℕ) (θ : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hδε : δ ≤ ε)
    (Vq Vθ : ℝ → ℝ → ℝ → ℝ)
    (hV : ∀ q ∈ Ioo (-δ) δ,
      ContinuousOn
        (fun p : PolarPoint => minusCharacteristicSpeed
          (originalCoefficients D S C (x, q)) p)
        (Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ)))
    (hjet : ∀ q ∈ Ioo (-δ) δ, ∀ r ∈ Ioo (C.left m) (C.right m), ∀ y : ℝ,
      HasFDerivAt
        (fun p : ℝ × ℝ => minusCharacteristicSpeed
          (originalCoefficients D S C (x, p.1)) (r, p.2))
        ((ContinuousLinearMap.toSpanSingleton ℝ (Vq q r y)).coprod
          (ContinuousLinearMap.toSpanSingleton ℝ (Vθ q r y))) (q, y))
    (hbounded : ∃ K : ℝ, 0 ≤ K ∧ ∀ q ∈ Ioo (-δ) δ,
      ∀ r ∈ Ioo (C.left m) (C.right m), ∀ y : ℝ,
        |Vq q r y| ≤ K ∧ |Vθ q r y| ≤ K)
    (hVq0 : ContinuousOn (fun p : PolarPoint => Vq 0 p.1 p.2)
      (Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ)))
    (hVθ0 : ∀ r ∈ Icc (C.left m) (C.right m), ∀ y : ℝ, Vθ 0 r y = 0) :
    HasDerivAt (fun q : ℝ => C.minusFlow (x, q) m (C.right m) θ)
      (∫ r in C.left m..C.right m, Vq 0 r (C.minusFlow (x, 0) m r θ)) 0 := by
  let Y : ℝ → ℝ → ℝ := fun q r => C.minusFlow (x, q) m r θ
  let V : ℝ → ℝ → ℝ → ℝ := fun q r y =>
    minusCharacteristicSpeed (originalCoefficients D S C (x, q)) (r, y)
  let G : ℝ → ℝ → ℝ := fun q r =>
    Vq q r (Y q r) + Vθ q r (Y q r) * deriv (fun t => Y t r) q
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have hab : C.left m < C.right m := (hcontrol.1 m).2.1
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN.2.2.2.2.2.2.1
  have hqmem (q : ℝ) (hq : q ∈ Ioo (-δ) δ) :
      (x, q) ∈ stateNeighborhood S C base ε :=
    ⟨hx, (abs_lt.mpr hq).trans_le hδε⟩
  have hzero : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hY (q : ℝ) (hq : q ∈ Ioo (-δ) δ) :
      ContinuousOn (Y q) (Icc (C.left m) (C.right m)) :=
    (hflow (x, q) (hqmem q hq) m θ).2.1
  have hVi (q : ℝ) (hq : q ∈ Ioo (-δ) δ) :
      IntervalIntegrable (fun r => V q r (Y q r)) volume (C.left m) (C.right m) := by
    have hc : ContinuousOn (fun r => V q r (Y q r)) (Icc (C.left m) (C.right m)) :=
      (hV q hq).comp (continuousOn_id.prodMk (hY q hq))
        (fun r hr => ⟨hr, mem_univ _⟩)
    exact hc.intervalIntegrable_of_Icc hab.le
  have hGzero (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m)) :
      G 0 r = Vq 0 r (Y 0 r) := by
    simp only [G, hVθ0 r hr, zero_mul, add_zero]
  have hG0c : ContinuousOn (G 0) (Icc (C.left m) (C.right m)) := by
    apply ((hVq0.comp (continuousOn_id.prodMk (hY 0 hzero))
      (fun r hr => ⟨hr, mem_univ _⟩))).congr
    intro r hr
    exact hGzero r hr
  have hGi : IntervalIntegrable (G 0) volume (C.left m) (C.right m) :=
    hG0c.intervalIntegrable_of_Icc hab.le
  obtain ⟨KY, hKY, hYbound⟩ := hN.minusFlow_q_derivative_bounded hx m
  obtain ⟨KV, hKV, hVbound⟩ := hbounded
  have hGbound : ∀ᵐ r ∂volume, r ∈ uIoc (C.left m) (C.right m) →
      ∀ q ∈ Ioo (-δ) δ, ‖G q r‖ ≤ KV * (1 + KY) := by
    apply ae_uIoc_imp_of_forall_Ioo hab.le
    intro r hr q hq
    obtain ⟨hqp, hθp⟩ := hVbound q hq r hr (Y q r)
    have hy := hYbound q (hqmem q hq).2 r θ hr
    rw [Real.norm_eq_abs]
    calc
      _ ≤ |Vq q r (Y q r)| +
          |Vθ q r (Y q r) * deriv (fun t => Y t r) q| := abs_add_le _ _
      _ = |Vq q r (Y q r)| +
          |Vθ q r (Y q r)| * |deriv (fun t => Y t r) q| := by rw [abs_mul]
      _ ≤ KV + KV * KY :=
        add_le_add hqp (mul_le_mul hθp hy (abs_nonneg _) hKV)
      _ = _ := by ring
  have hGderiv : ∀ᵐ r ∂volume, r ∈ uIoc (C.left m) (C.right m) →
      ∀ q ∈ Ioo (-δ) δ, HasDerivAt (fun t => V t r (Y t r)) (G q r) q := by
    apply ae_uIoc_imp_of_forall_Ioo hab.le
    intro r hr q hq
    have hy := hN.minusFlow_q_hasDerivAt (hqmem q hq) m hr θ
    exact hasDerivAt_composed_velocity_coprod (F := fun t y => V t r y)
      (Y := fun t => Y t r) (hjet q hq r hr (Y q r)) hy
  have hd := hasDerivAt_scalarFlow_endpoint_of_dominated hab.le
    (Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ) hY
    (fun q hq => (hflow (x, q) (hqmem q hq) m θ).1)
    (fun q hq r hr => (hflow (x, q) (hqmem q hq) m θ).2.2.1 r hr)
    hVi hGi.def'.aestronglyMeasurable hGbound
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => KV * (1 + KY))
      volume (C.left m) (C.right m)) hGderiv
  apply hd.congr_deriv
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le hab.le] at hr
  exact hGzero r hr

end ContinuousFlexibility.Statements
