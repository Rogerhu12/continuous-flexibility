import ContinuousFlexibility.Analysis.N01FlowHeightVariation

/-!
# Parameter variation at every partial-return radius

The actual parameter-variation formula is proved on each truncated
closed radial interval. This keeps the evaluation radius inside the
domain of the N01 quantitative towers and permits a subsequent
continuous limit to the terminal radius.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.minusFlow_q_zero_partial_hasDerivAt_of_speed
    (hN : N01Properties D T S C base loss ε)
    {x : AnnularState S}
    (hx : stateGrading S base (x - C.referenceState) < ε)
    (m : ℕ) (θ : ℝ) {b : ℝ} (hb : b ∈ Icc (C.left m) (C.right m))
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
    HasDerivAt (fun q : ℝ => C.minusFlow (x, q) m b θ)
      (∫ r in C.left m..b, Vq 0 r (C.minusFlow (x, 0) m r θ)) 0 := by
  let Y : ℝ → ℝ → ℝ := fun q r => C.minusFlow (x, q) m r θ
  let V : ℝ → ℝ → ℝ → ℝ := fun q r y =>
    minusCharacteristicSpeed (originalCoefficients D S C (x, q)) (r, y)
  let G : ℝ → ℝ → ℝ := fun q r =>
    Vq q r (Y q r) + Vθ q r (Y q r) * deriv (fun t => Y t r) q
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have hab : C.left m ≤ b := hb.1
  have hrad (r : ℝ) (hr : r ∈ Icc (C.left m) b) :
      r ∈ Icc (C.left m) (C.right m) := ⟨hr.1, hr.2.trans hb.2⟩
  have hradi (r : ℝ) (hr : r ∈ Ioo (C.left m) b) :
      r ∈ Ioo (C.left m) (C.right m) := ⟨hr.1, hr.2.trans_le hb.2⟩
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN.2.2.2.2.2.2.1
  have hqmem (q : ℝ) (hq : q ∈ Ioo (-δ) δ) :
      (x, q) ∈ stateNeighborhood S C base ε :=
    ⟨hx, (abs_lt.mpr hq).trans_le hδε⟩
  have hzero : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hY (q : ℝ) (hq : q ∈ Ioo (-δ) δ) :
      ContinuousOn (Y q) (Icc (C.left m) b) :=
    (hflow (x, q) (hqmem q hq) m θ).2.1.mono (Icc_subset_Icc le_rfl hb.2)
  have hVi (q : ℝ) (hq : q ∈ Ioo (-δ) δ) :
      IntervalIntegrable (fun r => V q r (Y q r)) volume (C.left m) b := by
    have hc : ContinuousOn (fun r => V q r (Y q r)) (Icc (C.left m) b) :=
      (hV q hq).comp (continuousOn_id.prodMk (hY q hq))
        (fun r hr => ⟨hrad r hr, mem_univ _⟩)
    exact hc.intervalIntegrable_of_Icc hab
  have hGzero (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m)) :
      G 0 r = Vq 0 r (Y 0 r) := by
    simp only [G, hVθ0 r hr, zero_mul, add_zero]
  have hG0c : ContinuousOn (G 0) (Icc (C.left m) b) := by
    apply ((hVq0.comp (continuousOn_id.prodMk (hY 0 hzero))
      (fun r hr => ⟨hrad r hr, mem_univ _⟩))).congr
    intro r hr
    exact hGzero r (hrad r hr)
  have hGi : IntervalIntegrable (G 0) volume (C.left m) b :=
    hG0c.intervalIntegrable_of_Icc hab
  obtain ⟨KY, hKY, hYbound⟩ := hN.minusFlow_q_derivative_bounded hx m
  obtain ⟨KV, hKV, hVbound⟩ := hbounded
  have hGbound : ∀ᵐ r ∂volume, r ∈ uIoc (C.left m) b →
      ∀ q ∈ Ioo (-δ) δ, ‖G q r‖ ≤ KV * (1 + KY) := by
    apply ae_uIoc_imp_of_forall_Ioo hab
    intro r hr q hq
    obtain ⟨hqp, hθp⟩ := hVbound q hq r (hradi r hr) (Y q r)
    have hy := hYbound q (hqmem q hq).2 r θ (hradi r hr)
    rw [Real.norm_eq_abs]
    calc
      _ ≤ |Vq q r (Y q r)| +
          |Vθ q r (Y q r) * deriv (fun t => Y t r) q| := abs_add_le _ _
      _ = |Vq q r (Y q r)| +
          |Vθ q r (Y q r)| * |deriv (fun t => Y t r) q| := by rw [abs_mul]
      _ ≤ KV + KV * KY :=
        add_le_add hqp (mul_le_mul hθp hy (abs_nonneg _) hKV)
      _ = _ := by ring
  have hGderiv : ∀ᵐ r ∂volume, r ∈ uIoc (C.left m) b →
      ∀ q ∈ Ioo (-δ) δ, HasDerivAt (fun t => V t r (Y t r)) (G q r) q := by
    apply ae_uIoc_imp_of_forall_Ioo hab
    intro r hr q hq
    have hy := hN.minusFlow_q_hasDerivAt (hqmem q hq) m (hradi r hr) θ
    exact hasDerivAt_composed_velocity_coprod (F := fun t y => V t r y)
      (Y := fun t => Y t r) (hjet q hq r (hradi r hr) (Y q r)) hy
  have hd := hasDerivAt_scalarFlow_endpoint_of_dominated hab
    (Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ) hY
    (fun q hq => (hflow (x, q) (hqmem q hq) m θ).1)
    (fun q hq r hr => (hflow (x, q) (hqmem q hq) m θ).2.2.1 r (hradi r hr))
    hVi hGi.def'.aestronglyMeasurable hGbound
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => KV * (1 + KY))
      volume (C.left m) b) hGderiv
  apply hd.congr_deriv
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le hab] at hr
  exact hGzero r (hrad r hr)


theorem N01Properties.minusFlow_q_zero_partial_height_response
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {x : AnnularState S}
    (hx : stateGrading S base (x - C.referenceState) < ε)
    (m : ℕ) (θ : ℝ) {b : ℝ} (hb : b ∈ Icc (C.left m) (C.right m))
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
    HasDerivAt (fun q : ℝ => C.minusFlow (x, q) m b θ)
      (∫ r in C.left m..b,
        heightSpeedVariation (stateProfile D S C x) (stateU S x)
          (r, θ - opticalTravel (stateProfile D S C x) (C.left m) r)) 0 := by
  have hd := hN.minusFlow_q_zero_partial_hasDerivAt_of_speed hx m θ hb hδ hδε
    Vq Vθ hV hjet hbounded hVq0 hVθ0
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have hab : C.left m ≤ b := hb.1
  have hzero : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hx0 : (x, (0 : ℝ)) ∈ stateNeighborhood S C base ε :=
    ⟨hx, by simpa only [abs_zero] using hN.2.1⟩
  apply hd.congr_deriv
  apply intervalIntegral.integral_congr_ae
  apply ae_uIoc_imp_of_forall_Ioo hab
  intro r hr
  have hrf : r ∈ Ioo (C.left m) (C.right m) := ⟨hr.1, hr.2.trans_le hb.2⟩
  let y := C.minusFlow (x, 0) m r θ
  have hp : (r, y) ∈ annularOpen D :=
    ⟨⟨(hcontrol.1 m).1.trans hrf.1, hrf.2.trans (hcontrol.1 m).2.2⟩, mem_univ _⟩
  have hq : HasDerivAt
      (fun q : ℝ => minusCharacteristicSpeed (originalCoefficients D S C (x, q)) (r, y))
      (Vq 0 r y) 0 := by
    have h := (hjet 0 hzero r hrf y).comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) y))
    simpa [Function.comp_def, smul_eq_mul] using h
  have heq : Vq 0 r y =
      heightSpeedVariation (stateProfile D S C x) (stateU S x) (r, y) :=
    hq.unique (hN.hasDerivAt_minusCharacteristicSpeed_q_zero hS hT x hp)
  change Vq 0 r y = _
  rw [heq]
  dsimp only [y]
  rw [hN.minusFlow_zero_eq_opticalTravel hS hT hx0 m θ ⟨hrf.1.le, hrf.2.le⟩]


end ContinuousFlexibility.Statements
