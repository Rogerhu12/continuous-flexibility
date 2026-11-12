import ContinuousFlexibility.Analysis.N08OpticalSquareRoot
import ContinuousFlexibility.Analysis.N08CircleReferenceDiagonal
import ContinuousFlexibility.Analysis.N08StateLinearOperations

/-!
# Relative control of the actual optical radicand

The radial derivative of the genuine zero-parameter flow is its optical
speed. The N01 directional tower makes this derivative differentiable along
every allowed weighted control line. An affine radicand cannot cross zero
inside such a line, so its control coefficient is bounded relative to the
reference radicand. No placement of the control interval in `C.cell m` is
used, and preservation of the negative type is proved rather than assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem n08_affine_seminorm_lt
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (x v : E) {ε t : ℝ}
    (ht : |t| < ε / (1 + p v)) : p (x + t • v - x) < ε := by
  have hp : 0 < 1 + p v := by
    have := apply_nonneg p v
    linarith
  have hh := (lt_div_iff₀ hp).mp ht
  rw [add_sub_cancel_left, map_smul_eq_mul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (by linarith : p v ≤ 1 + p v)
    (abs_nonneg t)).trans_lt hh

private theorem n08_zero_parameter_line
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (x v : E) (t : ℝ) :
    (x, (0 : ℝ)) + t • (v, (0 : ℝ)) = (x + t • v, (0 : ℝ)) := by
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero]

private theorem n08_affine_radicand_bound
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (p : Seminorm ℝ E) (x v : E) (f : E × ℝ → ℝ) {ε A B K : ℝ}
    (hε : 0 < ε) (hA : 0 < A)
    (J : SmoothDirections {z : E × ℝ | p (z.1 - x) < ε ∧ |z.2| < ε} f)
    (hf : ∀ t : ℝ, (x + n08RealSMul t v, 0) ∈
      {z : E × ℝ | p (z.1 - x) < ε ∧ |z.2| < ε} →
        f (x + n08RealSMul t v, 0) = K - Real.sqrt (A + t * B)) :
    (ε / (1 + p v)) * |B| ≤ A := by
  have hp : 0 < 1 + p v := by
    have := apply_nonneg p v
    linarith
  have hmem (t : ℝ) (ht : |t| < ε / (1 + p v)) :
      (x + t • v, (0 : ℝ)) ∈
        {z : E × ℝ | p (z.1 - x) < ε ∧ |z.2| < ε} :=
    ⟨n08_affine_seminorm_lt p x v ht, (abs_zero : |(0 : ℝ)| = 0).trans_lt hε⟩
  apply n08_sqrtAffine_bound_of_lineDerivatives f (x, 0) (v, 0)
    hA (div_pos hε hp)
  · intro t ht
    have hm : (x, 0) + t • (v, 0) ∈
        {z : E × ℝ | p (z.1 - x) < ε ∧ |z.2| < ε} := by
      rw [n08_zero_parameter_line]
      exact hmem t ht
    exact ⟨_, J.hasProjectiveJetsOn.hasLineDerivAt J.open_domain hm (v, 0)⟩
  · intro t ht
    rw [n08_zero_parameter_line]
    exact hf t (hmem t ht)

private theorem n08_affine_radicand_bound_of_exists
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (p : Seminorm ℝ E) (x v : E) (f : E × ℝ → ℝ) {ε A B K : ℝ}
    (hε : 0 < ε) (hA : 0 < A)
    (hJ : ∃ J : SmoothDirections
      {z : E × ℝ | p (z.1 - x) < ε ∧ |z.2| < ε} f, True)
    (hf : ∀ t : ℝ, (x + n08RealSMul t v, 0) ∈
      {z : E × ℝ | p (z.1 - x) < ε ∧ |z.2| < ε} →
        f (x + n08RealSMul t v, 0) = K - Real.sqrt (A + t * B)) :
    (ε / (1 + p v)) * |B| ≤ A := by
  obtain ⟨J, _⟩ := hJ
  exact n08_affine_radicand_bound p x v f hε hA J hf

private theorem n08_smoothDirections_of_flow_tower
    {E P : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (U : Set E)
    (f : ℕ → ℕ → ℕ → P → E → ℝ) (region : ℕ → P → Prop)
    (normFun : ℕ → ℕ → P → ℝ → ℝ) (weight : ℝ → ℕ → ℝ)
    (base loss : ℕ) (x0 : E)
    (h : ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m a b y,
      a + b ≤ s → region m y → ∃ J : SmoothDirections U (f m a b y),
        ∀ z ∈ U, ∀ v : Fin k → E, normFun m a y (J.D k z v) ≤
          weight B m * oneHighVariationWeight p base (s + loss) (z - x0) v)
    (m a b : ℕ) (y : P) (hy : region m y) :
    ∃ J : SmoothDirections U (f m a b y), True := by
  obtain ⟨B, _, hB⟩ := h 1 (a + b)
  obtain ⟨J, _⟩ := hB m a b y le_rfl hy
  exact ⟨J, trivial⟩

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The spatial first derivative is computed from the actual ordinary ODE,
not from a postulated variational equation. -/
theorem n08_ordinaryFlow_radial_jet_zero_parameter
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (m : ℕ) (r θ : ℝ) (hr : r ∈ Ioo (C.left m) (C.right m)) :
    ordinaryFlowFamily S C m 1 0 (r, θ) (x, 0) =
      -opticalSpeed (stateProfile D S C x) r + opticalSpeed D.w r := by
  have hw := contDiff_stateProfile_of_n01 hS hT hN x
  have hdata := hN
  obtain ⟨hD, hε, href, hC, _, _, hflow, _⟩ := hdata
  obtain ⟨bounds, hbounds⟩ := hD.1
  have hg : RadialProfileGeometry D := hbounds.1
  have hcore : r ∈ radialCore D :=
    ⟨(hC.1 m).1.trans hr.1, hr.2.trans (hC.1 m).2.2⟩
  have hzero : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    ⟨n08_seminorm_center_lt (stateGrading S base) C.referenceState hε,
      (abs_zero : |(0 : ℝ)| = 0).trans_lt hε⟩
  have hxder := ((hflow (x, 0) hx m θ).2.2.1 r hr).congr_deriv
    (n08_minusCharacteristicSpeed_zero_parameter hg x hw r _ hcore)
  have hzeroder := ((hflow (C.referenceState, 0) hzero m θ).2.2.1 r hr).congr_deriv
    (n08_minusCharacteristicSpeed_reference hg href r _ hcore)
  have hd := hxder.sub hzeroder
  change HasDerivAt
    (fun s => C.minusFlow (x, 0) m s θ - C.minusFlow (C.referenceState, 0) m s θ)
    (-opticalSpeed (stateProfile D S C x) r - -opticalSpeed D.w r) r at hd
  simpa only [ordinaryFlowFamily, mixedDerivative, iteratedDeriv_one,
    iteratedDeriv_zero, sub_neg_eq_add] using hd.deriv

/-- A public affine-radicand identity for the actual logarithmic control. -/
theorem n08_opticalSpeed_logPerturbation {w χ : ℝ → ℝ} {t r : ℝ}
    (hw : DifferentiableAt ℝ w r) (hχ : DifferentiableAt ℝ χ r)
    (hr : r ≠ 0) (hwr : w r ≠ 0) :
    opticalSpeed (opticalLogPerturbation w χ t) r =
      Real.sqrt (-deriv w r / (r * w r) + t * (-deriv χ r / r)) := by
  have hp := (hw.hasDerivAt.mul ((hχ.hasDerivAt.const_mul t).exp)).deriv
  change deriv (fun s => w s * Real.exp (t * χ s)) r = _ at hp
  unfold opticalSpeed
  change Real.sqrt (-deriv (fun s => w s * Real.exp (t * χ s)) r /
    (r * (w r * Real.exp (t * χ r)))) = _
  rw [hp]
  congr 1
  field_simp [hr, hwr, (Real.exp_pos (t * χ r)).ne']
  ring

private theorem n08_ordinaryFlow_radial_smoothDirections
    (hN : N01Properties D T S C base loss ε) (m : ℕ) (r : ℝ)
    (hr : r ∈ Ioo (C.left m) (C.right m)) :
    ∃ J : SmoothDirections (stateNeighborhood S C base ε)
      (ordinaryFlowFamily S C m 1 0 (r, (0 : ℝ))), True :=
  n08_smoothDirections_of_flow_tower (E := AnnularState S × ℝ) (P := PolarPoint)
    (pairGrading (stateGrading S) realGrading) (stateNeighborhood S C base ε)
    (ordinaryFlowFamily S C) (fun m p => p.1 ∈ Ioo (C.left m) (C.right m))
    (fun m a p u => min (p.1 - C.left m) (C.right m - p.1) ^ a * |u|)
    (fun B m => B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
      T.E0 (T.sample (C.cell m)) ^ B)
    base loss (C.referenceState, 0) hN.2.2.2.2.2.2.2.2.2.2.2.2 m 1 0 (r, 0) hr

private theorem n08_optical_component_data
    (hN : N01Properties D T S C base loss ε)
    (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (C.left m) (C.right m)) :
    r ≠ 0 ∧ D.w r ≠ 0 ∧ DifferentiableAt ℝ D.w r ∧
      DifferentiableAt ℝ (C.control m) r ∧ 0 < -deriv D.w r / (r * D.w r) := by
  have hg : RadialProfileGeometry D := hN.1.1.choose_spec.1
  have hC := hN.2.2.2.1
  have hcore : r ∈ radialCore D :=
    ⟨(hC.1 m).1.trans hr.1, hr.2.trans (hC.1 m).2.2⟩
  have hrpos : 0 < r := hg.1.trans hcore.1
  have hwpos : 0 < D.w r := hg.2.2.2.2.1 r hcore
  exact ⟨hrpos.ne', hwpos.ne', hg.2.2.1.1.differentiable (by simp) r,
    (hC.2.2.2.2.2.1 m).1.differentiable (by simp) r,
    div_pos (neg_pos.mpr (hC.2.2.2.1 m r hr)) (mul_pos hrpos hwpos)⟩

private theorem n08_opticalSpeed_log_difference {w χ : ℝ → ℝ} {a t r : ℝ}
    (hw : DifferentiableAt ℝ w r) (hχ : DifferentiableAt ℝ χ r)
    (hr : r ≠ 0) (hwr : w r ≠ 0) :
    -opticalSpeed (opticalLogPerturbation w χ (t * a)) r + opticalSpeed w r =
      opticalSpeed w r - Real.sqrt (-deriv w r / (r * w r) +
        t * (a * (-deriv χ r / r))) := by
  rw [n08_opticalSpeed_logPerturbation hw hχ hr hwr]
  simp only [mul_assoc, sub_eq_add_neg, add_comm]

private theorem n08_controlBasis_optical_affine
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (C.left m) (C.right m)) (t : ℝ) :
    -opticalSpeed (stateProfile D S C
        (C.referenceState + n08StateSMul S t (0, 0, n08ControlBasis hS m, 0))) r +
      opticalSpeed D.w r =
      opticalSpeed D.w r - Real.sqrt (-deriv D.w r / (r * D.w r) +
        t * (T.H (T.sample m) ^ (3 / 4 : ℝ) * (-deriv (C.control m) r / r))) := by
  have hd := n08_optical_component_data hN m r hr
  exact (congrArg (fun w : ℝ → ℝ => -opticalSpeed w r + opticalSpeed D.w r)
      (n08_controlBasis_reference_profile hS hN.2.2.1 hN.2.2.2.1 m t)).trans
    (n08_opticalSpeed_log_difference (w := D.w) (χ := C.control m)
      (a := T.H (T.sample m) ^ (3 / 4 : ℝ)) (t := t) (r := r)
      hd.2.2.1 hd.2.2.2.1 hd.1 hd.2.1)

private theorem n08_controlBasis_flow_jet_affine
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (C.left m) (C.right m)) (t : ℝ)
    (ht : (C.referenceState + n08StateSMul S t (0, 0, n08ControlBasis hS m, 0), 0) ∈
      stateNeighborhood S C base ε) :
    ordinaryFlowFamily S C m 1 0 (r, (0 : ℝ))
      (C.referenceState + n08StateSMul S t (0, 0, n08ControlBasis hS m, 0), 0) =
      opticalSpeed D.w r - Real.sqrt (-deriv D.w r / (r * D.w r) +
        t * (T.H (T.sample m) ^ (3 / 4 : ℝ) * (-deriv (C.control m) r / r))) :=
  (n08_ordinaryFlow_radial_jet_zero_parameter hS hT hN
      (C.referenceState + n08StateSMul S t (0, 0, n08ControlBasis hS m, 0))
      ht m r 0 hr).trans
    (n08_controlBasis_optical_affine hS hN m r hr t)

/-- The same weighted control basis used by the circle diagonal has an
actual relative radicand bound on its own negative component. -/
theorem n08_controlBasis_radical_relative_bound
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (C.left m) (C.right m)) :
    (ε / (1 + stateGrading S base (0, 0, n08ControlBasis hS m, 0))) *
        |T.H (T.sample m) ^ (3 / 4 : ℝ) * (-deriv (C.control m) r / r)| ≤
      -deriv D.w r / (r * D.w r) :=
  n08_affine_radicand_bound_of_exists (E := AnnularState S)
    (stateGrading S base) C.referenceState
    (0, 0, n08ControlBasis hS m, 0) (ordinaryFlowFamily S C m 1 0 (r, (0 : ℝ)))
    (A := -deriv D.w r / (r * D.w r))
    (B := T.H (T.sample m) ^ (3 / 4 : ℝ) * (-deriv (C.control m) r / r))
    (K := opticalSpeed D.w r) hN.2.1 (n08_optical_component_data hN m r hr).2.2.2.2
    (n08_ordinaryFlow_radial_smoothDirections hN m r hr)
    (n08_controlBasis_flow_jet_affine hS hT hN m r hr)

end ContinuousFlexibility.Statements
