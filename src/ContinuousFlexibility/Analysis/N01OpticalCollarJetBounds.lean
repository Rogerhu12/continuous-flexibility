import ContinuousFlexibility.Analysis.N01ReferenceOpticalCollars
import ContinuousFlexibility.Analysis.N01NeighborhoodRestriction

/-!
# The optical collar controls the radial endpoint weights in N01

A positive optical-speed lower bound and the squared-speed derivative
bound force a quantitative distance from both turning radii. Thus the
radial endpoint factors in the original N01 flow tower can be divided
out on the actual correction collars with a fixed radial-cell power.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01OpticalCollarJetBoundsStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

theorem abs_le_of_power_weight_bound
    {d K E A C y : ℝ} (n : ℕ) (hd : 0 < d) (hE : 0 < E)
    (hdist : d⁻¹ ≤ K * E ^ A) (hraw : d ^ n * |y| ≤ C) :
    |y| ≤ K ^ n * E ^ (A * n) * C := by
  have hC : 0 ≤ C := (mul_nonneg (pow_nonneg hd.le _) (abs_nonneg _)).trans hraw
  have h := mul_le_mul_of_nonneg_left hraw (pow_nonneg (inv_nonneg.mpr hd.le) n)
  have heq : d⁻¹ ^ n * (d ^ n * |y|) = |y| := by
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hd.ne', one_pow, one_mul]
  rw [heq] at h
  have hpow := pow_le_pow_left₀ (inv_nonneg.mpr hd.le) hdist n
  have hb := h.trans (mul_le_mul_of_nonneg_right hpow hC)
  rw [mul_pow, ← Real.rpow_mul_natCast hE.le] at hb
  exact hb

/-- Extracting a scalar zeroth jet is independent of the concrete
parameter model and does not unfold any of its seminorm instances. -/
theorem smoothDirections_zeroth_spatialWeight_bound
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {U : Set E} {f : E → ℝ} (q : ℕ → Seminorm ℝ E)
    (base high : ℕ) (x₀ : E) (d A : ℝ)
    (h : ∃ J : SmoothDirections U f, ∀ x ∈ U, ∀ v : Fin 0 → E,
      d * |J.D 0 x v| ≤ A * oneHighVariationWeight q base high (x - x₀) v)
    (x : E) (hx : x ∈ U) :
    d * |f x| ≤ A * (1 + q high (x - x₀)) := by
  obtain ⟨J, hJ⟩ := h
  simpa only [oneHighVariationWeight, Fin.prod_univ_zero, Fin.sum_univ_zero,
    mul_one, add_zero, J.zero x hx] using hJ x hx Fin.elim0

/-- Division by a scalar spatial weight keeps the same parameter tower
and its complete one-high-factor budget. -/
theorem smoothDirections_divide_spatialWeight_bound
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {U : Set E} {f : E → ℝ} (q : ℕ → Seminorm ℝ E)
    (base high k a : ℕ) (x₀ : E) (d K W P A : ℝ)
    (hd : 0 < d) (hW : 0 < W) (hdist : d⁻¹ ≤ K * W ^ P)
    (h : ∃ J : SmoothDirections U f, ∀ x ∈ U, ∀ v : Fin k → E,
      d ^ a * |J.D k x v| ≤ A * oneHighVariationWeight q base high (x - x₀) v) :
    ∃ J : SmoothDirections U f, ∀ x ∈ U, ∀ v : Fin k → E,
      |J.D k x v| ≤ K ^ a * W ^ (P * a) *
        (A * oneHighVariationWeight q base high (x - x₀) v) := by
  obtain ⟨J, hJ⟩ := h
  refine ⟨J, fun x hx v => ?_⟩
  exact abs_le_of_power_weight_bound a hd hW hdist (hJ x hx v)

theorem opticalSpeed_lower_boundaryDistance
    {w : ℝ → ℝ} {l h r τ M : ℝ}
    (hl : 0 < l) (hlh : l < h) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ s ∈ Icc l h, 0 < w s)
    (hrootl : deriv w l = 0) (hrooth : deriv w h = 0)
    (hM : 0 ≤ M)
    (hbound : ∀ s ∈ Icc l h,
      |deriv (fun t => -deriv w t / (t * w t)) s| ≤ M)
    (hr : r ∈ Ioo l h) (hτ : 0 < τ) (hspeed : τ ≤ opticalSpeed w r) :
    (min (r - l) (h - r))⁻¹ ≤ (M + 1) / τ ^ 2 := by
  let Q (s : ℝ) := -deriv w s / (s * w s)
  have hd := (contDiff_infty_iff_deriv.mp hw).2
  have hQdiff (s : ℝ) (hs : s ∈ Icc l h) : DifferentiableAt ℝ Q s :=
    (hd.differentiable (by simp) s).neg.div
      (differentiableAt_id.mul (hw.differentiable (by simp) s))
      (mul_pos (hl.trans_le hs.1) (hpos s hs)).ne'
  have hQlip (s : ℝ) (hs : s ∈ Icc l h) (t : ℝ) (ht : t ∈ Icc l h) :
      |Q t - Q s| ≤ M * |t - s| := by
    simpa only [Real.norm_eq_abs] using
      (convex_Icc l h).norm_image_sub_le_of_norm_deriv_le hQdiff
        (fun u hu => by simpa only [Real.norm_eq_abs] using hbound u hu) hs ht
  have hQr : 0 < Q r := Real.sqrt_pos.mp (hτ.trans_le hspeed)
  have hsq : τ ^ 2 ≤ Q r := by
    have h := pow_le_pow_left₀ hτ.le hspeed 2
    change τ ^ 2 ≤ (Real.sqrt (Q r)) ^ 2 at h
    simpa only [Real.sq_sqrt hQr.le] using h
  have hQl : Q l = 0 := by simp only [Q, hrootl, neg_zero, zero_div]
  have hQh : Q h = 0 := by simp only [Q, hrooth, neg_zero, zero_div]
  have hleft : Q r ≤ M * (r - l) := by
    have h := hQlip l ⟨le_rfl, hlh.le⟩ r ⟨hr.1.le, hr.2.le⟩
    simpa only [hQl, sub_zero, abs_of_pos hQr, abs_of_pos (sub_pos.mpr hr.1)] using h
  have hright : Q r ≤ M * (h - r) := by
    have hb := hQlip h ⟨hlh.le, le_rfl⟩ r ⟨hr.1.le, hr.2.le⟩
    simpa only [hQh, sub_zero, abs_of_pos hQr, abs_sub_comm r h,
      abs_of_pos (sub_pos.mpr hr.2)] using hb
  let d := min (r - l) (h - r)
  have hdpos : 0 < d := lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)
  have hqdist : τ ^ 2 ≤ M * d := by
    dsimp only [d]
    rw [mul_min_of_nonneg _ _ hM]
    exact le_min (hsq.trans hleft) (hsq.trans hright)
  have hsq' : τ ^ 2 ≤ (M + 1) * d :=
    hqdist.trans (mul_le_mul_of_nonneg_right (by linarith : M ≤ M + 1) hdpos.le)
  apply (inv_le_iff_one_le_mul₀ hdpos).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hτ)).mpr
  simpa only [one_mul, mul_one, mul_comm] using hsq'

theorem N01Properties.opticalCollar_inverse_boundaryDistance_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (j : ℕ → ℕ) (x δ : ℕ → ℝ) {B : ℝ} (hB : 0 < B)
    (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (hinside : ∀ m, C.left m < x m - δ m ∧ x m + δ m < C.right m)
    (hspeed : ∀ m r, r ∈ Icc (x m - δ m) (x m + δ m) →
      radialE (D.cellIndex (j m)) ^ (-B) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r) :
    ∃ K A : ℝ, 0 < K ∧ 0 < A ∧ ∀ m r,
      r ∈ Icc (x m - δ m) (x m + δ m) →
      (min (r - C.left m) (C.right m - r))⁻¹ ≤
        K * radialE (D.cellIndex (j m)) ^ A := by
  obtain ⟨K, A, hK, hA, hderiv⟩ := hN.1.1.opticalSquaredSpeed_deriv_component_bound
  obtain ⟨_, hdata⟩ := hN.1.1
  have hg : RadialProfileGeometry D := hdata.1
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  let R := D.b - D.a
  have hR : 0 < R := sub_pos.mpr hg.2.1
  refine ⟨4 * (K + 1) * R ^ 2, A + 2 * B,
    by positivity, by linarith only [hA, hB], fun m r hr => ?_⟩
  have hm : r ∈ Ioo (C.left m) (C.right m) :=
    ⟨(hinside m).1.trans_le hr.1, hr.2.trans_lt (hinside m).2⟩
  let E := radialE (D.cellIndex (j m))
  have hE : 0 < E := Real.exp_pos _
  have hE₁ : 1 ≤ E := by
    have hn : 0 ≤ (D.cellIndex (j m) : ℝ) := Nat.cast_nonneg _
    have he : 1 ≤ Real.exp 1 + (D.cellIndex (j m) : ℝ) :=
      (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans
        (le_add_of_nonneg_right hn)
    exact Real.one_le_exp_iff.mpr
      (mul_nonneg (Real.rpow_nonneg hn _) (Real.log_nonneg he))
  have hpos (s : ℝ) (hs : s ∈ Icc (C.left m) (C.right m)) : 0 < D.w s :=
    hg.2.2.2.2.1 s ⟨(hC.1 m).1.trans_le hs.1, hs.2.trans_lt (hC.1 m).2.2⟩
  have h := opticalSpeed_lower_boundaryDistance
    (hg.1.trans (hC.1 m).1) (hC.1 m).2.1 hg.2.2.1.1 hpos
    (hC.2.1 m).1 (hC.2.1 m).2.1
    (mul_nonneg hK.le (Real.rpow_nonneg hE.le _))
    (hderiv _ _ (j m) (n01Properties_negativeRadialComponent hN m) (hcell m))
    hm (div_pos (Real.rpow_pos_of_pos hE _) (mul_pos (by norm_num) hR))
    (hspeed m r hr)
  have hEA : 1 ≤ E ^ A := Real.one_le_rpow hE₁ hA.le
  have hnum : K * E ^ A + 1 ≤ (K + 1) * E ^ A := by nlinarith only [hEA]
  have hden : 0 < (E ^ (-B) / (2 * R)) ^ 2 :=
    sq_pos_of_pos (div_pos (Real.rpow_pos_of_pos hE _) (mul_pos (by norm_num) hR))
  refine h.trans ((div_le_div_of_nonneg_right hnum hden.le).trans_eq ?_)
  have hp : E ^ (A + 2 * B) * (E ^ (-B)) ^ 2 = E ^ A := by
    rw [pow_two, ← Real.rpow_add hE, ← Real.rpow_add hE]
    congr 1
    ring
  apply (div_eq_iff hden.ne').mpr
  rw [← hp, div_pow]
  field_simp [hR.ne']
  <;> ring


/-- Extract the zeroth parameter jet once, before applying the geometric
collar factor. The equality of actual jets is transported explicitly. -/
theorem N01Properties.ordinaryFlowFamily_weighted_zeroth_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ z ∈ stateNeighborhood S C base ε, ∀ m a b p,
      a + b ≤ s → p.1 ∈ Ioo (C.left m) (C.right m) →
      min (p.1 - C.left m) (C.right m - p.1) ^ a *
        |ordinaryFlowFamily S C m a b p z| ≤
        B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          (1 + pairGrading (stateGrading S) realGrading (s + loss)
            (z - (C.referenceState, 0))) := by
  let hdata := hN.2.2.2.2.2.2.2.2.2.2.2.2 0 s
  let B : ℝ := hdata.choose
  have hB : 0 < B := hdata.choose_spec.1
  have hpoint : ∀ z ∈ stateNeighborhood S C base ε, ∀ m a b p,
      a + b ≤ s → p.1 ∈ Ioo (C.left m) (C.right m) →
      min (p.1 - C.left m) (C.right m - p.1) ^ a *
        |ordinaryFlowFamily S C m a b p z| ≤
        B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          (1 + pairGrading (stateGrading S) realGrading (s + loss)
            (z - (C.referenceState, 0))) := by
    intro z hz m a b p hab hp
    exact smoothDirections_zeroth_spatialWeight_bound
      (pairGrading (stateGrading S) realGrading) base (s + loss)
      (C.referenceState, (0 : ℝ))
      (min (p.1 - C.left m) (C.right m - p.1) ^ a)
      (B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ B)
      (hdata.choose_spec.2 m a b p hab hp) z hz
  exact ⟨B, hB, hpoint⟩

/-- The actual N01 spatial-flow jet estimate on the selected collars,
with the endpoint factors divided out quantitatively. This is the
ordinary mixed derivative appearing in the original tower. -/
theorem N01Properties.ordinaryFlowFamily_collar_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (j : ℕ → ℕ) (x δ : ℕ → ℝ) {B₀ : ℝ} (hB₀ : 0 < B₀)
    (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (hinside : ∀ m, C.left m < x m - δ m ∧ x m + δ m < C.right m)
    (hspeed : ∀ m r, r ∈ Icc (x m - δ m) (x m + δ m) →
      radialE (D.cellIndex (j m)) ^ (-B₀) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r)
    (s : ℕ) :
    ∃ K A B : ℝ, 0 < K ∧ 0 < A ∧ 0 < B ∧
      ∀ z ∈ stateNeighborhood S C base ε, ∀ m a b p,
      a + b ≤ s → p.1 ∈ Icc (x m - δ m) (x m + δ m) →
      |ordinaryFlowFamily S C m a b p z| ≤
        K ^ a * radialE (D.cellIndex (j m)) ^ (A * a) *
          (B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell m)) ^ B *
            (1 + pairGrading (stateGrading S) realGrading (s + loss)
              (z - (C.referenceState, 0)))) := by
  have hgeom : ∃ K A : ℝ, 0 < K ∧ 0 < A ∧ ∀ m r,
      r ∈ Icc (x m - δ m) (x m + δ m) →
      (min (r - C.left m) (C.right m - r))⁻¹ ≤
        K * radialE (D.cellIndex (j m)) ^ A :=
    @N01Properties.opticalCollar_inverse_boundaryDistance_bound
      D T S C base loss ε hN j x δ B₀ hB₀ hcell hinside hspeed
  obtain ⟨K, A, hK, hA, hdist⟩ := hgeom
  obtain ⟨B, hB, hraw⟩ := hN.ordinaryFlowFamily_weighted_zeroth_bound s
  refine ⟨K, A, B, hK, hA, hB, fun z hz m a b p hab hp => ?_⟩
  have hm : p.1 ∈ Ioo (C.left m) (C.right m) :=
    ⟨(hinside m).1.trans_le hp.1, hp.2.trans_lt (hinside m).2⟩
  have hd : 0 < min (p.1 - C.left m) (C.right m - p.1) :=
    lt_min (sub_pos.mpr hm.1) (sub_pos.mpr hm.2)
  exact abs_le_of_power_weight_bound
    (d := min (p.1 - C.left m) (C.right m - p.1))
    (K := K) (E := radialE (D.cellIndex (j m))) (A := A)
    (C := B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
      T.E0 (T.sample (C.cell m)) ^ B *
      (1 + pairGrading (stateGrading S) realGrading (s + loss)
        (z - (C.referenceState, 0))))
    (y := ordinaryFlowFamily S C m a b p z) a hd (Real.exp_pos _)
    (hdist m p.1 hp) (hraw z hz m a b p hab hm)

/-- The same two geometric constants precede every parameter and spatial
order. The actual N01 directional tower, its neighborhood and its
one-high-factor input weight are retained without specialization to a
fixed state. -/
theorem N01Properties.ordinaryFlowFamily_collar_directional_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (j : ℕ → ℕ) (x δ : ℕ → ℝ) {B₀ : ℝ} (hB₀ : 0 < B₀)
    (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (hinside : ∀ m, C.left m < x m - δ m ∧ x m + δ m < C.right m)
    (hspeed : ∀ m r, r ∈ Icc (x m - δ m) (x m + δ m) →
      radialE (D.cellIndex (j m)) ^ (-B₀) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r) :
    ∃ K A : ℝ, 0 < K ∧ 0 < A ∧ ∀ k s : ℕ,
      ∃ B : ℝ, 0 < B ∧ ∀ m a b p,
      a + b ≤ s → p.1 ∈ Icc (x m - δ m) (x m + δ m) →
      ∃ J : SmoothDirections (stateNeighborhood S C base ε) (ordinaryFlowFamily S C m a b p),
        ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin k → (AnnularState S × ℝ),
        |J.D k z v| ≤ K ^ a * radialE (D.cellIndex (j m)) ^ (A * a) *
          (B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ B *
            oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
              base (s + loss) (z - (C.referenceState, 0)) v) := by
  have hgeom : ∃ K A : ℝ, 0 < K ∧ 0 < A ∧ ∀ m r,
      r ∈ Icc (x m - δ m) (x m + δ m) →
      (min (r - C.left m) (C.right m - r))⁻¹ ≤
        K * radialE (D.cellIndex (j m)) ^ A :=
    @N01Properties.opticalCollar_inverse_boundaryDistance_bound
      D T S C base loss ε hN j x δ B₀ hB₀ hcell hinside hspeed
  obtain ⟨K, A, hK, hA, hdist⟩ := hgeom
  refine ⟨K, A, hK, hA, fun k s => ?_⟩
  let hdata := hN.2.2.2.2.2.2.2.2.2.2.2.2 k s
  let B : ℝ := hdata.choose
  have hB : 0 < B := hdata.choose_spec.1
  have hpoint : ∀ m a b p,
      a + b ≤ s → p.1 ∈ Icc (x m - δ m) (x m + δ m) →
      ∃ J : SmoothDirections (stateNeighborhood S C base ε) (ordinaryFlowFamily S C m a b p),
        ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin k → (AnnularState S × ℝ),
        |J.D k z v| ≤ K ^ a * radialE (D.cellIndex (j m)) ^ (A * a) *
          (B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ B *
            oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
              base (s + loss) (z - (C.referenceState, 0)) v) := by
    intro m a b p hab hp
    have hm : p.1 ∈ Ioo (C.left m) (C.right m) :=
      ⟨(hinside m).1.trans_le hp.1, hp.2.trans_lt (hinside m).2⟩
    have hd : 0 < min (p.1 - C.left m) (C.right m - p.1) :=
      lt_min (sub_pos.mpr hm.1) (sub_pos.mpr hm.2)
    exact smoothDirections_divide_spatialWeight_bound
      (pairGrading (stateGrading S) realGrading) base (s + loss) k a
      (C.referenceState, (0 : ℝ))
      (min (p.1 - C.left m) (C.right m - p.1)) K
      (radialE (D.cellIndex (j m))) A
      (B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ B)
      hd (Real.exp_pos _) (hdist m p.1 hp)
      (hdata.choose_spec.2 m a b p hab hm)
  exact Exists.intro B (And.intro hB hpoint)


end ContinuousFlexibility.Statements

