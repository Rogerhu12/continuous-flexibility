import ContinuousFlexibility.Analysis.N07aAngularFixedJetOperations
import ContinuousFlexibility.Analysis.N07aActualChartDifferentials
import ContinuousFlexibility.Analysis.CanonicalSourceMeasure
import ContinuousFlexibility.Geometry.EuclideanRigidity

/-!
# Fixed-state envelopes for the genuine inverse Jacobian

Positive-order jets of a planar map control its Jacobian. Taking the
absolute value costs no derivative at a nonzero Jacobian, since its sign
is constant in a neighborhood of each point. These facts apply on the
actual canonical domain and do not sample a fixed physical rectangle.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S}

namespace N07aAngularFixedJetEnvelope

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem linearMap
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {W : ℕ → Set E} {w : ℕ → ℝ} {f : ℕ → E → F}
    (hW : ∀ m, IsOpen (W m))
    (hfs : ∀ m, ContDiffOn ℝ ∞ (f m) (W m))
    (hf : N07aAngularFixedJetEnvelope T K W w f) (A : F →L[ℝ] G) :
    N07aAngularFixedJetEnvelope T K W w (fun m => A ∘ f m) := by
  intro n
  obtain ⟨e, he, he0, heb⟩ := hf n
  refine ⟨fun m => ‖A‖ * e m,
    N07aSampleSubpower.mul hD hT (N07aSampleSubpower.const hD hT ‖A‖) he,
    fun m => mul_nonneg (norm_nonneg _) (he0 m), fun m x hx => ?_⟩
  have h := A.norm_iteratedFDeriv_comp_left
    ((hfs m).contDiffAt ((hW m).mem_nhds hx)) (n := n) (by simp)
  exact h.trans ((mul_le_mul_of_nonneg_left (heb m x hx) (norm_nonneg A)).trans_eq
    (mul_assoc ‖A‖ (e m) (w m)).symm)

theorem neg
    {W : ℕ → Set E} {w : ℕ → ℝ} {f : ℕ → E → F}
    (hf : N07aAngularFixedJetEnvelope T K W w f) :
    N07aAngularFixedJetEnvelope T K W w (fun m x => -(f m x)) := by
  intro n
  obtain ⟨e, he, he0, heb⟩ := hf n
  refine ⟨e, he, he0, fun m x hx => ?_⟩
  simpa only [iteratedFDeriv_neg_apply, norm_neg] using heb m x hx

end N07aAngularFixedJetEnvelope

theorem n07a_norm_iteratedFDeriv_abs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContinuousAt f x) (hne : f x ≠ 0) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => |f y|) x‖ = ‖iteratedFDeriv ℝ n f x‖ := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hnear : ∀ᶠ y in 𝓝 x, f y < 0 := hf.eventually (Iio_mem_nhds hneg)
    have he : (fun y => |f y|) =ᶠ[𝓝 x] (fun y => -(f y)) := by
      filter_upwards [hnear] with y hy
      exact abs_of_neg hy
    rw [(he.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_neg_apply, norm_neg]
  · have hnear : ∀ᶠ y in 𝓝 x, 0 < f y := hf.eventually (Ioi_mem_nhds hpos)
    have he : (fun y => |f y|) =ᶠ[𝓝 x] f := by
      filter_upwards [hnear] with y hy
      exact abs_of_pos hy
    rw [(he.iteratedFDeriv ℝ n).eq_of_nhds]

theorem N07aAngularFixedJetEnvelope.abs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : ℕ → Set E} {w : ℕ → ℝ} {f : ℕ → E → ℝ}
    (hfs : ∀ m x, x ∈ W m → ContinuousAt (f m) x)
    (hne : ∀ m x, x ∈ W m → f m x ≠ 0)
    (hf : N07aAngularFixedJetEnvelope T K W w f) :
    N07aAngularFixedJetEnvelope T K W w (fun m x => |f m x|) := by
  intro n
  obtain ⟨e, he, he0, heb⟩ := hf n
  refine ⟨e, he, he0, fun m x hx => ?_⟩
  rw [n07a_norm_iteratedFDeriv_abs (hfs m x hx) (hne m x hx)]
  exact heb m x hx

theorem n07a_directional_fixedEnvelope_of_positiveJets
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {W : ℕ → Set E} {f : ℕ → E → F}
    (hW : ∀ m, IsOpen (W m))
    (hfs : ∀ m, ContDiffOn ℝ ∞ (f m) (W m))
    (hf : ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ m x, x ∈ W m → ‖iteratedFDeriv ℝ n (f m) x‖ ≤ e m)
    (v : E) :
    N07aAngularFixedJetEnvelope T K W (fun _ => 1)
      (fun m x => fderiv ℝ (f m) x v) := by
  intro n
  obtain ⟨e, he, he0, heb⟩ := hf (n + 1) (Nat.succ_pos n)
  refine ⟨fun m => ‖v‖ * e m,
    N07aSampleSubpower.mul hD hT (N07aSampleSubpower.const hD hT ‖v‖) he,
    fun m => mul_nonneg (norm_nonneg v) (he0 m), fun m x hx => ?_⟩
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ (f m)) x :=
    ((hfs m).contDiffAt ((hW m).mem_nhds hx)).fderiv_right (by simp)
  have h := norm_iteratedFDeriv_clm_apply_const (c := v) (n := n) hd (by simp)
  rw [norm_iteratedFDeriv_fderiv] at h
  simpa only [mul_one] using
    h.trans (mul_le_mul_of_nonneg_left (heb m x hx) (norm_nonneg v))

theorem n07a_planeJacobian_fixedEnvelope_of_positiveJets
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {W : ℕ → Set PolarPoint} {F : ℕ → PolarPoint → PolarPoint}
    (hW : ∀ m, IsOpen (W m))
    (hF : ∀ m, ContDiffOn ℝ ∞ (F m) (W m))
    (hb : ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ m x, x ∈ W m → ‖iteratedFDeriv ℝ n (F m) x‖ ≤ e m) :
    N07aAngularFixedJetEnvelope T K W (fun _ => 1) (fun m => planeJacobian (F m)) := by
  let R : ℕ → PolarPoint → PolarPoint := fun m x => fderiv ℝ (F m) x (1, 0)
  let A : ℕ → PolarPoint → PolarPoint := fun m x => fderiv ℝ (F m) x (0, 1)
  have hs (v : PolarPoint) (m : ℕ) :
      ContDiffOn ℝ ∞ (fun x => fderiv ℝ (F m) x v) (W m) := by
    intro x hx
    exact ((((hF m).contDiffAt ((hW m).mem_nhds hx)).fderiv_right (by simp)).clm_apply
      (contDiffAt_const (c := v))).contDiffWithinAt
  have hR := n07a_directional_fixedEnvelope_of_positiveJets hD hT hW hF hb (1, 0)
  have hA := n07a_directional_fixedEnvelope_of_positiveJets hD hT hW hF hb (0, 1)
  have hR₁ := hR.linearMap hD hT hW (hs (1, 0)) (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hR₂ := hR.linearMap hD hT hW (hs (1, 0)) (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hA₁ := hA.linearMap hD hT hW (hs (0, 1)) (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hA₂ := hA.linearMap hD hT hW (hs (0, 1)) (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hP : N07aAngularFixedJetEnvelope T K W (fun _ => 1)
      (fun m x => (R m x).1 * (A m x).2) := by
    simpa only [one_mul] using N07aAngularFixedJetEnvelope.mul hD hT hW
      (fun m => (hs (1, 0) m).fst) (fun m => (hs (0, 1) m).snd)
      hR₁ hA₂ (fun _ => zero_le_one) (fun _ => zero_le_one)
  have hQ : N07aAngularFixedJetEnvelope T K W (fun _ => 1)
      (fun m x => (R m x).2 * (A m x).1) := by
    simpa only [one_mul] using N07aAngularFixedJetEnvelope.mul hD hT hW
      (fun m => (hs (1, 0) m).snd) (fun m => (hs (0, 1) m).fst)
      hR₂ hA₁ (fun _ => zero_le_one) (fun _ => zero_le_one)
  have hsum := hP.add hD hT hW
    (fun m => ((hs (1, 0) m).fst).mul ((hs (0, 1) m).snd))
    (fun m => (((hs (1, 0) m).snd).mul ((hs (0, 1) m).fst)).neg) hQ.neg
  simpa only [planeJacobian, sub_eq_add_neg] using hsum

theorem n07a_actual_inverseChart_jacobian_abs
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hgeom : CanonicalGeometry D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {y : PolarPoint}
    (hy : y ∈ canonicalOpen S K m) :
    |planeJacobian (K.inverseChart z m) y| =
      |planeJacobian (K.chart z m) (K.inverseChart z m y)|⁻¹ := by
  have hi := (n07a_actualChart_fderiv_inverse hgeom hz hs m hy).1
  have hlin :
      (fderiv ℝ (K.chart z m) (K.inverseChart z m y)).toLinearMap.comp
          (fderiv ℝ (K.inverseChart z m) y).toLinearMap =
        LinearMap.id := congrArg ContinuousLinearMap.toLinearMap hi
  have hdet := congrArg LinearMap.det hlin
  have hmul : planeJacobian (K.chart z m) (K.inverseChart z m y) *
      planeJacobian (K.inverseChart z m) y = 1 := by
    simpa only [planeJacobian_eq_fderiv_det, LinearMap.det_comp, LinearMap.det_id] using hdet
  have habs : |planeJacobian (K.chart z m) (K.inverseChart z m y)| *
      |planeJacobian (K.inverseChart z m) y| = 1 := by
    simpa only [abs_mul, abs_one] using congrArg abs hmul
  have hne : |planeJacobian (K.chart z m) (K.inverseChart z m y)| ≠ 0 :=
    abs_ne_zero.mpr ((hgeom.charts z hz hs m).2.2.2.2.2.2.2 _
      ((hgeom.charts z hz hs m).2.1 hy)).2.1
  rw [← one_div]
  exact (eq_div_iff hne).mpr (by simpa only [mul_comm] using habs)

theorem n07a_canonicalHeightInverse_eq_sourceFactorInverse
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    (z : CanonicalGeometry.Parameter S)
    (hz : liftSectorParameter S C z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S (liftSectorParameter S C z).1)
    (m : ℕ) {y : PolarPoint} (hy : y ∈ canonicalOpen S K m) :
    (K.height (liftSectorParameter S C z) m
      (K.inverseChart (liftSectorParameter S C z) m y))⁻¹ =
        n07aCanonicalAtomField D T S C L K .sourceFactorInverse z m y *
          |planeJacobian (K.inverseChart (liftSectorParameter S C z) m) y| := by
  have hc := h04.1.charts (liftSectorParameter S C z) hz hs m
  have hx := hc.2.1 hy
  have hh := (hc.2.2.2.2.2.2.2 _ hx).1.ne'
  have hj := abs_ne_zero.mpr (hc.2.2.2.2.2.2.2 _ hx).2.1
  have hunit := n07aCanonicalUnitPoint_inverse (h04.1.referenceBounds m).2.1 y
  rw [n07a_actual_inverseChart_jacobian_abs h04.1 hz hs m hy]
  simp only [n07aCanonicalAtomField, Function.comp_apply, CanonicalGeometry.atom,
    hunit, canonicalSource, mul_one]
  field_simp [hh, hj]

end ContinuousFlexibility.Analysis
