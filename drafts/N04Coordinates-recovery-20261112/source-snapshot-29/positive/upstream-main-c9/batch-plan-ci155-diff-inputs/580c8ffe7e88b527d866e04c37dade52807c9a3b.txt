import ContinuousFlexibility.Analysis.N05TricomiNullCoordinates
import ContinuousFlexibility.Analysis.N01RadialFlow
import Mathlib.Topology.Algebra.Field

/-!
# Transport of the actual reference null coordinates

The null identities of N04 imply one fixed signed radial transport
equation on each connected negative piece.  Integrating its actual
characteristics identifies the null coordinate with its value at either
physical endpoint.  Only the forward chart is used on the boundary.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The actual characteristic formula for a scalar transport equation on
a closed strip.  No differentiability at its two radial endpoints is used. -/
theorem n06_strip_radial_transport
    {a b : ℝ} (hab : a < b) {N : PolarPoint → ℝ} {v : ℝ → ℝ} {τ : ℝ}
    (hN : ContinuousOn N (Icc a b ×ˢ (univ : Set ℝ)))
    (hdN : ∀ p : PolarPoint, p.1 ∈ Ioo a b → DifferentiableAt ℝ N p)
    (hv : ContinuousOn v (Icc a b))
    (heq : ∀ p : PolarPoint, p.1 ∈ Ioo a b →
      radialPartial N p = τ * v p.1 * angularPartial N p)
    {r s : ℝ} (hr : r ∈ Icc a b) (hs : s ∈ Icc a b) (θ : ℝ) :
    N (r, θ) = N (s, θ + τ * (∫ x in s..r, v x)) := by
  let T : ℝ → ℝ := fun t => ∫ x in a..t, v x
  have hint (t : ℝ) (ht : t ∈ Icc a b) : IntervalIntegrable v volume a t :=
    (hv.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  have hTc : ContinuousOn T (Icc a b) := by
    simpa only [T, uIcc_of_le hab.le] using
      intervalIntegral.continuousOn_primitive_interval'
        (hv.intervalIntegrable_of_Icc hab.le) (a := a) left_mem_uIcc
  have hTd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt T (v t) t := by
    exact intervalIntegral.integral_hasDerivAt_right (hint t ⟨ht.1.le, ht.2.le⟩)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (hv.mono Ioo_subset_Icc_self) t ht)
      ((hv.mono Ioo_subset_Icc_self).continuousAt (isOpen_Ioo.mem_nhds ht))
  let q : ℝ → PolarPoint := fun t => (t, θ + τ * (T r - T t))
  let F : ℝ → ℝ := fun t => N (q t)
  have hq : ContinuousOn q (Icc a b) :=
    continuousOn_id.prodMk
      (continuousOn_const.add (continuousOn_const.mul (continuousOn_const.sub hTc)))
  have hF : ContinuousOn F (Icc a b) :=
    hN.comp hq (fun t ht => ⟨ht, mem_univ _⟩)
  have hdF (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt F 0 t := by
    have hqd : HasDerivAt q (1, -τ * v t) t := by
      simpa only [q, id_eq, Pi.sub_apply, zero_sub, mul_neg, neg_mul] using
        (hasDerivAt_id t).prodMk
          ((((hasDerivAt_const t (T r)).sub (hTd t ht)).const_mul τ).const_add θ)
    have hh := (hdN (q t) ht).hasFDerivAt.comp_hasDerivAt t hqd
    have hvalue : fderiv ℝ N (q t) (1, -τ * v t) = 0 := by
      rw [polarCLM_apply_decompose]
      change 1 * radialPartial N (q t) + (-τ * v t) * angularPartial N (q t) = 0
      rw [heq (q t) ht]
      dsimp only [q]
      ring
    simpa only [F, Function.comp_def, hvalue] using hh
  have hconstant (t : ℝ) (ht : t ∈ Icc a b) : F t = F a := by
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (f := F) (f' := fun _ : ℝ => (0 : ℝ)) ht.1
      (hF.mono (Icc_subset_Icc le_rfl ht.2))
      (fun u hu => hdF u ⟨hu.1, hu.2.trans_le ht.2⟩)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a t)
    simpa only [intervalIntegral.integral_zero, sub_eq_zero] using he.symm
  have hdiff : T r - T s = ∫ x in s..r, v x :=
    intervalIntegral.integral_interval_sub_left (hint r hr) (hint s hs)
  have he := (hconstant r hr).trans (hconstant s hs).symm
  simpa only [F, q, sub_self, mul_zero, add_zero, hdiff] using he

/-- A continuous pair of real null derivatives has one sign throughout
the connected physical strip.  The nonzero angular derivative rules out
switching between the two characteristic directions. -/
theorem n06_null_derivatives_signed
    {a b : ℝ} {N : PolarPoint → ℝ} {v : ℝ → ℝ}
    (hr : ContinuousOn (radialPartial N) (Ioo a b ×ˢ (univ : Set ℝ)))
    (ht : ContinuousOn (angularPartial N) (Ioo a b ×ˢ (univ : Set ℝ)))
    (hv : ContinuousOn (fun p : PolarPoint => v p.1)
      (Ioo a b ×ˢ (univ : Set ℝ)))
    (hne : ∀ p : PolarPoint, p.1 ∈ Ioo a b → v p.1 * angularPartial N p ≠ 0)
    (hsq : ∀ p : PolarPoint, p.1 ∈ Ioo a b →
      radialPartial N p ^ 2 = (v p.1 * angularPartial N p) ^ 2) :
    ∃ τ : ℝ, τ ^ 2 = 1 ∧ ∀ p : PolarPoint, p.1 ∈ Ioo a b →
      radialPartial N p = τ * v p.1 * angularPartial N p := by
  have hc : IsPreconnected (Ioo a b ×ˢ (univ : Set ℝ)) :=
    isPreconnected_Ioo.prod isPreconnected_univ
  have hg : ContinuousOn (fun p : PolarPoint => v p.1 * angularPartial N p)
      (Ioo a b ×ˢ (univ : Set ℝ)) := hv.mul ht
  have hsplit := hc.eq_or_eq_neg_of_sq_eq hr hg
    (fun p hp => hsq p hp.1) (fun {p} hp => hne p hp.1)
  rcases hsplit with hplus | hminus
  · refine ⟨1, by norm_num, fun p hp => ?_⟩
    simpa only [one_mul] using hplus ⟨hp, mem_univ _⟩
  · refine ⟨-1, by norm_num, fun p hp => ?_⟩
    simpa only [Pi.neg_apply, neg_one_mul, neg_mul, one_mul] using hminus ⟨hp, mem_univ _⟩

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}

/-- The closed physical half of an original negative cut lies strictly
inside the physical annulus. -/
theorem n06_cutPiece_closed_subset
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) {i : ℕ} (hi : i = (K.cutPair m).1 ∨ i = (K.cutPair m).2) :
    Icc (K.physicalLeft i) (K.physicalRight i) ⊆ radialCore D := by
  have hg : controlGeometryConditions D S C := h.1.1.1.2.2.2.1
  have hpieces := h.2.2.2.2.1.1.referenceBounds
  have hcuts := h.2.2.2.2.1.2.1.1.1
  obtain ⟨_, _, hl, hr, hmeet, _⟩ := hcuts m
  intro r hri
  rcases hi with rfl | rfl
  · constructor
    · rw [hl] at hri
      exact (hg.1 m).1.trans_le hri.1
    · have hcut : K.physicalRight (K.cutPair m).1 < C.right m := by
        rw [hmeet, ← hr]
        exact (hpieces (K.cutPair m).2).1
      exact hri.2.trans_lt (hcut.trans (hg.1 m).2.2)
  · constructor
    · have hcut : C.left m < K.physicalLeft (K.cutPair m).2 := by
        rw [← hmeet, ← hl]
        exact (hpieces (K.cutPair m).1).1
      exact ((hg.1 m).1.trans hcut).trans_le hri.1
    · rw [hr] at hri
      exact hri.2.trans_lt (hg.1 m).2.2

/-- The actual N04 reference null coordinate is its root-circle value
transported by the actual optical integral.  The sign is constant on the
whole piece and is not assumed as an extra chart property. -/
theorem n06_negative_reference_null_transport
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {m : ℕ} (hm : K.positive m = false)
    (hinside : Icc (K.physicalLeft m) (K.physicalRight m) ⊆ radialCore D)
    {σ : ℝ} (hσ : σ ^ 2 = 1) :
    ∃ τ : ℝ, τ ^ 2 = 1 ∧
      ∀ r ∈ Icc (K.physicalLeft m) (K.physicalRight m),
      ∀ s ∈ Icc (K.physicalLeft m) (K.physicalRight m), ∀ θ : ℝ,
        n05NullCoordinate (K.chart (C.referenceState, 0) m) σ (r, θ) =
          n05NullCoordinate (K.chart (C.referenceState, 0) m) σ
            (s, θ + τ * opticalTravel D.w s r) := by
  let Ψ : PolarPoint → PolarPoint := K.chart (C.referenceState, 0) m
  let N : PolarPoint → ℝ := n05NullCoordinate Ψ σ
  let a := K.physicalLeft m
  let b := K.physicalRight m
  have h01 := h.1.1.1
  obtain ⟨B, hB⟩ := h01.1.1
  have hw : ContDiff ℝ ∞ D.w := hB.1.2.2.1.1
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  have hA := h.2.2.2.2.1.1
  have hpieces := hA.referenceBounds
  have hnegative := hA.referenceNegative
  have hab : a < b := (hpieces m).1
  have hpos (r : ℝ) (hr : r ∈ Icc a b) : 0 < D.w r :=
    hB.1.2.2.2.2.1 r (hinside hr)
  have hrad (r : ℝ) (hr : r ∈ Icc a b) : 0 < r :=
    hB.1.1.trans (hinside hr).1
  have hv : ContinuousOn (opticalSpeed D.w) (Icc a b) :=
    continuousOn_opticalSpeed_of_profile hw (hrad a ⟨le_rfl, hab.le⟩) hpos
  have hΨ (p : PolarPoint) (hp : p.1 ∈ Icc a b) : ContDiffAt ℝ ∞ Ψ p :=
    (n05_reference_boundary_regular hA href hsector m (p := p) hp).1
  have hNc : ContinuousOn N (Icc a b ×ˢ (univ : Set ℝ)) := by
    intro p hp
    have hc := (hΨ p hp.1).continuousAt
    exact (hc.snd.add (continuousAt_const.mul
      (n05TricomiTime_continuous.continuousAt.comp hc.fst))).continuousWithinAt
  have hNs (p : PolarPoint) (hp : p.1 ∈ Ioo a b) : ContDiffAt ℝ ∞ N p := by
    have hpclosed : p.1 ∈ Icc a b := ⟨hp.1.le, hp.2.le⟩
    exact n05NullCoordinate_contDiffAt (hΨ p hpclosed)
      (n05_negative_reference_radius_pos hT hS h hm hpclosed
        ⟨hinside hpclosed, mem_univ _⟩ (hnegative m hm p.1 hp)) σ
  have hvpos (p : PolarPoint) (hp : p.1 ∈ Ioo a b) : 0 < opticalSpeed D.w p.1 := by
    exact Real.sqrt_pos.mpr (div_pos (neg_pos.mpr (hnegative m hm p.1 hp))
      (mul_pos (hrad p.1 ⟨hp.1.le, hp.2.le⟩) (hpos p.1 ⟨hp.1.le, hp.2.le⟩)))
  have hsquare (p : PolarPoint) (hp : p.1 ∈ Ioo a b) :
      radialPartial N p ^ 2 = (opticalSpeed D.w p.1 * angularPartial N p) ^ 2 := by
    have ha := hpos p.1 ⟨hp.1.le, hp.2.le⟩
    have hr := hrad p.1 ⟨hp.1.le, hp.2.le⟩
    have hn := (n05_negative_reference_null_identities hT hS h hm
      (x := p) ⟨hp, mem_univ _⟩ hσ).1
    change D.w p.1 * radialPartial N p ^ 2 +
      (deriv D.w p.1 / p.1) * angularPartial N p ^ 2 = 0 at hn
    have hsq : opticalSpeed D.w p.1 ^ 2 = -deriv D.w p.1 / (p.1 * D.w p.1) :=
      Real.sq_sqrt (div_nonneg (neg_nonneg.mpr (hnegative m hm p.1 hp).le)
        (mul_pos hr ha).le)
    have hcoef : D.w p.1 * opticalSpeed D.w p.1 ^ 2 = -deriv D.w p.1 / p.1 := by
      rw [hsq]
      field_simp [ha.ne', hr.ne']
    apply mul_left_cancel₀ ha.ne'
    rw [mul_pow, ← mul_assoc, hcoef, neg_div, neg_mul]
    linarith only [hn]
  obtain ⟨τ, hτ, heq⟩ := n06_null_derivatives_signed
    (fun p hp => (contDiffAt_radialPartial (hNs p hp.1) (m := 0)
      (by simp)).continuousAt.continuousWithinAt)
    (fun p hp => (contDiffAt_angularPartial (hNs p hp.1) (m := 0)
      (by simp)).continuousAt.continuousWithinAt)
    ((hv.mono Ioo_subset_Icc_self).comp continuous_fst.continuousOn (fun _ hp => hp.1))
    (fun p hp => mul_ne_zero (hvpos p hp).ne'
      (n05_negative_reference_null_angular_ne_zero hT hS h hm
        (x := p) ⟨hp, mem_univ _⟩ hσ)) hsquare
  refine ⟨τ, hτ, ?_⟩
  intro r hr s hs θ
  exact n06_strip_radial_transport hab hNc
    (fun p hp => (hNs p hp).differentiableAt (by simp)) hv heq hr hs θ

end ContinuousFlexibility.Statements
