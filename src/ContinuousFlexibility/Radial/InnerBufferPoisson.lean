import ContinuousFlexibility.Radial.InnerPoissonCutoff
import ContinuousFlexibility.Radial.PositiveBufferGeometry
import Mathlib.Analysis.Convex.Segment

/-!
# The cutoff of an actual R09 buffer Poisson column

The coordinate is the existing positiveBufferPoint: its wall is at
t = action + 6. The cutoff changes only between action + 3 and
action + 4, hence at distances between 2 / mass and 3 / mass before
the wall. Both endpoints use this same construction.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

def innerBufferCutoff (B : BufferData) (i : Fin 2) (x : ℝ) : ℝ :=
  smoothTransition (B.action i + 4 + B.mass i * bufferSign i * (x - bufferCut B i))

theorem innerBufferCutoff_contDiff (B : BufferData) (i : Fin 2) :
    ContDiff ℝ ∞ (innerBufferCutoff B i) := by
  have h : ContDiff ℝ ∞ (fun x : ℝ =>
      B.action i + 4 + B.mass i * bufferSign i * (x - bufferCut B i)) :=
    contDiff_const.add (contDiff_const.mul (contDiff_id.sub contDiff_const))
  exact smoothTransition.contDiff.comp h

theorem innerBufferCutoff_nonneg (B : BufferData) (i : Fin 2) (x : ℝ) :
    0 ≤ innerBufferCutoff B i x := smoothTransition.nonneg _

theorem innerBufferCutoff_le_one (B : BufferData) (i : Fin 2) (x : ℝ) :
    innerBufferCutoff B i x ≤ 1 := smoothTransition.le_one _

theorem innerBufferPoint_coordinate {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) (x : ℝ) :
    positiveBufferPoint B i (B.mass i * bufferSign i * (bufferCut B i - x)) = x := by
  have hm : B.mass i ≠ 0 := (buffer_mass_pos hB i).ne'
  calc
    positiveBufferPoint B i (B.mass i * bufferSign i * (bufferCut B i - x)) =
        bufferCut B i - bufferSign i ^ 2 * (bufferCut B i - x) := by
      dsimp only [positiveBufferPoint]
      field_simp [hm]
      ring
    _ = x := by rw [bufferSign_sq]; ring

theorem innerBufferCutoff_point {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) (t : ℝ) :
    innerBufferCutoff B i (positiveBufferPoint B i t) =
      smoothTransition (B.action i + 4 - t) := by
  have hm : B.mass i ≠ 0 := (buffer_mass_pos hB i).ne'
  apply congrArg smoothTransition
  calc
    B.action i + 4 + B.mass i * bufferSign i *
        (positiveBufferPoint B i t - bufferCut B i) =
      B.action i + 4 - bufferSign i ^ 2 * t := by
        dsimp only [positiveBufferPoint]
        field_simp [hm]
        ring
    _ = B.action i + 4 - t := by rw [bufferSign_sq, one_mul]

theorem innerBufferCutoff_cut {B : BufferData} (hB : BufferHypotheses B) (i : Fin 2) :
    innerBufferCutoff B i (bufferCut B i) = 1 := by
  have hA := buffer_action_pos hB i
  apply smoothTransition.one_of_one_le
  dsimp only
  nlinarith

private theorem innerBuffer_cut_wall_gap {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) :
    bufferSign i * (bufferCut B i - bufferInnerWall B i) =
      (B.action i + 6) / B.mass i := by
  calc
    bufferSign i * (bufferCut B i - bufferInnerWall B i) =
        bufferSign i ^ 2 * ((B.action i + 6) / B.mass i) := by
      dsimp only [bufferInnerWall]
      ring
    _ = (B.action i + 6) / B.mass i := by rw [bufferSign_sq, one_mul]

theorem innerBuffer_cut_ne_wall {B : BufferData} (hB : BufferHypotheses B) (i : Fin 2) :
    bufferCut B i ≠ bufferInnerWall B i := by
  have hA := buffer_action_pos hB i
  have hpos : 0 < (B.action i + 6) / B.mass i :=
    div_pos (by linarith) (buffer_mass_pos hB i)
  intro he
  have h := innerBuffer_cut_wall_gap hB i
  rw [he, sub_self, mul_zero] at h
  linarith

theorem innerBuffer_walls_inside {B : BufferData} (hB : BufferHypotheses B) :
    B.l < bufferInnerWall B 0 ∧ bufferInnerWall B 0 < bufferInnerWall B 1 ∧
      bufferInnerWall B 1 < B.h := by
  have hpos (i : Fin 2) : 0 < bufferSign i * (bufferCut B i - bufferInnerWall B i) := by
    rw [innerBuffer_cut_wall_gap hB i]
    apply div_pos _ (buffer_mass_pos hB i)
    have hA := buffer_action_pos hB i
    linarith
  have hL := hpos 0
  have hR := hpos 1
  norm_num [bufferSign, bufferCut] at hL hR
  exact ⟨by linarith, hB.2.1, by linarith⟩

/-- Every strictly intermediate inward parameter lies in the same open
span, independently of the orientation of the endpoint. -/
theorem innerBufferPoint_mem_openSpan {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) {t : ℝ} (ht : 0 < t) (htw : t < B.action i + 6) :
    positiveBufferPoint B i t ∈ radialOpenSpan (bufferCut B i) (bufferInnerWall B i) := by
  have hA := buffer_action_pos hB i
  have hlen : 0 < B.action i + 6 := by linarith
  have hm : B.mass i ≠ 0 := (buffer_mass_pos hB i).ne'
  have hne := innerBuffer_cut_ne_wall hB i
  rw [radialOpenSpan, ← openSegment_eq_Ioo' hne, openSegment_eq_image]
  refine ⟨t / (B.action i + 6), ⟨div_pos ht hlen, (div_lt_one hlen).mpr htw⟩, ?_⟩
  simp only [smul_eq_mul]
  dsimp only [positiveBufferPoint, bufferInnerWall]
  field_simp [hm, hlen.ne']
  ring

theorem innerBuffer_openSpan_subset_retained {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) :
    radialOpenSpan (bufferCut B i) (bufferInnerWall B i) ⊆ Ioo B.l B.h := by
  have hW := innerBuffer_walls_inside hB
  have hL : B.l < bufferInnerWall B 0 := hW.1
  have hR : bufferInnerWall B 1 < B.h := hW.2.2
  fin_cases i
  · have hsub : Ioo B.l (bufferInnerWall B 0) ⊆ Ioo B.l B.h :=
      Ioo_subset_Ioo le_rfl (hW.2.1.le.trans hR.le)
    simpa only [bufferCut, if_pos rfl, radialOpenSpan, min_eq_left hL.le,
      max_eq_right hL.le] using hsub
  · have hcut : bufferCut B (1 : Fin 2) = B.h := by norm_num [bufferCut]
    rw [hcut, radialOpenSpan, min_eq_right hR.le, max_eq_left hR.le]
    exact Ioo_subset_Ioo (hL.le.trans hW.2.1.le) le_rfl

theorem innerBufferCutoff_tsupport_bound {B : BufferData} (i : Fin 2) {x : ℝ}
    (hx : x ∈ tsupport (innerBufferCutoff B i)) :
    B.mass i * bufferSign i * (bufferCut B i - x) ≤ B.action i + 4 := by
  have hs : Function.support (innerBufferCutoff B i) ⊆
      {y : ℝ | B.mass i * bufferSign i * (bufferCut B i - y) ≤ B.action i + 4} := by
    intro y hy
    by_contra hn
    have hlt := lt_of_not_ge hn
    apply hy
    exact smoothTransition.zero_of_nonpos (by nlinarith)
  have hc : IsClosed {y : ℝ |
      B.mass i * bufferSign i * (bufferCut B i - y) ≤ B.action i + 4} :=
    isClosed_le (by fun_prop) continuous_const
  exact closure_minimal hs hc hx

theorem innerBufferCutoff_tsupport_retained {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) {x : ℝ} (hx : x ∈ Icc B.l B.h)
    (hs : x ∈ tsupport (innerBufferCutoff B i)) :
    x = bufferCut B i ∨ x ∈ radialOpenSpan (bufferCut B i) (bufferInnerWall B i) := by
  let t : ℝ := B.mass i * bufferSign i * (bufferCut B i - x)
  have ht : 0 ≤ t := by
    have hm := (buffer_mass_pos hB i).le
    have hL := hx.1
    have hR := hx.2
    fin_cases i <;> dsimp [t, bufferCut, bufferSign] <;> nlinarith
  have htw : t < B.action i + 6 := by
    have h := innerBufferCutoff_tsupport_bound i hs
    dsimp only [t]
    linarith
  rcases eq_or_lt_of_le ht with hz | hpos
  · left
    have h := innerBufferPoint_coordinate hB i x
    rw [show B.mass i * bufferSign i * (bufferCut B i - x) = 0 from hz.symm,
      positiveBufferPoint_zero] at h
    exact h.symm
  · right
    have h := innerBufferPoint_mem_openSpan hB i hpos htw
    rw [innerBufferPoint_coordinate hB i x] at h
    exact h

theorem innerBufferCut_not_mem_retained (B : BufferData) (i : Fin 2) :
    bufferCut B i ∉ Ioo B.l B.h := by
  fin_cases i <;> simp [bufferCut]

theorem innerBufferCutoff_boundary_values {B : BufferData} (hB : BufferHypotheses B)
    (i j : Fin 2) :
    innerBufferCutoff B i (bufferCut B j) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, innerBufferCutoff_cut hB i]
  · rw [if_neg hij]
    by_contra hne
    have hmem : bufferCut B j ∈ Icc B.l B.h := by
      fin_cases j <;> simp [bufferCut, hB.1.le]
    have hs : bufferCut B j ∈ tsupport (innerBufferCutoff B i) := subset_closure hne
    rcases innerBufferCutoff_tsupport_retained hB i hmem hs with he | he
    · have hab := hB.1
      fin_cases i <;> fin_cases j <;> norm_num [bufferCut] at hij he ⊢ <;> linarith
    · exact innerBufferCut_not_mem_retained B j
        (innerBuffer_openSpan_subset_retained hB i he)

/-- The actual temporary border and the buffer cutoff have disjoint support. -/
theorem innerBufferCutoff_border_disjoint {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) :
    Disjoint (Function.support B.borderFunction) (Function.support (innerBufferCutoff B i)) := by
  apply Set.disjoint_left.mpr
  intro x hcolumn hcutoff
  have ht := innerBufferCutoff_tsupport_bound i (subset_closure hcutoff)
  have hzero := positiveBufferPoint_border_eq_zero hB i
    (t := B.mass i * bufferSign i * (bufferCut B i - x)) (by linarith)
  rw [innerBufferPoint_coordinate hB i x] at hzero
  exact hcolumn hzero

/-- The actual C² buffer minimizer is smooth in the open buffer, by its
homogeneous equation and the smoothness of the same potential. -/
theorem innerBufferPin_contDiffOn {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) {pin : ℝ → ℝ}
    (hpin : ContDiffOn ℝ 2 pin (uIcc (bufferCut B i) (bufferInnerWall B i)))
    (heq : ∀ x ∈ radialOpenSpan (bufferCut B i) (bufferInnerWall B i),
      -deriv (deriv pin) x + B.potential x * pin x = 0) :
    ContDiffOn ℝ ∞ pin (radialOpenSpan (bufferCut B i) (bufferInnerWall B i)) := by
  have hV : ContDiff ℝ ∞ B.potential := hB.2.2.2.2.1
  apply innerPoisson_contDiffOn_of_secondOrder
    (show IsOpen (radialOpenSpan (bufferCut B i) (bufferInnerWall B i)) from isOpen_Ioo)
    hV.contDiffOn
    (hpin.mono (show radialOpenSpan (bufferCut B i) (bufferInnerWall B i) ⊆
      uIcc (bufferCut B i) (bufferInnerWall B i) from Ioo_subset_Icc_self))
  intro x hx
  linarith [heq x hx]

/-- Only the actual cut germ and the open buffer are needed on the closed
support of the cutoff; no smooth extension across the inner wall is assumed. -/
theorem innerBufferPin_contDiffAt_on_cutoff {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {pin : ℝ → ℝ}
    (hpin : ContDiffOn ℝ 2 pin (uIcc (bufferCut B i) (bufferInnerWall B i)))
    (hcut : ContDiffAt ℝ ∞ pin (bufferCut B i))
    (heq : ∀ x ∈ radialOpenSpan (bufferCut B i) (bufferInnerWall B i),
      -deriv (deriv pin) x + B.potential x * pin x = 0) :
    ∀ x ∈ Icc B.l B.h, x ∈ tsupport (innerBufferCutoff B i) →
      ContDiffAt ℝ ∞ pin x := by
  have hsmooth := innerBufferPin_contDiffOn hB i hpin heq
  intro x hx hs
  rcases innerBufferCutoff_tsupport_retained hB i hx hs with hxc | hxi
  · simpa only [hxc] using hcut
  · exact hsmooth.contDiffAt (isOpen_Ioo.mem_nhds hxi)

theorem innerBufferPin_equation_on_cutoff {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {pin : ℝ → ℝ}
    (heq : ∀ x ∈ radialOpenSpan (bufferCut B i) (bufferInnerWall B i),
      -deriv (deriv pin) x + B.potential x * pin x = 0) :
    ∀ x ∈ Ioo B.l B.h, x ∈ tsupport (innerBufferCutoff B i) →
      -deriv (deriv pin) x + B.potential x * pin x = 0 := by
  intro x hx hs
  rcases innerBufferCutoff_tsupport_retained hB i (Ioo_subset_Icc_self hx) hs with
      hxc | hxi
  · rw [hxc] at hx
    exact (innerBufferCut_not_mem_retained B i hx).elim
  · exact heq x hxi

/-- The actual R09 Poisson column splits into its localized buffer lift and
the correction by the same Dirichlet inverse. Both L and f are constructed
as genuine L² classes. The single temporary scalar border is retained;
the unbordered row is exactly scalar = 0 from R09. -/
theorem innerBufferPoisson_cutoff_decomposition {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2)
    (G : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ))
    {pin p : ℝ → ℝ} {P : RadialL2} {scalar : ℝ}
    (hpin : ContDiffOn ℝ 2 pin (uIcc (bufferCut B i) (bufferInnerWall B i)))
    (hpinCut : ContDiffAt ℝ ∞ pin (bufferCut B i))
    (hpinValue : pin (bufferCut B i) = 1)
    (hpinEq : ∀ x ∈ radialOpenSpan (bufferCut B i) (bufferInnerWall B i),
      -deriv (deriv pin) x + B.potential x * pin x = 0)
    (hpLeft : ContDiffAt ℝ ∞ p B.l) (hpRight : ContDiffAt ℝ ∞ p B.h)
    (hpInside : ContDiffOn ℝ ∞ p (Ioo B.l B.h))
    (hPInside : (P : ℝ → ℝ) =ᵐ[volume.restrict (Ioo B.l B.h)] p)
    (hPOutside : (P : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo B.l B.h)ᶜ)] (fun _ => 0))
    (hrow : if B.bordered then ⟪B.border, P⟫_ℝ = 0 else scalar = 0)
    (hpEq : ∀ x ∈ Ioo B.l B.h,
      -deriv (deriv p) x + B.potential x * p x + scalar * B.borderFunction x = 0)
    (hpTrace : ∀ j, p (bufferCut B j) = if i = j then 1 else 0)
    (hunique : ∀ U F : RadialL2 × ℝ,
      BorderedIntervalGraph B.potential B.border B.bordered B.l B.h U F → G F = U) :
    ∃ L f : RadialL2,
      ((L : ℝ → ℝ) =ᵐ[volume]
        (Ioo B.l B.h).indicator (fun x => innerBufferCutoff B i x * pin x)) ∧
      ((f : ℝ → ℝ) =ᵐ[volume] (Ioo B.l B.h).indicator (fun x =>
        -deriv (deriv (innerBufferCutoff B i)) x * pin x -
          2 * deriv (innerBufferCutoff B i) x * deriv pin x)) ∧
      (P, scalar) = (L, 0) - G (f, 0) := by
  have hV : ContDiff ℝ ∞ B.potential := hB.2.2.2.2.1
  have hχ := innerBufferCutoff_contDiff B i
  have hpinSupport := innerBufferPin_contDiffAt_on_cutoff hB i hpin hpinCut hpinEq
  have hpinSupportEq := innerBufferPin_equation_on_cutoff hB i hpinEq
  let lift : ℝ → ℝ := fun x => innerBufferCutoff B i x * pin x
  have hlift : ∀ x ∈ Icc B.l B.h, ContDiffAt ℝ ∞ lift x :=
    innerPoisson_cutoff_smooth hχ hpinSupport
  have hliftCont : ContinuousOn lift (Icc B.l B.h) :=
    fun x hx => (hlift x hx).continuousAt.continuousWithinAt
  have hLmem := innerDirichlet_indicator_memLp hliftCont
  let L : RadialL2 := hLmem.toLp ((Ioo B.l B.h).indicator lift)
  have hL : (L : ℝ → ℝ) =ᵐ[volume] (Ioo B.l B.h).indicator lift :=
    MemLp.coeFn_toLp hLmem
  have hd : ∀ x ∈ Icc B.l B.h, ContDiffAt ℝ ∞ (deriv lift) x :=
    fun x hx => (hlift x hx).derivWithin (m := ∞) (by simp)
  have hsourceCont : ContinuousOn
      (fun x => -deriv (deriv lift) x + B.potential x * lift x) (Icc B.l B.h) :=
    (innerDirichlet_deriv_continuousOn hd).neg.add
      (hV.continuous.continuousOn.mul hliftCont)
  have hFmem := innerDirichlet_indicator_memLp hsourceCont
  let f : RadialL2 := hFmem.toLp ((Ioo B.l B.h).indicator
    (fun x => -deriv (deriv lift) x + B.potential x * lift x))
  have hfRaw : (f : ℝ → ℝ) =ᵐ[volume] (Ioo B.l B.h).indicator
      (fun x => -deriv (deriv lift) x + B.potential x * lift x) :=
    MemLp.coeFn_toLp hFmem
  have hf : (f : ℝ → ℝ) =ᵐ[volume] (Ioo B.l B.h).indicator (fun x =>
      -deriv (deriv (innerBufferCutoff B i)) x * pin x -
        2 * deriv (innerBufferCutoff B i) x * deriv pin x) := by
    have hformula := innerPoisson_cutoff_expression hχ hpinSupport hpinSupportEq
    filter_upwards [hfRaw] with x hfx
    rw [hfx]
    by_cases hx : x ∈ Ioo B.l B.h
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      exact hformula x hx
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  have hboundary (j : Fin 2) :
      innerBufferCutoff B i (bufferCut B j) * pin (bufferCut B j) =
        p (bufferCut B j) := by
    rw [innerBufferCutoff_boundary_values hB i j, hpTrace j]
    by_cases hij : i = j
    · subst j
      simp only [if_pos rfl, one_mul, hpinValue]
    · rw [if_neg hij, zero_mul]
  have hleft : innerBufferCutoff B i B.l * pin B.l = p B.l := by
    simpa only [bufferCut, if_pos rfl] using hboundary 0
  have hright : innerBufferCutoff B i B.h * pin B.h = p B.h := by
    have hcut : bufferCut B (1 : Fin 2) = B.h := by norm_num [bufferCut]
    simpa only [hcut] using hboundary 1
  have hborder : (B.border : ℝ → ℝ) =ᵐ[volume]
      (Ioo B.l B.h).indicator B.borderFunction := by
    rcases hB with ⟨_, _, _, _, _, _, _, _, hg, _, _, hout, _, _, _⟩
    exact innerPoisson_eq_indicator (ae_restrict_of_ae hg) hout
  refine ⟨L, f, hL, hf, ?_⟩
  exact innerPoisson_cutoff_sub_dirichlet B.bordered G hB.1
    hV.continuous.continuousOn
    (innerPoisson_contDiff_closed hpLeft hpRight hpInside) hχ hpinSupport hpinSupportEq
    hleft hright hborder (innerPoisson_eq_indicator hPInside hPOutside) hL hf
    (innerBufferCutoff_border_disjoint hB i) hrow hpEq hunique

end ContinuousFlexibility.Radial
