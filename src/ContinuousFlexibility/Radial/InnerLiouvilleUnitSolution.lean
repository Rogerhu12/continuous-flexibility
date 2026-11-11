import ContinuousFlexibility.Radial.InnerLiouvilleH1Representative
import ContinuousFlexibility.Radial.InnerLiouvillePoissonWeak
import ContinuousFlexibility.Radial.InnerRadialSmoothUnitDomain
import ContinuousFlexibility.Radial.InnerBufferLocalizedConstruction

/-!
# Actual unit-trace solutions from the same localized model columns

The derivative class is formed from the original smooth R09 column.
Its physical value and scalar are exactly the existing unit Poisson
pair. Both endpoints use the same construction and the same physical
domain, signed potential, scalar row and closed weak equation.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff InnerProductSpace

def innerBufferLocalizedDerivative {B : BufferData} {C K : ℝ}
    (M : InnerBufferLocalizedData B C K) (i : Fin 2) : RadialL2 :=
  (innerDirichlet_indicator_memLp
    (innerDirichlet_deriv_continuousOn (M.column i).p_regular)).toLp
      ((Ioo B.l B.h).indicator (deriv (M.column i).p))

theorem innerBufferLocalizedDerivative_ae {B : BufferData} {C K : ℝ}
    (M : InnerBufferLocalizedData B C K) (i : Fin 2) :
    (innerBufferLocalizedDerivative M i : ℝ → ℝ) =ᵐ[volume]
      (Ioo B.l B.h).indicator (deriv (M.column i).p) :=
  MemLp.coeFn_toLp _

theorem innerBuffer_border_indicator {B : BufferData} (hB : BufferHypotheses B) :
    (B.border : ℝ → ℝ) =ᵐ[volume] (Ioo B.l B.h).indicator B.borderFunction := by
  have hglobal : (B.border : ℝ → ℝ) =ᵐ[volume] B.borderFunction := by
    rcases hB with ⟨_, _, _, _, _, _, _, _, hg, _⟩
    exact hg
  have hout : (B.border : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo B.l B.h)ᶜ)] (fun _ => 0) := by
    rcases hB with ⟨_, _, _, _, _, _, _, _, _, _, _, hg, _⟩
    exact hg
  filter_upwards [hglobal, ae_imp_of_ae_restrict hout] with x hx ho
  by_cases hxi : x ∈ Ioo B.l B.h
  · rw [indicator_of_mem hxi, hx]
  · rw [indicator_of_notMem hxi]
    exact ho hxi

variable (D : ReferenceData) {B : BufferData} (hB : BufferHypotheses B)
  {C K : ℝ} (M : InnerBufferLocalizedData B C K)
  {R s : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam)
  (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc B.l B.h, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R B.l) (R B.h) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc B.l B.h, D.w (R x) = lam * s x ^ 2 * deriv R x)
  (U : ℝ) (hU : 0 ≤ U)
  (hv : ∀ x ∈ Icc B.l B.h, |deriv R x / R x| ≤ U)

theorem innerLiouvilleLocalizedUnit_representative (i : Fin 2) :
    ∃ u : ℝ → ℝ,
      (∀ x ∈ Icc B.l B.h, (fun y => u (R y)) =ᶠ[𝓝 x]
        (fun y => s (bufferCut B i) * (M.column i).p y / s y)) ∧
      (∀ r ∈ Icc (R B.l) (R B.h), ContDiffAt ℝ ∞ u r) ∧
      ((innerLiouvilleUnitPoissonPair D hB.1.le hlam hR hs hp hcore hw U hU hv
          (bufferCut B i) (M.column i).field (M.column i).scalar).1 : ℝ → ℝ)
        =ᵐ[radialHilbertMeasure D] (Ioo (R B.l) (R B.h)).indicator u ∧
      (((Real.sqrt lam * s (bufferCut B i)) •
          innerLiouvilleGradientLift D hB.1.le hlam hR hs hp hcore hw
            ((M.column i).field, innerBufferLocalizedDerivative M i) : RadialModeL2 D) : ℝ → ℝ)
        =ᵐ[radialHilbertMeasure D]
          (Ioo (R B.l) (R B.h)).indicator (innerGapGradientField u) ∧
      ∀ k, u (R (bufferCut B k)) = innerEndpointValues i k := by
  have hfield : ((M.column i).field : ℝ → ℝ) =ᵐ[volume.restrict (Ioo B.l B.h)]
      (M.column i).p := by
    filter_upwards [ae_restrict_of_ae (M.column i).field_ae,
      ae_restrict_mem measurableSet_Ioo] with x hx hxi
    simpa only [indicator_of_mem hxi] using hx
  have hderivative : (innerBufferLocalizedDerivative M i : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioo B.l B.h)] deriv (M.column i).p := by
    filter_upwards [ae_restrict_of_ae (innerBufferLocalizedDerivative_ae M i),
      ae_restrict_mem measurableSet_Ioo] with x hx hxi
    simpa only [indicator_of_mem hxi] using hx
  obtain ⟨u, hnear, hreg, hvalue, hgrad⟩ :=
    exists_innerLiouvilleScaledH1Representative D hB.1.le hlam hR hs hp hcore hw U hU hv
      (Real.sqrt lam * s (bufferCut B i)) (M.column i).field
      (innerBufferLocalizedDerivative M i) (M.column i).p (M.column i).p_regular
      hfield hderivative
  have hformula (x : ℝ) (hx : x ∈ Icc B.l B.h) :
      (fun y => u (R y)) =ᶠ[𝓝 x]
        (fun y => s (bufferCut B i) * (M.column i).p y / s y) := by
    have hsp : ∀ᶠ y in 𝓝 x, 0 < s y :=
      hs.continuous.continuousAt.eventually (lt_mem_nhds (hp x hx).2.2)
    filter_upwards [hnear x hx, hsp] with y hy hsy
    rw [hy]
    field_simp [(Real.sqrt_pos.mpr hlam).ne', hsy.ne']
    <;> ring
  refine ⟨u, hformula, hreg, ?_, hgrad, ?_⟩
  · rw [innerLiouvilleUnitPoissonPair_apply]
    exact hvalue
  · intro k
    have hk : bufferCut B k ∈ Icc B.l B.h := by
      unfold bufferCut
      split_ifs
      · exact left_mem_Icc.mpr hB.1.le
      · exact right_mem_Icc.mpr hB.1.le
    rw [(hformula (bufferCut B k) hk).eq_of_nhds, (M.column i).trace k]
    by_cases hik : i = k
    · subst k
      simp only [innerEndpointValues, ite_true, mul_one]
      exact div_self (hp (bufferCut B i) hk).2.2.ne'
    · simp only [innerEndpointValues, if_neg hik, mul_zero, zero_div]

variable (hDw : ContDiff ℝ ∞ D.w) (j : ℝ)
  (hcoeff : ∀ x ∈ Ioo B.l B.h,
    B.potential x = liouvilleV0 s x - j ^ 2 * liouvilleRho R s x)

include hcoeff in
theorem innerLiouvilleLocalizedUnit_gradient_solution (i : Fin 2) :
    let P := innerLiouvilleUnitPoissonPair D hB.1.le hlam hR hs hp hcore hw U hU hv
      (bufferCut B i) (M.column i).field (M.column i).scalar
    let grad := (Real.sqrt lam * s (bufferCut B i)) •
      innerLiouvilleGradientLift D hB.1.le hlam hR hs hp hcore hw
        ((M.column i).field, innerBufferLocalizedDerivative M i)
    let hpos := innerLiouville_radial_weight_pos_closed D hB.1.le hlam hR hp hw
    ∃ potential : RadialModeL2 D,
      (P.1, grad) ∈ innerRadialH1Domain D hDw.continuous
        (hp B.l (left_mem_Icc.mpr hB.1.le)).1 hcore hpos ∧
      innerRadialH1Trace D hDw.continuous
        (hp B.l (left_mem_Icc.mpr hB.1.le)).1 hcore hpos (P.1, grad) =
          innerEndpointValues i ∧
      InnerRadialPotentialClass D j (R B.l) (R B.h) P.1 potential ∧
      (if B.bordered then
        ⟪innerLiouvilleColumnLift D hB.1.le hlam hR hs hp hcore hw B.border, P.1⟫_ℝ = 0
       else P.2 = 0) ∧
      ∀ T ∈ innerRadialH1Zero D (R B.l) (R B.h),
        innerRadialWeakResidual D (P.1, grad) potential 0
          (innerLiouvilleColumnLift D hB.1.le hlam hR hs hp hcore hw B.border) P.2 T = 0 := by
  let c : ℝ := Real.sqrt lam * s (bufferCut B i)
  let f := innerLiouvilleFieldLift D hB.1.le hlam hR hs hp hcore hw U hU hv (M.column i).field
  let d := innerLiouvilleGradientLift D hB.1.le hlam hR hs hp hcore hw
    ((M.column i).field, innerBufferLocalizedDerivative M i)
  let hpos := innerLiouville_radial_weight_pos_closed D hB.1.le hlam hR hp hw
  let v := innerRadialPotentialMultiplier D hDw j hpos f
  have hpot : InnerRadialPotentialClass D j (R B.l) (R B.h) f v :=
    innerRadialPotentialMultiplier_class D hDw j hpos f
  obtain ⟨u, _hnear, hreg, hvalue, hgrad, htrace⟩ :=
    innerLiouvilleLocalizedUnit_representative D hB M hlam hR hs hp hcore hw U hU hv i
  rw [innerLiouvilleUnitPoissonPair_apply] at hvalue
  have hrange : R B.l < R B.h :=
    (morseCell_strictMonoOn hR (fun x hx => (hp x hx).2.1))
      (left_mem_Icc.mpr hB.1.le) (right_mem_Icc.mpr hB.1.le) hB.1
  have hends := innerRadialH1Pair_unit_domain_trace D hDw.continuous hrange
    (hp B.l (left_mem_Icc.mpr hB.1.le)).1 hcore hpos hreg i
      (by simpa only [bufferCut, ite_true] using htrace 0)
      (by simpa only [bufferCut, show (1 : Fin 2) ≠ 0 by decide, ite_false] using htrace 1)
      (Q := (c • f, c • d)) hvalue hgrad
  dsimp only
  rw [innerLiouvilleUnitPoissonPair_apply]
  refine ⟨c • v, hends.1, hends.2, hpot.smul c, ?_, ?_⟩
  · have hborder : (B.border : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo B.l B.h)ᶜ)]
        (fun _ => 0) := by
      rcases hB with ⟨_, _, _, _, _, _, _, _, _, _, _, hb, _⟩
      exact hb
    have hrow := (M.column i).scalar_row
    by_cases hb : B.bordered = true
    ·
      simp only [hb, ite_true] at hrow ⊢
      rw [real_inner_smul_right, innerLiouvilleColumnLift_field_pairing D hB.1.le
        hlam hR hs hp hcore hw U hU hv B.border (M.column i).field hborder, hrow, mul_zero]
    · simp only [hb, ite_false] at hrow ⊢
      rw [hrow, mul_zero]
  · intro T hT
    have hV : Continuous B.potential := by
      rcases hB with ⟨_, _, _, _, hV, _⟩
      exact hV.continuous
    have he := innerLiouvillePoissonWeak_on_zeroDomain D hB.1 hlam hR hs hp hcore hw
      U hU hv hDw j hpos hV hcoeff (M.column i).scalar (M.column i).p_regular
      (innerBuffer_border_indicator hB) (M.column i).field_ae
      (innerBufferLocalizedDerivative_ae M i) (M.column i).equation hT
    have hscale := innerRadialWeakResidual_smul_solution D c (f, d) v 0
      (innerLiouvilleColumnLift D hB.1.le hlam hR hs hp hcore hw B.border)
      (M.column i).scalar T
    rw [he, mul_zero, smul_zero] at hscale
    simpa only [innerRadialWeakResidual_apply, Prod.smul_snd] using hscale

include hcoeff in
theorem innerLiouvilleLocalizedUnit_solution (i : Fin 2) :
    let P := innerLiouvilleUnitPoissonPair D hB.1.le hlam hR hs hp hcore hw U hU hv
      (bufferCut B i) (M.column i).field (M.column i).scalar
    let hpos := innerLiouville_radial_weight_pos_closed D hB.1.le hlam hR hp hw
    ∃ grad potential : RadialModeL2 D,
      (P.1, grad) ∈ innerRadialH1Domain D hDw.continuous
        (hp B.l (left_mem_Icc.mpr hB.1.le)).1 hcore hpos ∧
      innerRadialH1Trace D hDw.continuous
        (hp B.l (left_mem_Icc.mpr hB.1.le)).1 hcore hpos (P.1, grad) =
          innerEndpointValues i ∧
      InnerRadialPotentialClass D j (R B.l) (R B.h) P.1 potential ∧
      (if B.bordered then
        ⟪innerLiouvilleColumnLift D hB.1.le hlam hR hs hp hcore hw B.border, P.1⟫_ℝ = 0
       else P.2 = 0) ∧
      ∀ T ∈ innerRadialH1Zero D (R B.l) (R B.h),
        innerRadialWeakResidual D (P.1, grad) potential 0
          (innerLiouvilleColumnLift D hB.1.le hlam hR hs hp hcore hw B.border) P.2 T = 0 := by
  obtain ⟨potential, hdomain, htrace, hpotential, hrow, hweak⟩ :=
    innerLiouvilleLocalizedUnit_gradient_solution D hB M hlam hR hs hp hcore hw U hU hv
      hDw j hcoeff i
  exact ⟨(Real.sqrt lam * s (bufferCut B i)) •
      innerLiouvilleGradientLift D hB.1.le hlam hR hs hp hcore hw
        ((M.column i).field, innerBufferLocalizedDerivative M i),
    potential, hdomain, htrace, hpotential, hrow, hweak⟩

end ContinuousFlexibility.Radial
