import ContinuousFlexibility.Radial.InnerLiouvilleUnitSolution
import ContinuousFlexibility.Radial.InnerLiouvillePoissonEquation
import ContinuousFlexibility.Radial.InnerLiouvilleConormal
import ContinuousFlexibility.Radial.InnerModelFluxError

/-!
# The actual model weak flux is the same physical compression matrix

The affine-hat residual of the genuine transported unit column is its
classical outward conormal. The density drift is kept in the diagonal
kappa, so the remaining matrix is exactly the physical flux error of
the original localized R09 construction.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff InnerProductSpace

variable (D : ReferenceData) {B : BufferData} (hB : BufferHypotheses B)
  {C K : ℝ} (M : InnerBufferLocalizedData B C K)
  {R s : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam)
  (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc B.l B.h, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R B.l) (R B.h) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc B.l B.h, D.w (R x) = lam * s x ^ 2 * deriv R x)
  (U : ℝ) (hU : 0 ≤ U)
  (hv : ∀ x ∈ Icc B.l B.h, |deriv R x / R x| ≤ U)
  (hDw : ContDiff ℝ ∞ D.w) (j : ℝ)
  (hcoeff : ∀ x ∈ Ioo B.l B.h,
    B.potential x = liouvilleV0 s x - j ^ 2 * liouvilleRho R s x)

include hcoeff in
theorem innerLiouvilleLocalizedUnit_affineFlux (i k : Fin 2)
    (potential : RadialModeL2 D)
    (hpotential : InnerRadialPotentialClass D j (R B.l) (R B.h)
      (innerLiouvilleUnitPoissonPair D hB.1.le hlam hR hs hp hcore hw U hU hv
        (bufferCut B i) (M.column i).field (M.column i).scalar).1 potential) :
    let P := innerLiouvilleUnitPoissonPair D hB.1.le hlam hR hs hp hcore hw U hU hv
      (bufferCut B i) (M.column i).field (M.column i).scalar
    let grad := (Real.sqrt lam * s (bufferCut B i)) •
      innerLiouvilleGradientLift D hB.1.le hlam hR hs hp hcore hw
        ((M.column i).field, innerBufferLocalizedDerivative M i)
    let hpos := innerLiouville_radial_weight_pos_closed D hB.1.le hlam hR hp hw
    innerRadialWeakResidual D (P.1, grad) potential 0
      (innerLiouvilleColumnLift D hB.1.le hlam hR hs hp hcore hw B.border) P.2
      (innerRadialAffineUnitPair D hDw.continuous
        (hp B.l (left_mem_Icc.mpr hB.1.le)).1 hcore hpos k) =
      (if k = i then innerLiouvilleBoundaryKappa lam s (bufferCut B)
        (fun l => (M.column l).inwardEnergy) k else 0) +
          M.physicalFluxError lam (fun l => s (bufferCut B l)) k i := by
  let P := innerLiouvilleUnitPoissonPair D hB.1.le hlam hR hs hp hcore hw U hU hv
    (bufferCut B i) (M.column i).field (M.column i).scalar
  let grad := (Real.sqrt lam * s (bufferCut B i)) •
    innerLiouvilleGradientLift D hB.1.le hlam hR hs hp hcore hw
      ((M.column i).field, innerBufferLocalizedDerivative M i)
  let hpos := innerLiouville_radial_weight_pos_closed D hB.1.le hlam hR hp hw
  obtain ⟨u, hnear, hreg, hvalue, hgrad, _htrace⟩ :=
    innerLiouvilleLocalizedUnit_representative D hB M hlam hR hs hp hcore hw U hU hv i
  have hsource := innerLiouvilleUnitPoisson_effectiveSource_ae D hB.1.le hlam hR hs hp
    hcore hw hDw j (bufferCut B i) (M.column i).scalar B.border
      (M.column i).p_regular hreg hnear hcoeff (M.column i).equation
      (innerBuffer_border_indicator hB)
  have hscalar : P.2 = Real.sqrt lam * s (bufferCut B i) * (M.column i).scalar := by
    rw [innerLiouvilleUnitPoissonPair_apply]
  rw [← hscalar] at hsource
  have hm := morseCell_strictMonoOn hR (fun x hx => (hp x hx).2.1)
  have hrange : R B.l < R B.h :=
    hm (left_mem_Icc.mpr hB.1.le) (right_mem_Icc.mpr hB.1.le) hB.1
  have hflux := innerRadialWeakResidual_affineUnit D hDw hrange
    (hp B.l (left_mem_Icc.mpr hB.1.le)).1 hcore hpos hreg P.2
      (Q := (P.1, grad)) hvalue hgrad hpotential hsource k
  have hk : bufferCut B k ∈ Icc B.l B.h := by
    unfold bufferCut
    split_ifs
    · exact left_mem_Icc.mpr hB.1.le
    · exact right_mem_Icc.mpr hB.1.le
  have hRk : R (bufferCut B k) ∈ Icc (R B.l) (R B.h) :=
    ⟨hm.monotoneOn (left_mem_Icc.mpr hB.1.le) hk hk.1,
      hm.monotoneOn hk (right_mem_Icc.mpr hB.1.le) hk.2⟩
  have hclassical := innerLiouvilleUnitPoisson_flux
    (hR.differentiable (by simp) (bufferCut B k))
    (hs.differentiable (by simp) (bufferCut B k))
    (((M.column i).p_regular (bufferCut B k) hk).differentiableAt (by simp))
    ((hreg (R (bufferCut B k)) hRk).differentiableAt (by simp))
    (hp (bufferCut B k) hk).2.2.ne' (hw (bufferCut B k) hk)
    (hnear (bufferCut B k) hk)
  have hcut : (if k = 0 then R B.l else R B.h) = R (bufferCut B k) := by
    by_cases hk0 : k = 0 <;> simp only [bufferCut, hk0, ite_true, ite_false]
  dsimp only
  rw [hflux, hcut, hclassical, (M.column i).trace k]
  unfold InnerBufferLocalizedData.physicalFluxError InnerBufferLocalizedData.modelFluxError
  simp only [Matrix.of_apply]
  by_cases hki : k = i
  · subst i
    simp only [if_pos rfl, mul_one, innerLiouvilleBoundaryKappa, innerLiouvilleBoundaryDrift]
    field_simp [(hp (bufferCut B k) hk).2.2.ne']
    <;> ring
  · simp only [if_neg hki, if_neg (Ne.symm hki), mul_zero, sub_zero, zero_add]
    ring

include hcoeff in
/-- The actual unit solution, with its full outgoing physical flux.
The same field/scalar pair appears in the Poisson norm estimates. -/
theorem innerLiouvilleLocalizedUnit_flux_solution (i : Fin 2) :
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
      (∀ T ∈ innerRadialH1Zero D (R B.l) (R B.h),
        innerRadialWeakResidual D (P.1, grad) potential 0
          (innerLiouvilleColumnLift D hB.1.le hlam hR hs hp hcore hw B.border) P.2 T = 0) ∧
      ∀ k : Fin 2,
        innerRadialWeakResidual D (P.1, grad) potential 0
          (innerLiouvilleColumnLift D hB.1.le hlam hR hs hp hcore hw B.border) P.2
          (innerRadialAffineUnitPair D hDw.continuous
            (hp B.l (left_mem_Icc.mpr hB.1.le)).1 hcore hpos k) =
          (if k = i then innerLiouvilleBoundaryKappa lam s (bufferCut B)
            (fun l => (M.column l).inwardEnergy) k else 0) +
              M.physicalFluxError lam (fun l => s (bufferCut B l)) k i := by
  obtain ⟨potential, hdomain, htrace, hpotential, hrow, hweak⟩ :=
    innerLiouvilleLocalizedUnit_gradient_solution D hB M hlam hR hs hp hcore hw U hU hv
      hDw j hcoeff i
  refine ⟨(Real.sqrt lam * s (bufferCut B i)) •
      innerLiouvilleGradientLift D hB.1.le hlam hR hs hp hcore hw
        ((M.column i).field, innerBufferLocalizedDerivative M i),
    potential, hdomain, htrace, hpotential, hrow, hweak, ?_⟩
  intro k
  exact innerLiouvilleLocalizedUnit_affineFlux D hB M hlam hR hs hp hcore hw U hU hv
    hDw j hcoeff i k potential hpotential

end ContinuousFlexibility.Radial
