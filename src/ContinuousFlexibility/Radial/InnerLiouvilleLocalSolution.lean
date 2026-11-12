import ContinuousFlexibility.Radial.InnerLiouvilleUnitSolution
import ContinuousFlexibility.Radial.InnerLiouvilleDirichletSolution

/-!
# The same model Dirichlet and Poisson maps solve every local trace problem

An arbitrary actual physical source and both endpoint values are
realized by the original localized Dirichlet inverse and the two
normalized columns. The field and scalar are exactly their linear
combination; the actual derivative, potential, domain, trace, row and
all closed-domain weak equations are proved for that same combination.
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
theorem innerLiouvilleLocalizedSolution
    (F : RadialModeL2 D × ℝ) (hscalar : B.bordered = false → F.2 = 0)
    (z : Fin 2 → ℝ) :
    let Z := innerLiouvillePhysicalDirichlet D hB.1.le hlam hR hs hp hcore hw
      U hU hv M.dirichlet F
    let P := fun i => innerLiouvilleUnitPoissonPair D hB.1.le hlam hR hs hp hcore hw
      U hU hv (bufferCut B i) (M.column i).field (M.column i).scalar
    let out := Z + (z 0 • P 0 + z 1 • P 1)
    let hpos := innerLiouville_radial_weight_pos_closed D hB.1.le hlam hR hp hw
    ∃ q : InnerRadialH1Pair D, ∃ potential : RadialModeL2 D,
      q.1 = out.1 ∧
      q ∈ innerRadialH1Domain D hDw.continuous
        (hp B.l (left_mem_Icc.mpr hB.1.le)).1 hcore hpos ∧
      innerRadialH1Trace D hDw.continuous
        (hp B.l (left_mem_Icc.mpr hB.1.le)).1 hcore hpos q = z ∧
      InnerRadialPotentialClass D j (R B.l) (R B.h) q.1 potential ∧
      (if B.bordered then
        ⟪innerLiouvilleColumnLift D hB.1.le hlam hR hs hp hcore hw B.border, q.1⟫_ℝ = F.2
       else out.2 = 0 ∧ F.2 = 0) ∧
      ∀ T ∈ innerRadialH1Zero D (R B.l) (R B.h),
        innerRadialWeakResidual D q potential F.1
          (innerLiouvilleColumnLift D hB.1.le hlam hR hs hp hcore hw B.border) out.2 T = 0 := by
  let Z := innerLiouvillePhysicalDirichlet D hB.1.le hlam hR hs hp hcore hw
    U hU hv M.dirichlet F
  let P : Fin 2 → RadialModeL2 D × ℝ := fun i =>
    innerLiouvilleUnitPoissonPair D hB.1.le hlam hR hs hp hcore hw
      U hU hv (bufferCut B i) (M.column i).field (M.column i).scalar
  let out := Z + (z 0 • P 0 + z 1 • P 1)
  let hpos := innerLiouville_radial_weight_pos_closed D hB.1.le hlam hR hp hw
  let col := innerLiouvilleColumnLift D hB.1.le hlam hR hs hp hcore hw B.border
  let dom := innerRadialH1Domain D hDw.continuous
    (hp B.l (left_mem_Icc.mpr hB.1.le)).1 hcore hpos
  let tr := innerRadialH1Trace D hDw.continuous
    (hp B.l (left_mem_Icc.mpr hB.1.le)).1 hcore hpos
  obtain ⟨dZ, vZ, hZzero, hZpot, hZrow, hZweak⟩ :=
    innerLiouvilleLocalizedDirichlet_solution D hB M hlam hR hs hp hcore hw U hU hv
      hDw j hcoeff F hscalar
  have hunit (i : Fin 2) := innerLiouvilleLocalizedUnit_solution D hB M hlam hR hs hp
    hcore hw U hU hv hDw j hcoeff i
  choose dP vP hPdom hPtrace hPpot hProw hPweak using hunit
  change (if B.bordered then ⟪col, Z.1⟫_ℝ = F.2 else Z.2 = 0 ∧ F.2 = 0) at hZrow
  change (∀ i, if B.bordered then ⟪col, (P i).1⟫_ℝ = 0 else (P i).2 = 0) at hProw
  let qZ : InnerRadialH1Pair D := (Z.1, dZ)
  let qP : Fin 2 → InnerRadialH1Pair D := fun i => ((P i).1, dP i)
  let q : InnerRadialH1Pair D := qZ + (z 0 • qP 0 + z 1 • qP 1)
  let v : RadialModeL2 D := vZ + (z 0 • vP 0 + z 1 • vP 1)
  have hrange : R B.l < R B.h :=
    (morseCell_strictMonoOn hR (fun x hx => (hp x hx).2.1))
      (left_mem_Icc.mpr hB.1.le) (right_mem_Icc.mpr hB.1.le) hB.1
  have hZdom : qZ ∈ dom := innerRadialH1Zero_mem_domain D hDw.continuous hrange
    (hp B.l (left_mem_Icc.mpr hB.1.le)).1 hcore hpos hZzero
  have hZtrace : tr qZ = 0 := innerRadialH1Trace_zero D hDw.continuous hrange
    (hp B.l (left_mem_Icc.mpr hB.1.le)).1 hcore hpos hZzero
  have hqdom : q ∈ dom :=
    dom.add_mem hZdom (dom.add_mem (dom.smul_mem (z 0) (hPdom 0))
      (dom.smul_mem (z 1) (hPdom 1)))
  have hqtrace : tr q = z := by
    rw [show q = qZ + (z 0 • qP 0 + z 1 • qP 1) from rfl,
      map_add, map_add, map_smul, map_smul, hZtrace, hPtrace 0, hPtrace 1, zero_add]
    funext i
    fin_cases i <;> norm_num [innerEndpointValues]
  have hqpot : InnerRadialPotentialClass D j (R B.l) (R B.h) q.1 v := by
    simpa only [q, qZ, qP, v, Prod.fst_add, Prod.smul_fst] using
      hZpot.add (((hPpot 0).smul (z 0)).add ((hPpot 1).smul (z 1)))
  change ∃ q : InnerRadialH1Pair D, ∃ potential : RadialModeL2 D,
    q.1 = out.1 ∧ q ∈ dom ∧ tr q = z ∧
    InnerRadialPotentialClass D j (R B.l) (R B.h) q.1 potential ∧
    (if B.bordered then ⟪col, q.1⟫_ℝ = F.2 else out.2 = 0 ∧ F.2 = 0) ∧
    ∀ T ∈ innerRadialH1Zero D (R B.l) (R B.h),
      innerRadialWeakResidual D q potential F.1 col out.2 T = 0
  refine ⟨q, v, ?_, hqdom, hqtrace, hqpot, ?_, ?_⟩
  · simp only [q, qZ, qP, out, Prod.fst_add, Prod.smul_fst]
  · cases hb : B.bordered with
    | false =>
      simp only [hb, Bool.false_eq_true, ite_false] at hZrow hProw ⊢
      refine ⟨?_, hZrow.2⟩
      simp only [out, Prod.snd_add, Prod.smul_snd, smul_eq_mul,
        hZrow.1, hProw 0, hProw 1, mul_zero, add_zero]
    | true =>
      simp only [hb, ite_true] at hZrow hProw ⊢
      simp only [q, qZ, qP, Prod.fst_add, Prod.smul_fst,
        inner_add_right, real_inner_smul_right,
        hZrow, hProw 0, hProw 1, mul_zero, add_zero]
  · intro T hT
    have heZ := hZweak T hT
    have he0 := hPweak 0 T hT
    have he1 := hPweak 1 T hT
    calc
      innerRadialWeakResidual D q v F.1 col out.2 T =
          innerRadialWeakResidual D qZ vZ F.1 col Z.2 T +
            (z 0 * innerRadialWeakResidual D (qP 0) (vP 0) 0 col (P 0).2 T +
              z 1 * innerRadialWeakResidual D (qP 1) (vP 1) 0 col (P 1).2 T) := by
        simp only [q, v, out, innerRadialWeakResidual_apply, Prod.snd_add,
          Prod.smul_snd, smul_eq_mul, inner_add_left, real_inner_smul_left,
          inner_zero_left, sub_zero]
        ring
      _ = 0 := by rw [heZ, he0, he1, mul_zero, mul_zero, add_zero, add_zero]

end ContinuousFlexibility.Radial
