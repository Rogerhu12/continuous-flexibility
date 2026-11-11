import ContinuousFlexibility.Radial.InnerRadialModelPiece
import ContinuousFlexibility.Radial.InnerLiouvilleUnitFlux
import ContinuousFlexibility.Radial.InnerChainBoundaryHilbert

/-!
# The actual retained-model conormal block in the finite chain

The two genuine normalized model columns are combined with the same
physical boundary values used by the chain. Their fields, scalar,
gradient and potential remain those of that combination. The resulting
affine-hat flux is the full physical matrix: the true diagonal kappa,
including the density drift, plus the original compression error.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace BigOperators

/-- The full physical conormal matrix of the same retained model. -/
def InnerBufferLocalizedData.physicalFluxMatrix {B : BufferData} {C K : ℝ}
    (M : InnerBufferLocalizedData B C K) (lam : ℝ) (scale : ℝ → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal (innerLiouvilleBoundaryKappa lam scale (bufferCut B)
    (fun i => (M.column i).inwardEnergy)) +
      M.physicalFluxError lam (fun i => scale (bufferCut B i))

private theorem innerRadialTwoColumnResidual (D : ReferenceData)
    (q : Fin 2 → InnerRadialH1Pair D) (v : Fin 2 → RadialModeL2 D)
    (scalar z : Fin 2 → ℝ) (column : RadialModeL2 D) (r : InnerRadialH1Pair D) :
    innerRadialWeakResidual D (z 0 • q 0 + z 1 • q 1)
      (z 0 • v 0 + z 1 • v 1) 0 column
      (z 0 * scalar 0 + z 1 * scalar 1) r =
      z 0 * innerRadialWeakResidual D (q 0) (v 0) 0 column (scalar 0) r +
        z 1 * innerRadialWeakResidual D (q 1) (v 1) 0 column (scalar 1) r := by
  simp only [innerRadialWeakResidual_apply, Prod.snd_add, Prod.smul_snd,
    inner_add_left, real_inner_smul_left, inner_zero_left, sub_zero]
  ring

private theorem innerRadialModelPoissonDomain_congr
    (D : ReferenceData) (hw : Continuous D.w) {a b a' b' : ℝ}
    (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (ha' : 0 < a') (hcore' : Ioo a' b' ⊆ radialCore D)
    (hpos' : ∀ r ∈ Icc a' b', 0 < D.w r)
    (hleft : a = a') (hright : b = b')
    (q : InnerRadialH1Pair D) (z : Fin 2 → ℝ) :
    (q ∈ innerRadialH1Domain D hw ha hcore hpos ∧
      innerRadialH1Trace D hw ha hcore hpos q = z) ↔
    (q ∈ innerRadialH1Domain D hw ha' hcore' hpos' ∧
      innerRadialH1Trace D hw ha' hcore' hpos' q = z) := by
  subst a'
  subst b'
  exact Iff.rfl

private theorem innerRadialModelPoissonAffine_congr
    (D : ReferenceData) (hw : Continuous D.w) {a b a' b' : ℝ}
    (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (ha' : 0 < a') (hcore' : Ioo a' b' ⊆ radialCore D)
    (hpos' : ∀ r ∈ Icc a' b', 0 < D.w r)
    (hleft : a = a') (hright : b = b') (i : Fin 2) :
    innerRadialAffineUnitPair D hw ha hcore hpos i =
      innerRadialAffineUnitPair D hw ha' hcore' hpos' i := by
  subst a'
  subst b'
  rfl

section ModelPoissonPiece

variable (D : ReferenceData) {n : ℕ} (G : InnerRadialChainGeometry D n)
  (bordered : Bool) (j : ℝ) (central : Fin (n + 1)) (column : RadialModeL2 D)
  (piece : Fin (n + 1))
  {B : BufferData} (hB : BufferHypotheses B) {C K : ℝ}
  (M : InnerBufferLocalizedData B C K)
  {R scale : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam)
  (hR : ContDiff ℝ ∞ R) (hscale : ContDiff ℝ ∞ scale)
  (hp : ∀ x ∈ Icc B.l B.h, 0 < R x ∧ 0 < deriv R x ∧ 0 < scale x)
  (hcore : Ioo (R B.l) (R B.h) ⊆ radialCore D)
  (hweight : ∀ x ∈ Icc B.l B.h,
    D.w (R x) = lam * scale x ^ 2 * deriv R x)
  (U : ℝ) (hU : 0 ≤ U)
  (hv : ∀ x ∈ Icc B.l B.h, |deriv R x / R x| ≤ U)
  (hDw : ContDiff ℝ ∞ D.w)
  (hcoeff : ∀ x ∈ Ioo B.l B.h,
    B.potential x = liouvilleV0 scale x - j ^ 2 * liouvilleRho R scale x)
  (hleft : G.left piece = R B.l) (hright : G.right piece = R B.h)
  (hbordered : B.bordered = if piece = central then bordered else false)
  (hcolumn : piece = central →
    innerLiouvilleColumnLift D hB.1.le hlam hR hscale hp hcore hweight B.border = column)

include hcoeff hleft hright hbordered hcolumn

local notation "forcing" => innerRadialPhysicalForcing D G bordered
local notation "rowSource" => innerRadialPhysicalRowLinear D G bordered

/-- The same actual model Poisson columns realize every chain trace
and have the complete physical conormal block, with no assumed flux
identity and with exactly the original temporary scalar. -/
theorem exists_innerRadialModelPoissonPiece (ξ : EuclideanSpace ℝ (Fin n)) :
    let z := innerChainBoundaryRestriction n piece ξ
    let P := fun i => innerLiouvilleUnitPoissonPair D hB.1.le hlam hR hscale hp hcore hweight
      U hU hv (bufferCut B i) (M.column i).field (M.column i).scalar
    let out := z 0 • P 0 + z 1 • P 1
    ∃ solution : InnerRadialPieceSolution D hDw.continuous G forcing rowSource
        bordered j central column 0 ξ piece,
      solution.q.1 = out.1 ∧ solution.borderScalar = out.2 ∧
      ∀ k : Fin 2,
        innerRadialWeakResidual D solution.q solution.potential 0
          (if piece = central then column else 0) solution.borderScalar
          (innerRadialAffineUnitPair D hDw.continuous (G.left_pos piece)
            (G.in_core piece) (G.weight_pos piece) k) =
          Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
            (M.physicalFluxMatrix lam scale) (innerChainBoundaryCLM n piece ξ) k := by
  let z := innerChainBoundaryRestriction n piece ξ
  let P : Fin 2 → RadialModeL2 D × ℝ := fun i =>
    innerLiouvilleUnitPoissonPair D hB.1.le hlam hR hscale hp hcore hweight
      U hU hv (bufferCut B i) (M.column i).field (M.column i).scalar
  let out := z 0 • P 0 + z 1 • P 1
  let col := innerLiouvilleColumnLift D hB.1.le hlam hR hscale hp hcore hweight B.border
  let hpos := innerLiouville_radial_weight_pos_closed D hB.1.le hlam hR hp hweight
  let dom := innerRadialH1Domain D hDw.continuous
    (hp B.l (left_mem_Icc.mpr hB.1.le)).1 hcore hpos
  let tr := innerRadialH1Trace D hDw.continuous
    (hp B.l (left_mem_Icc.mpr hB.1.le)).1 hcore hpos
  have hunit (i : Fin 2) :=
    innerLiouvilleLocalizedUnit_flux_solution D hB M hlam hR hscale hp hcore hweight
      U hU hv hDw j hcoeff i
  choose dP vP hPdom hPtrace hPpot hProw hPweak hPflux using hunit
  change (∀ i, if B.bordered then ⟪col, (P i).1⟫_ℝ = 0 else (P i).2 = 0) at hProw
  let qP : Fin 2 → InnerRadialH1Pair D := fun i => ((P i).1, dP i)
  let q := z 0 • qP 0 + z 1 • qP 1
  let v := z 0 • vP 0 + z 1 • vP 1
  have hqdom : q ∈ dom :=
    dom.add_mem (dom.smul_mem (z 0) (hPdom 0)) (dom.smul_mem (z 1) (hPdom 1))
  have hqtrace : tr q = z := by
    rw [show q = z 0 • qP 0 + z 1 • qP 1 from rfl,
      map_add, map_smul, map_smul, hPtrace 0, hPtrace 1]
    funext i
    fin_cases i <;> norm_num [innerEndpointValues]
  have hqpot : InnerRadialPotentialClass D j (R B.l) (R B.h) q.1 v := by
    simpa only [q, qP, v, Prod.fst_add, Prod.smul_fst] using
      ((hPpot 0).smul (z 0)).add ((hPpot 1).smul (z 1))
  have hqrow : if B.bordered then ⟪col, q.1⟫_ℝ = 0
      else out.2 = 0 ∧ (0 : ℝ) = 0 := by
    cases hb : B.bordered with
    | false =>
      simp only [hb, Bool.false_eq_true, ite_false] at hProw ⊢
      refine ⟨?_, True.intro⟩
      simp only [out, Prod.snd_add, Prod.smul_snd, smul_eq_mul,
        hProw 0, hProw 1, mul_zero, add_zero]
    | true =>
      simp only [hb, ite_true] at hProw ⊢
      simp only [q, qP, Prod.fst_add, Prod.smul_fst, inner_add_right,
        real_inner_smul_right, hProw 0, hProw 1, mul_zero, add_zero]
  have hfull : q ∈ innerRadialH1Domain D hDw.continuous
      (G.left_pos piece) (G.in_core piece) (G.weight_pos piece) ∧
      innerRadialH1Trace D hDw.continuous (G.left_pos piece) (G.in_core piece)
        (G.weight_pos piece) q = z :=
    (innerRadialModelPoissonDomain_congr D hDw.continuous
      (G.left_pos piece) (G.in_core piece) (G.weight_pos piece)
      (hp B.l (left_mem_Icc.mpr hB.1.le)).1 hcore hpos
      hleft hright q z).mpr ⟨hqdom, hqtrace⟩
  have hpotential : InnerRadialPotentialClass D j (G.left piece) (G.right piece)
      q.1 v := by simpa only [hleft, hright] using hqpot
  have hrow : if piece = central then
      if bordered then ⟪column, q.1⟫_ℝ = rowSource 0
        else out.2 = 0 ∧ rowSource 0 = 0
      else out.2 = 0 := by
    by_cases hc : piece = central
    · simpa only [hbordered, if_pos hc, ite_true, col, hcolumn hc, map_zero] using hqrow
    · rw [if_neg hc]
      have hb : B.bordered = false := by simpa only [if_neg hc] using hbordered
      have hr : out.2 = 0 ∧ (0 : ℝ) = 0 := by
        simpa only [hb, Bool.false_eq_true, ite_false] using hqrow
      exact hr.1
  have hres (T : InnerRadialH1Pair D) :
      innerRadialWeakResidual D q v 0 (if piece = central then column else 0) out.2 T =
        innerRadialWeakResidual D q v 0 col out.2 T := by
    by_cases hc : piece = central
    · simp only [if_pos hc, col, hcolumn hc]
    · have hc0 : out.2 = 0 := by simpa only [if_neg hc] using hrow
      simp only [if_neg hc, hc0, innerRadialWeakResidual_apply, zero_mul]
  have hcomb (T : InnerRadialH1Pair D) :
      innerRadialWeakResidual D q v 0 col out.2 T =
        z 0 * innerRadialWeakResidual D (qP 0) (vP 0) 0 col (P 0).2 T +
          z 1 * innerRadialWeakResidual D (qP 1) (vP 1) 0 col (P 1).2 T := by
    simpa only [q, v, out, Prod.snd_add, Prod.smul_snd, smul_eq_mul] using
      innerRadialTwoColumnResidual D qP vP (fun i => (P i).2) z col T
  have hweak : ∀ T ∈ innerRadialH1Zero D (G.left piece) (G.right piece),
      innerRadialWeakResidual D q v (forcing 0 piece)
        (if piece = central then column else 0) out.2 T = 0 := by
    intro T hT
    have hT' : T ∈ innerRadialH1Zero D (R B.l) (R B.h) := by
      simpa only [hleft, hright] using hT
    simp only [map_zero, Pi.zero_apply]
    rw [hres T, hcomb T, hPweak 0 T hT', hPweak 1 T hT', mul_zero, mul_zero, add_zero]
  let solution : InnerRadialPieceSolution D hDw.continuous G forcing rowSource
      bordered j central column 0 ξ piece :=
    { q := q, potential := v, borderScalar := out.2, domain := hfull.1,
      trace := hfull.2, potential_relation := hpotential, row := hrow, weak := hweak }
  refine ⟨solution, ?_, rfl, ?_⟩
  · change q.1 = out.1
    simp only [q, qP, out, Prod.fst_add, Prod.smul_fst]
  · intro k
    have hhat := innerRadialModelPoissonAffine_congr D hDw.continuous
      (G.left_pos piece) (G.in_core piece) (G.weight_pos piece)
      (hp B.l (left_mem_Icc.mpr hB.1.le)).1 hcore hpos hleft hright k
    dsimp only [solution]
    rw [hres, hhat, hcomb, hPflux 0 k, hPflux 1 k]
    have hm := congrFun (Matrix.ofLp_toEuclideanCLM
      (M.physicalFluxMatrix lam scale) (innerChainBoundaryCLM n piece ξ)) k
    rw [hm, InnerBufferLocalizedData.physicalFluxMatrix, Matrix.add_mulVec,
      Pi.add_apply, Matrix.mulVec_diagonal]
    simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, innerChainBoundaryCLM_apply]
    have hpoly (t d : Fin 2 → ℝ) (e : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) :
        t 0 * ((if i = 0 then d i else 0) + e i 0) +
            t 1 * ((if i = 1 then d i else 0) + e i 1) =
          d i * t i + (e i 0 * t 0 + e i 1 * t 1) := by
      fin_cases i <;>
        simp only [eq_self_iff_true, show (0 : Fin 2) ≠ 1 by decide,
          show (1 : Fin 2) ≠ 0 by decide, ite_true, ite_false, zero_add] <;> ring
    exact hpoly z
      (innerLiouvilleBoundaryKappa lam scale (bufferCut B)
        (fun l => (M.column l).inwardEnergy))
      (M.physicalFluxError lam (fun l => scale (bufferCut B l))) k

end ModelPoissonPiece

end ContinuousFlexibility.Radial
