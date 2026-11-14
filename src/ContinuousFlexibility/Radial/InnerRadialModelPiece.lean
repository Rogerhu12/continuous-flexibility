module

public import ContinuousFlexibility.Radial.InnerRadialPhysicalSource
public import ContinuousFlexibility.Radial.InnerLiouvilleDirichletUniqueness
public import ContinuousFlexibility.Radial.InnerLiouvilleLocalSolution

/-!
# Actual retained-model uniqueness in the finite physical chain

The local inverse is the transported R09 witness. Its proved physical
zero-kernel theorem supplies the finite-chain kernel condition. Only
the distinguished central chart may carry the temporary scalar column;
on every other chart its local scalar is zero.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

private theorem innerRadialModelDomainTrace_congr
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

section ModelPiece

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

include hB M hlam hR hscale hp hcore hweight U hU hv hDw hcoeff
  hleft hright hbordered hcolumn

/-- The actual transported local Dirichlet theorem, including its
central row, proves the common finite-chain kernel condition. -/
theorem innerRadialModelPieceKernelUnique :
    InnerRadialPieceKernelUnique D G bordered j central column piece := by
  intro q v borderScalar hq hpot hrow hweak
  have hq' : q ∈ innerRadialH1Zero D (R B.l) (R B.h) := by
    simpa only [hleft, hright] using hq
  have hpot' : InnerRadialPotentialClass D j (R B.l) (R B.h) q.1 v := by
    simpa only [hleft, hright] using hpot
  by_cases hc : piece = central
  · have hrow' : if B.bordered then
        ⟪innerLiouvilleColumnLift D hB.1.le hlam hR hscale hp hcore hweight B.border, q.1⟫_ℝ = 0
        else borderScalar = 0 := by
      simpa only [hbordered, if_pos hc, ite_true, hcolumn hc] using hrow
    have he : ∀ T ∈ innerRadialH1Zero D (R B.l) (R B.h),
        innerRadialWeakResidual D q v 0
          (innerLiouvilleColumnLift D hB.1.le hlam hR hscale hp hcore hweight B.border)
          borderScalar T = 0 := by
      intro T hT
      have hT' : T ∈ innerRadialH1Zero D (G.left piece) (G.right piece) := by
        simpa only [hleft, hright] using hT
      simpa only [if_pos hc, ite_true, hcolumn hc] using hweak T hT'
    have h := innerLiouvilleLocalizedDirichlet_kernel D hB M hlam hR hscale hp hcore hweight
      U hU hv hDw j hcoeff q v borderScalar hq' hpot' hrow' he
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · have hrow' : if B.bordered then
        ⟪innerLiouvilleColumnLift D hB.1.le hlam hR hscale hp hcore hweight B.border, q.1⟫_ℝ = 0
        else (0 : ℝ) = 0 := by
      simp only [hbordered, if_neg hc, Bool.false_eq_true, ite_false]
    have he : ∀ T ∈ innerRadialH1Zero D (R B.l) (R B.h),
        innerRadialWeakResidual D q v 0
          (innerLiouvilleColumnLift D hB.1.le hlam hR hscale hp hcore hweight B.border)
          0 T = 0 := by
      intro T hT
      have hT' : T ∈ innerRadialH1Zero D (G.left piece) (G.right piece) := by
        simpa only [hleft, hright] using hT
      simpa only [if_neg hc, innerRadialWeakResidual_apply, inner_zero_left,
        mul_zero, zero_mul, add_zero] using hweak T hT'
    have h := innerLiouvilleLocalizedDirichlet_kernel D hB M hlam hR hscale hp hcore hweight
      U hU hv hDw j hcoeff q v 0 hq' hpot' hrow' he
    exact ⟨h.1, h.2.1, fun hp => (hc hp).elim⟩

local notation "H" => InnerRadialPhysicalSource D G bordered
local notation "forcing" => innerRadialPhysicalForcing D G bordered
local notation "rowSource" => innerRadialPhysicalRowLinear D G bordered

/-- The same transported model inverse and normalized Poisson columns
supply an actual finite-chain source/trace solution. -/
theorem exists_innerRadialModelPieceSolution (F : H)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    let localSource := (forcing F piece, if piece = central then rowSource F else 0)
    let z := innerChainBoundaryRestriction n piece ξ
    let P := fun i => innerLiouvilleUnitPoissonPair D hB.1.le hlam hR hscale hp hcore hweight
      U hU hv (bufferCut B i) (M.column i).field (M.column i).scalar
    let out := innerLiouvillePhysicalDirichlet D hB.1.le hlam hR hscale hp hcore hweight
      U hU hv M.dirichlet localSource + (z 0 • P 0 + z 1 • P 1)
    ∃ solution : InnerRadialPieceSolution D hDw.continuous G forcing rowSource
        bordered j central column F ξ piece,
      solution.q.1 = out.1 ∧ solution.borderScalar = out.2 := by
  let localSource : RadialModeL2 D × ℝ :=
    (forcing F piece, if piece = central then rowSource F else 0)
  let z := innerChainBoundaryRestriction n piece ξ
  let P : Fin 2 → RadialModeL2 D × ℝ := fun i =>
    innerLiouvilleUnitPoissonPair D hB.1.le hlam hR hscale hp hcore hweight
      U hU hv (bufferCut B i) (M.column i).field (M.column i).scalar
  let out := innerLiouvillePhysicalDirichlet D hB.1.le hlam hR hscale hp hcore hweight
    U hU hv M.dirichlet localSource + (z 0 • P 0 + z 1 • P 1)
  let hpos := innerLiouville_radial_weight_pos_closed D hB.1.le hlam hR hp hweight
  have hscalar : B.bordered = false → localSource.2 = 0 := by
    intro hb
    dsimp only [localSource]
    by_cases hc : piece = central
    · rw [if_pos hc]
      have hglobal : bordered = false := by
        have he := hbordered
        rw [if_pos hc] at he
        exact he.symm.trans hb
      subst bordered
      exact innerRadialPhysicalRow_unbordered D G F
    · rw [if_neg hc]
  obtain ⟨q, potential, hvalue, hdomain, htrace, hpotential, hrow, hweak⟩ :=
    innerLiouvilleLocalizedSolution D hB M hlam hR hscale hp hcore hweight U hU hv
      hDw j hcoeff localSource hscalar z
  change q.1 = out.1 at hvalue
  change (if B.bordered then
    ⟪innerLiouvilleColumnLift D hB.1.le hlam hR hscale hp hcore hweight B.border, q.1⟫_ℝ =
      localSource.2 else out.2 = 0 ∧ localSource.2 = 0) at hrow
  change (∀ T ∈ innerRadialH1Zero D (R B.l) (R B.h),
    innerRadialWeakResidual D q potential localSource.1
      (innerLiouvilleColumnLift D hB.1.le hlam hR hscale hp hcore hweight B.border)
      out.2 T = 0) at hweak
  have hfull : q ∈ innerRadialH1Domain D hDw.continuous
      (G.left_pos piece) (G.in_core piece) (G.weight_pos piece) ∧
      innerRadialH1Trace D hDw.continuous (G.left_pos piece) (G.in_core piece)
        (G.weight_pos piece) q = z :=
    (innerRadialModelDomainTrace_congr D hDw.continuous
      (G.left_pos piece) (G.in_core piece) (G.weight_pos piece)
      (hp B.l (left_mem_Icc.mpr hB.1.le)).1 hcore hpos
      hleft hright q z).mpr ⟨hdomain, htrace⟩
  have hpotential' : InnerRadialPotentialClass D j (G.left piece) (G.right piece)
      q.1 potential := by
    simpa only [hleft, hright] using hpotential
  have hrow' : if piece = central then
      if bordered then ⟪column, q.1⟫_ℝ = rowSource F
        else out.2 = 0 ∧ rowSource F = 0
      else out.2 = 0 := by
    by_cases hc : piece = central
    · simpa only [hbordered, if_pos hc, ite_true, hcolumn hc, localSource] using hrow
    · have hb : B.bordered = false := by
        simpa only [if_neg hc] using hbordered
      rw [if_neg hc]
      have hr : out.2 = 0 ∧ localSource.2 = 0 := by
        simpa only [hb, Bool.false_eq_true, ite_false] using hrow
      exact hr.1
  have hweak' : ∀ T ∈ innerRadialH1Zero D (G.left piece) (G.right piece),
      innerRadialWeakResidual D q potential (forcing F piece)
        (if piece = central then column else 0) out.2 T = 0 := by
    intro T hT
    have hT' : T ∈ innerRadialH1Zero D (R B.l) (R B.h) := by
      simpa only [hleft, hright] using hT
    by_cases hc : piece = central
    · simpa only [if_pos hc, ite_true, hcolumn hc, localSource] using hweak T hT'
    · have hc0 : out.2 = 0 := by
        simpa only [if_neg hc] using hrow'
      simpa only [if_neg hc, localSource, hc0, innerRadialWeakResidual_apply,
        zero_mul, add_zero] using hweak T hT'
  refine ⟨
    { q := q
      potential := potential
      borderScalar := out.2
      domain := hfull.1
      trace := hfull.2
      potential_relation := hpotential'
      row := hrow'
      weak := hweak' },
    hvalue, rfl⟩

theorem innerRadialModelPieceSolution_nonempty (F : H)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    Nonempty (InnerRadialPieceSolution D hDw.continuous G forcing rowSource
      bordered j central column F ξ piece) := by
  obtain ⟨solution, _⟩ := exists_innerRadialModelPieceSolution D G bordered j central column
    piece hB M hlam hR hscale hp hcore hweight U hU hv hDw hcoeff
    hleft hright hbordered hcolumn F ξ
  exact ⟨solution⟩

end ModelPiece

end ContinuousFlexibility.Radial
