import ContinuousFlexibility.Radial.InnerRadialAffineLift
import ContinuousFlexibility.Radial.InnerFiniteWeakGluing
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The actual finite physical weak inner problem

The pieces are consecutive intervals in one radial reference domain.
Their value/normalized-gradient pairs use the same physical measure.
Boundary vectors live at the internal cuts only, so the two outer
endpoint values vanish. There is one central scalar, not one scalar per
piece. The global weak graph is defined by the actual energy tested
against all matched first-order fields.

The gluing theorem proves that this global equation is equivalent to
the local zero-endpoint equations and cancellation of the total weak
outgoing flux.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace BigOperators

/-- Both endpoint values of a piece, restricted from the actual internal
cut vector. The two endpoints outside the internal cut set are zero. -/
def innerChainBoundaryRestriction (n : ℕ) (p : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun ξ i :=
    if i = 0 then
      if hp : 0 < p.val then ξ ⟨p.val - 1, by omega⟩ else 0
    else
      if hp : p.val < n then ξ ⟨p.val, hp⟩ else 0
  map_add' ξ η := by
    funext i
    by_cases hi : i = 0
    · by_cases hp : 0 < p.val <;> simp [hi, hp, PiLp.add_apply]
    · by_cases hp : p.val < n <;> simp [hi, hp, PiLp.add_apply]
  map_smul' c ξ := by
    funext i
    by_cases hi : i = 0
    · by_cases hp : 0 < p.val <;> simp [hi, hp, PiLp.smul_apply]
    · by_cases hp : p.val < n <;> simp [hi, hp, PiLp.smul_apply]

@[simp] theorem innerChainBoundaryRestriction_apply (n : ℕ) (p : Fin (n + 1))
    (ξ : EuclideanSpace ℝ (Fin n)) (i : Fin 2) :
    innerChainBoundaryRestriction n p ξ i =
      if i = 0 then
        if hp : 0 < p.val then ξ ⟨p.val - 1, by omega⟩ else 0
      else if hp : p.val < n then ξ ⟨p.val, hp⟩ else 0 := rfl

theorem innerChainBoundaryRestriction_outer (n : ℕ) (ξ : EuclideanSpace ℝ (Fin n)) :
    innerChainBoundaryRestriction n 0 ξ 0 = 0 ∧
      innerChainBoundaryRestriction n (Fin.last n) ξ 1 = 0 := by
  constructor <;> simp [innerChainBoundaryRestriction_apply]

theorem innerChainBoundaryRestriction_match (n : ℕ) (i : Fin n)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    innerChainBoundaryRestriction n i.castSucc ξ 1 = ξ i ∧
      innerChainBoundaryRestriction n i.succ ξ 0 = ξ i := by
  constructor
  · simp [innerChainBoundaryRestriction_apply, i.isLt]
  · simp [innerChainBoundaryRestriction_apply, Nat.succ_pos]

/-- Actual ordered piece endpoints inside the radial core. These are
geometric inputs, with no differential equation or inverse in the data. -/
structure InnerRadialChainGeometry (D : ReferenceData) (n : ℕ) where
  cuts : Fin (n + 2) → ℝ
  increasing : StrictMono cuts
  left_pos : ∀ p : Fin (n + 1), 0 < cuts p.castSucc
  in_core : ∀ p : Fin (n + 1), Ioo (cuts p.castSucc) (cuts p.succ) ⊆ radialCore D
  weight_pos : ∀ p : Fin (n + 1), ∀ r ∈ Icc (cuts p.castSucc) (cuts p.succ), 0 < D.w r

namespace InnerRadialChainGeometry

def left {D : ReferenceData} {n : ℕ} (G : InnerRadialChainGeometry D n)
    (p : Fin (n + 1)) : ℝ := G.cuts p.castSucc

def right {D : ReferenceData} {n : ℕ} (G : InnerRadialChainGeometry D n)
    (p : Fin (n + 1)) : ℝ := G.cuts p.succ

theorem left_lt_right {D : ReferenceData} {n : ℕ} (G : InnerRadialChainGeometry D n)
    (p : Fin (n + 1)) : G.left p < G.right p :=
  G.increasing p.castSucc_lt_succ

end InnerRadialChainGeometry

section PhysicalChain

variable (D : ReferenceData) (hw : Continuous D.w) {n : ℕ}
  (G : InnerRadialChainGeometry D n)

/-- The fixed physical boundary lift on one actual piece. -/
def innerRadialChainLift (p : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] InnerRadialH1Pair D :=
  (innerRadialAffineLift D hw (G.left_pos p) (G.in_core p) (G.weight_pos p)).comp
    (innerChainBoundaryRestriction n p)

/-- The actual finite weak domain: all pieces share one internal cut
vector, and their residuals after the fixed affine lifts are in the
actual zero-endpoint physical closures. -/
def innerRadialChainDomain : Submodule ℝ (Fin (n + 1) → InnerRadialH1Pair D) :=
  innerMatchedPieceDomain
    (fun p => (innerRadialH1Zero D (G.left p) (G.right p)).toSubmodule)
    (innerRadialChainLift D hw G)

theorem innerRadialChainDomain_trace_iff (q : Fin (n + 1) → InnerRadialH1Pair D) :
    q ∈ innerRadialChainDomain D hw G ↔
      ∃ ξ : EuclideanSpace ℝ (Fin n), ∀ p,
        q p ∈ innerRadialH1Domain D hw (G.left_pos p) (G.in_core p) (G.weight_pos p) ∧
          innerRadialH1Trace D hw (G.left_pos p) (G.in_core p) (G.weight_pos p) (q p) =
            innerChainBoundaryRestriction n p ξ := by
  change (∃ ξ, ∀ p, q p - innerRadialChainLift D hw G p ξ ∈
    innerRadialH1Zero D (G.left p) (G.right p)) ↔ _
  constructor
  · rintro ⟨ξ, hξ⟩
    refine ⟨ξ, ?_⟩
    intro p
    apply (innerRadialH1Domain_trace_iff D hw (G.left_lt_right p)
      (G.left_pos p) (G.in_core p) (G.weight_pos p) (q p) _).mpr
    simpa only [innerRadialChainLift, LinearMap.comp_apply] using hξ p
  · rintro ⟨ξ, hξ⟩
    refine ⟨ξ, ?_⟩
    intro p
    simpa only [innerRadialChainLift, LinearMap.comp_apply] using
      (innerRadialH1Domain_trace_iff D hw (G.left_lt_right p)
        (G.left_pos p) (G.in_core p) (G.weight_pos p) (q p) _).mp (hξ p)

/-- The physical multiplication relation for the signed radial
potential. Positive gaps and negative wells use this same formula. -/
def InnerRadialPotentialClass (j a b : ℝ) (u v : RadialModeL2 D) : Prop :=
  (v : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator
    (fun r => ((j ^ 2 / 12) * (r * deriv D.w r / D.w r)) * u r)

/-- Actual energy minus forcing, including the single central border.
The potential coordinate is constrained by InnerRadialPotentialClass
in the weak graph; it is not a supplied abstract bilinear form. -/
def innerRadialWeakResidual (q : InnerRadialH1Pair D)
    (v f g : RadialModeL2 D) (borderScalar : ℝ) : InnerRadialH1Pair D →ₗ[ℝ] ℝ where
  toFun r := ⟪q.2, r.2⟫_ℝ + ⟪v, r.1⟫_ℝ + borderScalar * ⟪g, r.1⟫_ℝ - ⟪f, r.1⟫_ℝ
  map_add' r s := by
    simp only [Prod.fst_add, Prod.snd_add, inner_add_right]
    ring
  map_smul' c r := by
    simp only [Prod.fst_smul, Prod.snd_smul, real_inner_smul_right, smul_eq_mul]
    ring

/-- Exactly one piece carries the one temporary scalar column. -/
def innerRadialChainResidual (central : Fin (n + 1)) (column : RadialModeL2 D)
    (q : Fin (n + 1) → InnerRadialH1Pair D)
    (v f : Fin (n + 1) → RadialModeL2 D) (borderScalar : ℝ)
    (p : Fin (n + 1)) : InnerRadialH1Pair D →ₗ[ℝ] ℝ :=
  innerRadialWeakResidual D (q p) (v p) (f p) (if p = central then column else 0) borderScalar

/-- The boundary residual is the sum of actual outgoing weak flux
pairings on the two sides of each internal cut. -/
def innerRadialChainFlux (central : Fin (n + 1)) (column : RadialModeL2 D)
    (q : Fin (n + 1) → InnerRadialH1Pair D)
    (v f : Fin (n + 1) → RadialModeL2 D) (borderScalar : ℝ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ :=
  innerMatchedWeakFlux (innerRadialChainLift D hw G)
    (innerRadialChainResidual D central column q v f borderScalar)

/-- The actual weak inner problem. The scalar row is imposed once,
only in the bordered mode; in other modes the scalar and row source
are both zero. -/
def InnerRadialChainWeakGraph (bordered : Bool) (j : ℝ)
    (central : Fin (n + 1)) (column : RadialModeL2 D)
    (q : Fin (n + 1) → InnerRadialH1Pair D)
    (v f : Fin (n + 1) → RadialModeL2 D) (borderScalar scalarSource : ℝ) : Prop :=
  q ∈ innerRadialChainDomain D hw G ∧
  (∀ p, InnerRadialPotentialClass D j (G.left p) (G.right p) (q p).1 (v p)) ∧
  (if bordered then ⟪column, (q central).1⟫_ℝ = scalarSource
    else borderScalar = 0 ∧ scalarSource = 0) ∧
  ∀ r ∈ innerRadialChainDomain D hw G,
    ∑ p, innerRadialChainResidual D central column q v f borderScalar p (r p) = 0

/-- The global physical weak graph is obtained from the local closed
Dirichlet equations and the actual finite interface cancellation.
This equivalence also supplies the reverse global-to-local direction. -/
theorem innerRadialChainWeakGraph_iff (bordered : Bool) (j : ℝ)
    (central : Fin (n + 1)) (column : RadialModeL2 D)
    (q : Fin (n + 1) → InnerRadialH1Pair D)
    (v f : Fin (n + 1) → RadialModeL2 D) (borderScalar scalarSource : ℝ) :
    InnerRadialChainWeakGraph D hw G bordered j central column q v f borderScalar scalarSource ↔
      q ∈ innerRadialChainDomain D hw G ∧
      (∀ p, InnerRadialPotentialClass D j (G.left p) (G.right p) (q p).1 (v p)) ∧
      (if bordered then ⟪column, (q central).1⟫_ℝ = scalarSource
        else borderScalar = 0 ∧ scalarSource = 0) ∧
      (∀ p, ∀ r ∈ innerRadialH1Zero D (G.left p) (G.right p),
        innerRadialChainResidual D central column q v f borderScalar p r = 0) ∧
      innerRadialChainFlux D hw G central column q v f borderScalar = 0 := by
  unfold InnerRadialChainWeakGraph innerRadialChainDomain innerRadialChainFlux
  rw [innerMatchedPiece_weak_gluing]

end PhysicalChain

end ContinuousFlexibility.Radial
