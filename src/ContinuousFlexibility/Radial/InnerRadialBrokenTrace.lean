module

public import ContinuousFlexibility.Radial.InnerRadialBrokenSpace

/-!
# The actual internal trace and the local uniqueness kernel

The common boundary vector is recovered from the physical traces of
the left neighboring pieces. Zero internal trace and the two exterior
Dirichlet values put every piece in its actual zero-endpoint closure.
Consequently piecewise Dirichlet uniqueness implies uniqueness of the
whole broken weak graph at zero source and zero trace.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

section ChainTrace

variable (D : ReferenceData) (hw : Continuous D.w) {n : ℕ}
  (G : InnerRadialChainGeometry D n)

/-- The actual common trace at the internal cuts. -/
def innerRadialChainTrace :
    (Fin (n + 1) → InnerRadialH1Pair D) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun q := WithLp.toLp 2 (fun i : Fin n =>
    innerRadialH1Trace D hw (G.left_pos i.castSucc) (G.in_core i.castSucc)
      (G.weight_pos i.castSucc) (q i.castSucc) 1)
  map_add' q r := by
    ext i
    simp only [PiLp.toLp_apply, PiLp.add_apply, Pi.add_apply, map_add]
  map_smul' c q := by
    ext i
    simp only [PiLp.toLp_apply, PiLp.smul_apply, Pi.smul_apply,
      map_smul, RingHom.id_apply]

@[simp] theorem innerRadialChainTrace_apply
    (q : Fin (n + 1) → InnerRadialH1Pair D) (i : Fin n) :
    innerRadialChainTrace D hw G q i =
      innerRadialH1Trace D hw (G.left_pos i.castSucc) (G.in_core i.castSucc)
        (G.weight_pos i.castSucc) (q i.castSucc) 1 := rfl

/-- A common boundary label in the matched-domain definition is
uniquely recovered by the actual physical trace. -/
theorem innerRadialChainTrace_eq {q : Fin (n + 1) → InnerRadialH1Pair D}
    {ξ : EuclideanSpace ℝ (Fin n)}
    (hξ : ∀ p, innerRadialH1Trace D hw (G.left_pos p) (G.in_core p)
      (G.weight_pos p) (q p) = innerChainBoundaryRestriction n p ξ) :
    innerRadialChainTrace D hw G q = ξ := by
  ext i
  rw [innerRadialChainTrace_apply, hξ i.castSucc,
    (innerChainBoundaryRestriction_match n i ξ).1]

/-- Zero common trace forces every matched piece into the true
zero-endpoint closure. -/
theorem innerRadialChainDomain_zero_trace {q : Fin (n + 1) → InnerRadialH1Pair D}
    (hq : q ∈ innerRadialChainDomain D hw G)
    (htr : innerRadialChainTrace D hw G q = 0) :
    ∀ p, q p ∈ innerRadialH1Zero D (G.left p) (G.right p) := by
  obtain ⟨ξ, hξ⟩ := (innerRadialChainDomain_trace_iff D hw G q).mp hq
  have hξ0 : ξ = 0 :=
    (innerRadialChainTrace_eq D hw G (fun p => (hξ p).2)).symm.trans htr
  intro p
  have hp := (innerRadialH1Domain_trace_iff D hw (G.left_lt_right p)
    (G.left_pos p) (G.in_core p) (G.weight_pos p) (q p)
    (innerChainBoundaryRestriction n p ξ)).mp (hξ p)
  rwa [hξ0, map_zero, map_zero, sub_zero] at hp

/-- Subtracting the fixed lift of the recovered internal trace gives
an actual zero-endpoint field on every piece. -/
theorem innerRadialChainDomain_sub_lift {q : Fin (n + 1) → InnerRadialH1Pair D}
    (hq : q ∈ innerRadialChainDomain D hw G) :
    ∀ p, q p - innerRadialAffineLift D hw (G.left_pos p) (G.in_core p) (G.weight_pos p)
      (innerChainBoundaryRestriction n p (innerRadialChainTrace D hw G q)) ∈
      innerRadialH1Zero D (G.left p) (G.right p) := by
  obtain ⟨ξ, hξ⟩ := (innerRadialChainDomain_trace_iff D hw G q).mp hq
  have htr := innerRadialChainTrace_eq D hw G (fun p => (hξ p).2)
  intro p
  rw [htr]
  exact (innerRadialH1Domain_trace_iff D hw (G.left_lt_right p)
    (G.left_pos p) (G.in_core p) (G.weight_pos p) (q p)
    (innerChainBoundaryRestriction n p ξ)).mp (hξ p)

/-- The local homogeneous zero-Dirichlet uniqueness statement needed
for one actual piece. Only the central piece carries the scalar row.
This is a local realization property, not an assembled inverse. -/
def InnerRadialPieceKernelUnique (bordered : Bool) (j : ℝ)
    (central : Fin (n + 1)) (column : RadialModeL2 D) (p : Fin (n + 1)) : Prop :=
  ∀ (q : InnerRadialH1Pair D) (v : RadialModeL2 D) (borderScalar : ℝ),
    q ∈ innerRadialH1Zero D (G.left p) (G.right p) →
    InnerRadialPotentialClass D j (G.left p) (G.right p) q.1 v →
    (if p = central then
      if bordered then ⟪column, q.1⟫_ℝ = 0 else borderScalar = 0
      else True) →
    (∀ r ∈ innerRadialH1Zero D (G.left p) (G.right p),
      innerRadialWeakResidual D q v 0 (if p = central then column else 0) borderScalar r = 0) →
    q = 0 ∧ v = 0 ∧ (p = central → borderScalar = 0)

/-- Actual local value/scalar uniqueness already implies full
value/gradient/potential uniqueness: test the zero-forcing equation by
the same zero-endpoint field to kill its remaining gradient coordinate. -/
theorem innerRadialPieceKernelUnique_of_value_unique
    (bordered : Bool) (j : ℝ) (central : Fin (n + 1))
    (column : RadialModeL2 D) (p : Fin (n + 1))
    (hvalue : ∀ (q : InnerRadialH1Pair D) (v : RadialModeL2 D) (borderScalar : ℝ),
      q ∈ innerRadialH1Zero D (G.left p) (G.right p) →
      InnerRadialPotentialClass D j (G.left p) (G.right p) q.1 v →
      (if p = central then
        if bordered then ⟪column, q.1⟫_ℝ = 0 else borderScalar = 0
        else True) →
      (∀ r ∈ innerRadialH1Zero D (G.left p) (G.right p),
        innerRadialWeakResidual D q v 0 (if p = central then column else 0) borderScalar r = 0) →
      q.1 = 0 ∧ (p = central → borderScalar = 0)) :
    InnerRadialPieceKernelUnique D G bordered j central column p := by
  intro q v borderScalar hq hv hb heq
  obtain ⟨hval, hs⟩ := hvalue q v borderScalar hq hv hb heq
  have hv0 : v = 0 := hv.eq_zero_of_value_eq_zero hval
  have hg : ⟪q.2, q.2⟫_ℝ = 0 := by
    have he := heq q hq
    simpa only [innerRadialWeakResidual_apply, hval, hv0, inner_zero_left,
      inner_zero_right, mul_zero, add_zero, sub_zero] using he
  have hd : q.2 = 0 := inner_self_eq_zero.mp hg
  exact ⟨Prod.ext hval hd, hv0, hs⟩

end ChainTrace

section BrokenTrace

variable (D : ReferenceData) (hw : Continuous D.w) {n : ℕ}
  (G : InnerRadialChainGeometry D n) {H : Type*}
  [AddCommGroup H] [Module ℝ H]
  (forcing : H →ₗ[ℝ] (Fin (n + 1) → RadialModeL2 D))
  (rowSource : H →ₗ[ℝ] ℝ)

def innerRadialBrokenTrace : InnerRadialBrokenData D n H →ₗ[ℝ]
    EuclideanSpace ℝ (Fin n) :=
  (innerRadialChainTrace D hw G).comp (innerRadialBrokenQ D)

theorem innerRadialBrokenTrace_apply (x : InnerRadialBrokenData D n H) :
    innerRadialBrokenTrace D hw G x = innerRadialChainTrace D hw G x.1.1 := rfl

/-- The concrete broken graph has no zero-source, zero-trace kernel,
as a consequence of the actual local zero-Dirichlet uniqueness facts. -/
theorem innerRadialBrokenSpace_kernel
    (bordered : Bool) (j : ℝ) (central : Fin (n + 1)) (column : RadialModeL2 D)
    (hunique : ∀ p, InnerRadialPieceKernelUnique D G bordered j central column p)
    (x : InnerRadialBrokenData D n H)
    (hx : x ∈ innerRadialBrokenSpace D hw G forcing rowSource bordered j central column)
    (hsource : x.2 = 0) (htrace : innerRadialBrokenTrace D hw G x = 0) :
    x = 0 := by
  obtain ⟨hdom, hpot, hrow, heq⟩ :=
    (mem_innerRadialBrokenSpace D hw G forcing rowSource bordered j central column x).mp hx
  have hzeroTrace : innerRadialChainTrace D hw G x.1.1 = 0 := by
    simpa only [innerRadialBrokenTrace_apply] using htrace
  have hz := innerRadialChainDomain_zero_trace D hw G hdom hzeroTrace
  have hrow0 : if bordered then ⟪column, (x.1.1 central).1⟫_ℝ = 0
      else x.1.2.2 = 0 := by
    rw [hsource, map_zero] at hrow
    cases bordered with
    | false => exact hrow.1
    | true => exact hrow
  have hp (p : Fin (n + 1)) :
      x.1.1 p = 0 ∧ x.1.2.1 p = 0 ∧ (p = central → x.1.2.2 = 0) := by
    apply hunique p (x.1.1 p) (x.1.2.1 p) x.1.2.2 (hz p) (hpot p)
    · by_cases hc : p = central
      · subst p
        simpa only [if_pos rfl, ite_true] using hrow0
      · simp only [if_neg hc]
    · intro r hr
      simpa only [innerRadialChainResidual, hsource, map_zero, Pi.zero_apply] using heq p r hr
  have hq : x.1.1 = 0 := funext (fun p => (hp p).1)
  have hv : x.1.2.1 = 0 := funext (fun p => (hp p).2.1)
  have hs : x.1.2.2 = 0 := (hp central).2.2 rfl
  exact Prod.ext (Prod.ext hq (Prod.ext hv hs)) hsource

end BrokenTrace

end ContinuousFlexibility.Radial
