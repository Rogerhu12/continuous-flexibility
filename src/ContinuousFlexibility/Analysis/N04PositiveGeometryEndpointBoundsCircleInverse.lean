module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsLinear
public import ContinuousFlexibility.Analysis.CirclePositiveInverseFixedBaseBounds
public import ContinuousFlexibility.Analysis.CircleCompositionUniformBounds
public import ContinuousFlexibility.Analysis.CircleSmoothDirectionsOperations

/-!
# The actual inverse endpoint circle on one fixed low-order ball

The inverse displacement is the negative diagonal of the genuine
positive inverse-composition operator. Restricting that operator along
`x ↦ (L x, -L x)` keeps its low order and derivative loss. In particular,
the low order is selected before every parameter derivative order.

The only condition on the parameter map is a grading contraction; the
only geometric condition is a positive angular derivative lower bound.
No inverse-jet estimate is an input to the result.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

theorem n04PositiveGeometry_endpointBounds_compLinear_apply
    {E F G : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [IsTopologicalAddGroup F]
    [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
    {U : Set F} {V : Set E} {f : F → G}
    (J : SmoothDirections U f) (L : E →L[ℝ] F)
    (hV : IsOpen V) (hmap : MapsTo L V U)
    (n : ℕ) (x : E) (v : Fin n → E) :
    (J.compLinear L hV hmap).D n x v =
      J.D n (L x) (fun i => L (v i)) := by
  change (J.D n (0 + L x)).compContinuousLinearMap (fun _ => L) v = _
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, zero_add]

/-- Genuine inverse displacement jets along a grading-contracting
linear parameter map have one common low order at all parameter orders.
The estimate applies to every actual directional tower of that map. -/
theorem n04PositiveGeometry_endpointBounds_inverseLinear_oneHigh
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
    (hM : IsCircleModel T γ M) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hI : HasInterpolation M.grading)
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (p : ℕ → Seminorm ℝ E) (L : E →L[ℝ] M.Space)
    (hL : ∀ s x, M.grading s (L x) ≤ p s x)
    {U : Set E} (hU : IsOpen U) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ x ∈ U, ∀ m θ,
      a ≤ deriv (circleAffineLift (fun _ => 0) (M.decode (L x)) 1 m) θ) :
    ∃ B : ℕ, ∀ n : ℕ, ∃ loss : ℕ, ∀ R : ℝ, 1 ≤ R →
      ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧
        ∀ J : SmoothDirections U
          (fun x => circlePositiveInversePerturbation hM hT hD hγ (fun _ => 0) (L x)),
        ∀ x ∈ U, p B x ≤ R → ∀ v : Fin n → E,
          M.grading s (J.D n x v) ≤ K * tameJetSize p n s loss B x v := by
  let JF := (exists_circleChartComposition_uniform_oneHigh
    hM hT hD hγ hI (fun _ => 0)).choose
  let JP := (smoothTameOn_circlePositiveInverseComposeLinear
    hM hT hD hγ hI (fun _ => 0)).choose
  let LP : E →L[ℝ] (M.Space × M.Space) := L.prod (-L)
  have hLP (s : ℕ) (x : E) :
      pairGrading M.grading M.grading s (LP x) ≤ 2 * p s x := by
    change M.grading s (L x) + M.grading s (-L x) ≤ _
    rw [map_neg_eq_map]
    linarith only [hL s x]
  have hmap : MapsTo LP U (circlePositiveLiftDomain M ×ˢ univ) := by
    intro x hx
    refine ⟨?_, mem_univ _⟩
    exact (circlePositiveLiftDomain_iff hM (fun _ => 0) (L x)).mpr
      (fun m θ => ha.trans_le (hlower x hx m θ))
  let KJ : SmoothDirections U
      (fun x => circlePositiveInversePerturbation hM hT hD hγ (fun _ => 0) (L x)) :=
    (JP.compLinear LP hU hmap).congrOn (fun x _ =>
      (circlePositiveInverseComposeLinear hM hT hD hγ (fun _ => 0) (L x)).map_neg (L x))
  refine (circlePositiveInverseComposeLinear_fixedBase_oneHigh
    hD hT hγ hM hI JF JP a ha).elim ?_
  intro B hB
  refine ⟨B, fun n => ?_⟩
  refine (hB n).elim ?_
  intro loss hloss
  refine ⟨loss, fun R hR s => ?_⟩
  have h2R : 1 ≤ 2 * R := by linarith only [hR]
  refine (hloss (2 * R) h2R s).elim ?_
  intro C hC
  refine ⟨C * (2 : ℝ) ^ (n + 1),
    mul_nonneg hC.1 (pow_nonneg (by norm_num) _), ?_⟩
  intro J x hx hxR v
  have hxe : pairGrading M.grading M.grading B (LP x) ≤ 2 * R :=
    (hLP B x).trans (mul_le_mul_of_nonneg_left hxR (by norm_num))
  have hb := hC.2 (fun _ => 0) JP (LP x) (hlower x hx) hxe
    (fun i => LP (v i))
  have hweight := n04PositiveGeometry_endpointBounds_linearImage p
    (pairGrading M.grading M.grading) LP (by norm_num : (1 : ℝ) ≤ 2)
    hLP n s loss B x v
  have hjet : J.D n x v = JP.D n (LP x) (fun i => LP (v i)) := by
    exact (congrArg (fun A => A v) (J.unique KJ n x hx)).trans
      (n04PositiveGeometry_endpointBounds_compLinear_apply JP LP hU hmap n x v)
  calc
    _ = M.grading s (JP.D n (LP x) (fun i => LP (v i))) := congrArg (M.grading s) hjet
    _ ≤ C * tameJetSize (pairGrading M.grading M.grading) n s loss B
        (LP x) (fun i => LP (v i)) := hb
    _ ≤ C * ((2 : ℝ) ^ (n + 1) * tameJetSize p n s loss B x v) :=
      mul_le_mul_of_nonneg_left hweight hC.1
    _ = _ := by ring

end ContinuousFlexibility.Analysis
