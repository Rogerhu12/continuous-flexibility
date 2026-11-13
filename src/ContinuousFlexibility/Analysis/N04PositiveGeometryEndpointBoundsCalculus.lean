import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsCircleInverse
import ContinuousFlexibility.Analysis.TameFixedBaseCompositionBounds

/-!
# Fixed-base calculus for genuine endpoint towers

This records the quantifier order needed when the actual endpoint flow
is followed by positive circle inversion. Products and linear maps keep
the same common low order. The composition step uses the existing
ordered-partition theorem and selects its new low order before every
parameter derivative order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

section Bounds

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]

/-- A single low parameter order for all genuine directional jets. -/
def N04EndpointFixedBaseBounds
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    {U : Set E} {f : E → F} (J : SmoothDirections U f) : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, ∃ ell : ℕ, ∀ R : ℝ, 0 ≤ R →
    ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ U, p B x ≤ R →
      ∀ v : Fin n → E, q s (J.D n x v) ≤ K * tameJetSize p n s ell B x v

theorem N04EndpointFixedBaseBounds.congr
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U : Set E} {f g : E → F} {J : SmoothDirections U f}
    (hJ : N04EndpointFixedBaseBounds p q J) (hfg : EqOn f g U) :
    N04EndpointFixedBaseBounds p q (J.congrOn hfg) := hJ

theorem N04EndpointFixedBaseBounds.postLinear
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set E} {f : E → F} {J : SmoothDirections U f}
    (hJ : N04EndpointFixedBaseBounds p q J) (L : F →L[ℝ] G) (d : ℕ)
    (hL : ∀ s, ∃ A : ℝ, 0 ≤ A ∧ ∀ y, r s (L y) ≤ A * q (s + d) y) :
    N04EndpointFixedBaseBounds p r (solveSmoothDirectionsPostcomp J L) := by
  refine hJ.elim ?_
  intro B hB
  refine ⟨B, fun n => ?_⟩
  refine (hB n).elim ?_
  intro ell hell
  refine ⟨d + ell, fun R hR s => ?_⟩
  refine (hL s).elim ?_
  intro A hA
  refine (hell R hR (s + d)).elim ?_
  intro K hK
  refine ⟨A * K, mul_nonneg hA.1 hK.1, fun x hx hxR v => ?_⟩
  have hb := (hA.2 (J.D n x v)).trans
    (mul_le_mul_of_nonneg_left (hK.2 x hx hxR v) hA.1)
  change r s (L (J.D n x v)) ≤ _
  simpa only [tameJetSize, Nat.add_assoc, mul_assoc] using hb

end Bounds

section Linear

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

theorem n04PositiveGeometry_endpointBounds_linear
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (L : E →L[ℝ] F) {U : Set E} (hU : IsOpen U)
    (hL : ∀ s, ∃ A : ℝ, 0 ≤ A ∧ ∀ y, q s (L y) ≤ A * p s y) :
    N04EndpointFixedBaseBounds p q (smoothDirectionsLinearOn L hU) := by
  refine ⟨0, fun n => ⟨0, fun R _ s => ?_⟩⟩
  refine (hL s).elim ?_
  intro A hA
  refine ⟨A, hA.1, fun x _ _ v => ?_⟩
  have hjet : (smoothDirectionsLinearOn L hU).D n x v =
      continuousLinearJets L n x v := by
    simpa only [ContinuousLinearMap.id_apply] using
      n04PositiveGeometry_endpointBounds_compLinear_apply (smoothDirectionsLinear L)
        (ContinuousLinearMap.id ℝ E) hU (fun _ _ => mem_univ _) n x v
  rw [hjet]
  cases n with
  | zero =>
      rw [tameJetSize_zero]
      change q s (L x) ≤ A * (1 + p s x)
      exact (hA.2 x).trans (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left zero_le_one) hA.1)
  | succ n =>
      cases n with
      | zero =>
          rw [tameJetSize_one]
          change q s (L (v 0)) ≤ A * ((1 + p s x) * p 0 (v 0) + p s (v 0))
          exact (hA.2 (v 0)).trans (mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_left (mul_nonneg
              (add_nonneg zero_le_one (apply_nonneg _ _)) (apply_nonneg _ _))) hA.1)
      | succ n =>
          change q s 0 ≤ A * tameJetSize p (n + 2) s 0 0 x v
          rw [map_zero]
          exact mul_nonneg hA.1 (tameJetSize_nonneg _ _ _ _ _ _ _)

theorem N04EndpointFixedBaseBounds.of_unique
    [T2Space F] {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U : Set E} {f : E → F} {J : SmoothDirections U f}
    (hJ : N04EndpointFixedBaseBounds p q J) (K : SmoothDirections U f) :
    N04EndpointFixedBaseBounds p q K := by
  refine hJ.elim ?_
  intro B hB
  refine ⟨B, fun n => ?_⟩
  refine (hB n).elim ?_
  intro ell hell
  refine ⟨ell, fun R hR s => ?_⟩
  refine (hell R hR s).elim ?_
  intro A hA
  refine ⟨A, hA.1, fun x hx hxR v => ?_⟩
  exact (congrArg (fun Jn => q s (Jn v)) (K.unique J n x hx)).trans_le
    (hA.2 x hx hxR v)

end Linear

section Product

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G]

theorem N04EndpointFixedBaseBounds.prod
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    (hp : Monotone p) {U : Set E} {f : E → F} {g : E → G}
    {J : SmoothDirections U f} {K : SmoothDirections U g}
    (hJ : N04EndpointFixedBaseBounds p q J) (hK : N04EndpointFixedBaseBounds p r K) :
    N04EndpointFixedBaseBounds p (pairGrading q r) (smoothDirectionsProd J K) := by
  refine hJ.elim ?_
  intro BJ hBJ
  refine hK.elim ?_
  intro BK hBK
  let B := max BJ BK
  refine ⟨B, fun n => ?_⟩
  refine (hBJ n).elim ?_
  intro ellJ hJell
  refine (hBK n).elim ?_
  intro ellK hKell
  let ell := max ellJ ellK
  refine ⟨ell, fun R hR s => ?_⟩
  refine (hJell R hR s).elim ?_
  intro AJ hAJ
  refine (hKell R hR s).elim ?_
  intro AK hAK
  refine ⟨AJ + AK, add_nonneg hAJ.1 hAK.1, fun x hx hxR v => ?_⟩
  have hj := (hAJ.2 x hx ((hp (le_max_left _ _) x).trans hxR) v).trans
    (mul_le_mul_of_nonneg_left
      (tameJetSize_mono hp (le_max_left _ _) (le_max_left _ _) n s x v) hAJ.1)
  have hk := (hAK.2 x hx ((hp (le_max_right _ _) x).trans hxR) v).trans
    (mul_le_mul_of_nonneg_left
      (tameJetSize_mono hp (le_max_right _ _) (le_max_right _ _) n s x v) hAK.1)
  change q s (J.D n x v) + r s (K.D n x v) ≤ _
  exact (add_le_add hj hk).trans_eq (add_mul AJ AK (tameJetSize p n s ell B x v)).symm

end Product

section CircleComposition

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  {T : MaterialData} {γ : ℝ} {M : CircleModelData}

theorem N04EndpointFixedBaseBounds.compCircle
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    (hp : Monotone p) (hI : HasInterpolation (pairGrading realGrading p))
    (hM : IsCircleModel T γ M)
    {U : Set E} {V : Set F} {f : E → F} {g : F → M.Space}
    {J : SmoothDirections U f} {K : SmoothDirections V g}
    (hJ : N04EndpointFixedBaseBounds p q J)
    (hK : N04EndpointFixedBaseBounds q M.grading K) (hmap : MapsTo f U V) :
    N04EndpointFixedBaseBounds p M.grading (J.compCircle hM K hmap) := by
  classical
  refine hJ.elim ?_
  intro BJ hBJ
  refine hK.elim ?_
  intro BK hBK
  let d : ℕ → ℕ := fun n => (hBJ n).choose
  let e : ℕ → ℕ := fun n => (hBK n).choose
  have hinner : ∀ n R, 0 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (_ : Unit) x, x ∈ U → p BJ x ≤ R → ∀ v : Fin n → E,
        q s (J.D n x v) ≤ C * tameJetSize p n s (d n) BJ x v := by
    intro n R hR s
    exact ((hBJ n).choose_spec R hR s).elim
      (fun C hC => ⟨C, hC.1, fun _ => hC.2⟩)
  have houter : ∀ n R, 0 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (_ : Unit) y, y ∈ V → q BK y ≤ R → ∀ v : Fin n → F,
        M.grading s (K.D n y v) ≤ C * tameJetSize q n s (e n) BK y v := by
    intro n R hR s
    exact ((hBK n).choose_spec R hR s).elim
      (fun C hC => ⟨C, hC.1, fun _ => hC.2⟩)
  refine (projectiveCompositionJets_fixedBase_oneHigh p q M.grading hp hI
    (fun _ : Unit => J) (fun _ : Unit => K) BJ BK d e hinner houter
    (fun _ => hmap)).elim ?_
  intro B hB
  refine ⟨B, fun n => ?_⟩
  refine (hB.2 n).elim ?_
  intro ell hell
  refine ⟨ell, fun R hR s => ?_⟩
  refine (hell R hR s).elim ?_
  intro C hC
  exact ⟨C, hC.1, fun x hx hxR v => hC.2 () x hx hxR v⟩

end CircleComposition

end ContinuousFlexibility.Analysis
