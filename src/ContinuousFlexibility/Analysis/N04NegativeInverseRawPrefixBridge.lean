import ContinuousFlexibility.Analysis.N04NegativeInverseJetBudget
import ContinuousFlexibility.Analysis.N04NegativeInverseSpatialLinear
import ContinuousFlexibility.Analysis.N04NegativeInversePureJointBounds
import ContinuousFlexibility.Analysis.SmoothDirectionsAffine
import ContinuousFlexibility.Analysis.TameElementaryCalculus

/-!
# From actual forward prefixes to normalized inverse prefixes

The inverse equation is used on its true canonical target. A fixed
affine target normalization is applied only after the implicit estimate.
It changes spatial directions and their coefficient, while preserving
the exact parameter arity, interpolation degree and height factor.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

section AffineInput

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set E} {W Ω : Set PolarPoint} {f : E × PolarPoint → F}

theorem StateAngleWord.negativeInverse_pureSlots_eq {n : ℕ}
    (w : StateAngleWord n) (v : Fin n → E × PolarPoint)
    (hstate : ∀ i, w.isState i = false → (v i).1 = 0)
    (hspatial : ∀ i, w.isState i = true → (v i).2 = 0) :
    (fun i => if w.isState i then ((v i).1, (0 : PolarPoint)) else (0, (v i).2)) = v := by
  funext i
  cases hi : w.isState i with
  | true => simp only [hi, if_true, ← hspatial i hi, Prod.mk.eta]
  | false => simp only [hi, Bool.false_eq_true, if_false, ← hstate i hi, Prod.mk.eta]

/-- Equality of arbitrary genuine towers under a fixed affine change
of the target variable. The original parameter directions are retained. -/
theorem n04NegativeInverse_affineInput_jet
    (J : SmoothDirections (U ×ˢ W) f)
    (B : PolarPoint →L[ℝ] PolarPoint) (c : PolarPoint)
    (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hmap : MapsTo (fun q => c + B q) Ω W)
    (Q : SmoothDirections (U ×ˢ Ω) (fun p => f (p.1, c + B p.2)))
    {z : E} (hz : z ∈ U) {q : PolarPoint} (hq : q ∈ Ω)
    (n : ℕ) (v : Fin n → E × PolarPoint) :
    Q.D n (z, q) v = J.D n (z, c + B q) (fun i => ((v i).1, B (v i).2)) := by
  let L : (E × PolarPoint) →L[ℝ] E × PolarPoint :=
    (ContinuousLinearMap.fst ℝ E PolarPoint).prod
      (B.comp (ContinuousLinearMap.snd ℝ E PolarPoint))
  let a : E × PolarPoint := (0, c)
  have hpoint (p : E × PolarPoint) : a + L p = (p.1, c + B p.2) := by
    simp only [a, L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.mk_add_mk, zero_add]
  have hm : MapsTo (fun p : E × PolarPoint => a + L p) (U ×ˢ Ω) (U ×ˢ W) := by
    intro p hp
    rw [hpoint]
    exact ⟨hp.1, hmap hp.2⟩
  let Q' := (J.compAffine L a (hU.prod hΩ) hm).congrOn
    (fun p _ => congrArg f (hpoint p))
  have he := congrArg (fun A : (E × PolarPoint) [×n]→L[ℝ] F => A v)
    (Q.unique Q' n (z, q) ⟨hz, hq⟩)
  change Q.D n (z, q) v = (J.compAffine L a (hU.prod hΩ) hm).D n (z, q) v at he
  rw [SmoothDirections.compAffine_apply, hpoint] at he
  exact he

theorem n04NegativeInverse_affineInput_norm_le
    (J : SmoothDirections (U ×ˢ W) f)
    (B : PolarPoint →L[ℝ] PolarPoint) (c : PolarPoint)
    (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hmap : MapsTo (fun q => c + B q) Ω W)
    (Q : SmoothDirections (U ×ˢ Ω) (fun p => f (p.1, c + B p.2)))
    {z : E} (hz : z ∈ U) {q : PolarPoint} (hq : q ∈ Ω)
    {n : ℕ} (w : StateAngleWord n) (v : Fin n → E × PolarPoint)
    (hphysical : ∀ i, ‖(v i).2‖ ≤ 1)
    (hstate : ∀ i, w.isState i = false → (v i).1 = 0)
    (hspatial : ∀ i, w.isState i = true → (v i).2 = 0)
    {C T : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T) (hB : ‖B‖ ≤ T)
    (hunit : ∀ y : Fin n → PolarPoint, (∀ i, ‖y i‖ ≤ 1) →
      ‖J.D n (z, c + B q)
        (fun i => if w.isState i then ((v i).1, 0) else (0, y i))‖ ≤ C) :
    ‖Q.D n (z, q) v‖ ≤ C * T ^ w.angleArity := by
  let y : Fin n → PolarPoint := fun i => B (v i).2
  have hy (i : Fin n) : ‖y i‖ ≤ T := by
    calc
      _ ≤ ‖B‖ * ‖(v i).2‖ := B.le_opNorm _
      _ ≤ T * 1 := mul_le_mul hB (hphysical i) (norm_nonneg _) hT
      _ = T := mul_one _
  have heq : (fun i => ((v i).1, B (v i).2)) =
      fun i => if w.isState i then ((v i).1, (0 : PolarPoint)) else (0, y i) := by
    funext i
    cases hi : w.isState i with
    | true => simp only [hi, if_true, hspatial i hi, map_zero]
    | false => simp only [hi, Bool.false_eq_true, if_false, hstate i hi, y]
  rw [n04NegativeInverse_affineInput_jet J B c hU hΩ hmap Q hz hq, heq]
  have hh := n04NegativeInverse_pureSpatial_homogeneous w
    (J.D n (z, c + B q)) (fun i => (v i).1) hunit y
  have hp : w.selectedProduct (fun i => ‖y i‖) ≤ T ^ w.angleArity := by
    simpa only [w.selectedProduct_const] using
      w.selectedProduct_mono (fun i => norm_nonneg (y i)) hy
  exact hh.trans (mul_le_mul_of_nonneg_left hp hC)

end AffineInput

namespace N04NegativeInverseJet

section Prefix

variable {E F₀ : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]

/-- A finite mixed forward prefix in unit spatial directions. This is
the direct output of the physical scalar and vector estimates. -/
def UnitPrefix {D : Set (E × PolarPoint)} {f : E × PolarPoint → F₀}
    (J : SmoothDirections D f) (p : E × PolarPoint)
    (low high : Seminorm ℝ E) (N paramOrder shift : ℕ) (C H R t : ℝ) : Prop :=
  ∀ j : ℕ, 0 < j → j ≤ N → ∀ w : StateAngleWord j,
    w.stateArity ≤ paramOrder → ∀ b : Fin j → E, ∀ y : Fin j → PolarPoint,
    (∀ i, low (b i) ≤ 1) → (∀ i, high (b i) ≤ R) →
    (∀ i, ‖y i‖ ≤ 1) →
    ‖J.D j p (fun i => if w.isState i then (b i, 0) else (0, y i))‖ ≤
      C * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + shift * w.stateArity - 1)

theorem UnitPrefix.homogeneous {D : Set (E × PolarPoint)} {f : E × PolarPoint → F₀}
    {J : SmoothDirections D f} {p : E × PolarPoint}
    {low high : Seminorm ℝ E} {N paramOrder shift : ℕ} {C H R t : ℝ}
    (h : UnitPrefix J p low high N paramOrder shift C H R t)
    (j : ℕ) (hj : 0 < j) (hjN : j ≤ N) (w : StateAngleWord j)
    (hw : w.stateArity ≤ paramOrder) (b : Fin j → E) (y : Fin j → PolarPoint)
    (hlow : ∀ i, low (b i) ≤ 1) (hhigh : ∀ i, high (b i) ≤ R) :
    ‖J.D j p (fun i => if w.isState i then (b i, 0) else (0, y i))‖ ≤
      C * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + shift * w.stateArity - 1) *
          w.selectedProduct (fun i => ‖y i‖) :=
  n04NegativeInverse_pureSpatial_homogeneous w (J.D j p) b
    (fun a ha => h j hj hjN w hw b a hlow hhigh ha) y

theorem UnitPrefix.norm_le {D : Set (E × PolarPoint)} {f : E × PolarPoint → F₀}
    {J : SmoothDirections D f} {p : E × PolarPoint}
    {low high : Seminorm ℝ E} {N paramOrder shift : ℕ} {C H R t : ℝ}
    (h : UnitPrefix J p low high N paramOrder shift C H R t)
    (j : ℕ) (hj : 0 < j) (hjN : j ≤ N) (w : StateAngleWord j)
    (hw : w.stateArity ≤ paramOrder) (v : Fin j → E × PolarPoint)
    (hlow : ∀ i, low (v i).1 ≤ 1) (hhigh : ∀ i, high (v i).1 ≤ R)
    (hphysical : ∀ i, ‖(v i).2‖ ≤ 1)
    (hstate : ∀ i, w.isState i = false → (v i).1 = 0)
    (hspatial : ∀ i, w.isState i = true → (v i).2 = 0) :
    ‖J.D j p v‖ ≤ C * parameterHeightWeight H w.stateArity *
      t ^ (w.angleArity + shift * w.stateArity - 1) := by
  have hh := h j hj hjN w hw (fun i => (v i).1) (fun i => (v i).2)
    hlow hhigh hphysical
  rw [w.negativeInverse_pureSlots_eq v hstate hspatial] at hh
  exact hh

variable {U : Set E} {V W Ω : Set PolarPoint}
  {F G : E × PolarPoint → PolarPoint}

/-- The actual inverse prefix uses only forward unit jets and the
reciprocal actual spatial Jacobian. It does not assume any inverse jet
estimate. Quantitative hypotheses are required only at this point. -/
theorem inverse_unitPrefix_of_jacobian
    (J : SmoothDirections (U ×ˢ V) F) (K : SmoothDirections (U ×ˢ W) G)
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (hmap : MapsTo G (U ×ˢ W) V)
    (hJac : ∀ p ∈ U ×ˢ W, planeJacobian (fun y => F (p.1, y)) (G p) ≠ 0)
    (hright : ∀ p ∈ U ×ˢ W, F (p.1, G p) = p.2)
    (low high : Seminorm ℝ E) (N paramOrder shift : ℕ) (hshift : 1 ≤ shift)
    (p : E × PolarPoint) (hp : p ∈ U ×ˢ W)
    {C I H L R t : ℝ} (hC : 0 ≤ C) (hI : 0 ≤ I)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) (hR : 0 ≤ R) (ht : 0 ≤ t)
    (hdet : |planeJacobian (fun y => F (p.1, y)) (G p)|⁻¹ ≤ I)
    (hforward : UnitPrefix J (p.1, G p) low high N paramOrder shift C H R t) :
    UnitPrefix K p low high N paramOrder shift
      (n04NegativeInverse_prefixMajorant (2 * C * I) C L N) H R t := by
  intro n hn hnN w hw b y hl hh hy
  let A := spatialInverse J G
  have hAc : ContinuousOn A (U ×ˢ W) :=
    spatialInverse_continuousOn_of_jacobian J K.continuousOn hmap hJac
  have hleft (x : E × PolarPoint) (hx : x ∈ U ×ˢ W) (a : PolarPoint) :
      A x (J.D 1 (x.1, G x) (fun _ : Fin 1 => (0, a))) = a :=
    spatialInverse_left_of_jacobian J x ⟨hx.1, hmap hx⟩ (hJac x hx) a
  have hfirst (a : PolarPoint) (ha : ‖a‖ ≤ 1) :
      ‖J.D 1 (p.1, G p) (fun _ : Fin 1 => (0, a))‖ ≤ C := by
    let w₁ : StateAngleWord 1 := .angle .nil
    have h := hforward 1 (by omega) (by omega) w₁ (Nat.zero_le paramOrder)
      (fun _ => 0) (fun _ => a)
      (fun _ => by simp only [map_zero, zero_le_one])
      (fun _ => by simpa only [map_zero] using hR) (fun _ => ha)
    have he : (fun i : Fin 1 => if w₁.isState i then ((0 : E), (0 : PolarPoint))
        else (0, a)) = fun _ : Fin 1 => ((0 : E), a) := by
      funext i
      rw [Fin.eq_zero i]
      rfl
    rw [he] at h
    simpa only [w₁, StateAngleWord.stateArity, StateAngleWord.angleArity,
      parameterHeightWeight, if_true, Nat.mul_zero, Nat.add_zero, Nat.sub_self,
      pow_zero, mul_one] using h
  have hApoint : ‖A p‖ ≤ 2 * C * I :=
    spatialInverse_norm_le J p ⟨hp.1, hmap hp⟩ (hJac p hp) hC hdet hfirst
  apply prefix_norm_le J K hU hV hW hmap A hAc hleft hright low high
    N paramOrder shift hshift p hp (mul_nonneg (mul_nonneg (by norm_num) hC) hI)
    hC hH hHL hL hR ht hApoint hforward.homogeneous n hn hnN w hw
  · intro i
    cases hi : w.isState i <;> simp only [hi, Bool.false_eq_true, if_false, if_true]
    · simpa only [map_zero] using (zero_le_one : (0 : ℝ) ≤ 1)
    · exact hl i
  · intro i
    cases hi : w.isState i <;> simp only [hi, Bool.false_eq_true, if_false, if_true]
    · simpa only [map_zero] using hR
    · exact hh i
  · intro i
    cases hi : w.isState i <;> simp only [hi, Bool.false_eq_true, if_false, if_true]
    · exact hy i
    · simp only [norm_zero, zero_le_one]
  · intro i hi
    simp only [hi, Bool.false_eq_true, if_false]
  · intro i hi
    simp only [hi, if_true]

/-- Fixed affine target coordinates cost one operator norm per spatial
slot, after the genuine implicit inverse estimate has been proved. -/
theorem normalized_inverse_prefix_norm_le
    (J : SmoothDirections (U ×ˢ V) F) (K : SmoothDirections (U ×ˢ W) G)
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W) (hΩ : IsOpen Ω)
    (hmap : MapsTo G (U ×ˢ W) V)
    (hJac : ∀ p ∈ U ×ˢ W, planeJacobian (fun y => F (p.1, y)) (G p) ≠ 0)
    (hright : ∀ p ∈ U ×ˢ W, F (p.1, G p) = p.2)
    (B : PolarPoint →L[ℝ] PolarPoint) (c : PolarPoint)
    (hBmap : MapsTo (fun q => c + B q) Ω W)
    (Q : SmoothDirections (U ×ˢ Ω) (fun p => G (p.1, c + B p.2)))
    (low high : Seminorm ℝ E) (N paramOrder shift : ℕ) (hshift : 1 ≤ shift)
    {z : E} (hz : z ∈ U) {q : PolarPoint} (hq : q ∈ Ω)
    {C I T H L R t : ℝ} (hC : 0 ≤ C) (hI : 0 ≤ I) (hT : 0 ≤ T)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) (hR : 0 ≤ R) (ht : 0 ≤ t)
    (hdet : |planeJacobian (fun y => F (z, y)) (G (z, c + B q))|⁻¹ ≤ I)
    (hB : ‖B‖ ≤ T)
    (hforward : UnitPrefix J (z, G (z, c + B q)) low high N paramOrder shift C H R t)
    (n : ℕ) (hn : 0 < n) (hnN : n ≤ N)
    (w : StateAngleWord n) (hw : w.stateArity ≤ paramOrder) (v : Fin n → E × PolarPoint)
    (hlow : ∀ i, low (v i).1 ≤ 1) (hhigh : ∀ i, high (v i).1 ≤ R)
    (hphysical : ∀ i, ‖(v i).2‖ ≤ 1)
    (hstate : ∀ i, w.isState i = false → (v i).1 = 0)
    (hspatial : ∀ i, w.isState i = true → (v i).2 = 0) :
    ‖Q.D n (z, q) v‖ ≤
      (n04NegativeInverse_prefixMajorant (2 * C * I) C L N * T ^ w.angleArity) *
        parameterHeightWeight H w.stateArity *
          t ^ (w.angleArity + shift * w.stateArity - 1) := by
  have hK := inverse_unitPrefix_of_jacobian J K hU hV hW hmap hJac hright
    low high N paramOrder shift hshift (z, c + B q) ⟨hz, hBmap hq⟩
    hC hI hH hHL hL hR ht hdet hforward
  have hM : 0 ≤ n04NegativeInverse_prefixMajorant (2 * C * I) C L N :=
    zero_le_one.trans (n04NegativeInverse_prefixMajorant_one_le
      (mul_nonneg (mul_nonneg (by norm_num) hC) hI) hC (zero_le_one.trans hL) N)
  have hh := n04NegativeInverse_affineInput_norm_le K B c hU hΩ hBmap Q hz hq
    w v hphysical hstate hspatial
    (mul_nonneg (mul_nonneg hM (parameterHeightWeight_nonneg hH _)) (pow_nonneg ht _))
    hT hB (fun y hy => hK n hn hnN w hw (fun i => (v i).1) y hlow hhigh hy)
  exact hh.trans_eq (by ring)

end Prefix

section Scalar

variable {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {U : Set E} {V W Ω : Set PolarPoint}
  {F G : E × PolarPoint → PolarPoint} {f : E × PolarPoint → ℝ}

theorem scalar_prefix_norm_le
    (J : SmoothDirections (U ×ˢ V) f) (K : SmoothDirections (U ×ˢ W) G)
    (hmap : MapsTo G (U ×ˢ W) V)
    (Q : SmoothDirections (U ×ˢ W) (fun p => f (p.1, G p)))
    (low high : Seminorm ℝ E) (N paramOrder shift : ℕ) (hshift : 1 ≤ shift)
    (p : E × PolarPoint) (hp : p ∈ U ×ˢ W)
    {C M H L R t : ℝ} (hC : 0 ≤ C) (hM : 1 ≤ M)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) (hR : 0 ≤ R) (ht : 0 ≤ t)
    (hforward : UnitPrefix J (p.1, G p) low high N paramOrder shift C H R t)
    (hinverse : UnitPrefix K p low high N paramOrder shift M H R t)
    (n : ℕ) (hn : 0 < n) (hnN : n ≤ N)
    (w : StateAngleWord n) (hw : w.stateArity ≤ paramOrder) (v : Fin n → E × PolarPoint)
    (hlow : ∀ i, low (v i).1 ≤ 1) (hhigh : ∀ i, high (v i).1 ≤ R)
    (hphysical : ∀ i, ‖(v i).2‖ ≤ 1)
    (hstate : ∀ i, w.isState i = false → (v i).1 = 0)
    (hspatial : ∀ i, w.isState i = true → (v i).2 = 0) :
    ‖Q.D n p v‖ ≤ n04NegativeInverse_partitionMajorant C M L n *
      parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + shift * w.stateArity - 1) := by
  exact scalar_graph_norm_le J K hmap Q low high n paramOrder shift hn hshift p hp
    hC hM hH hHL hL hR ht
    (fun j hj hjn => hforward.homogeneous j hj (hjn.trans hnN))
    (fun j hj hjn => hinverse.norm_le j hj (hjn.trans hnN))
    w hw v hlow hhigh hphysical hstate hspatial

/-- The normalized scalar composition is estimated from the same
forward and actual inverse prefixes. This is the pulled-height bridge. -/
theorem normalized_scalar_prefix_norm_le
    (J : SmoothDirections (U ×ˢ V) F) (K : SmoothDirections (U ×ˢ W) G)
    (Jf : SmoothDirections (U ×ˢ V) f)
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W) (hΩ : IsOpen Ω)
    (hmap : MapsTo G (U ×ˢ W) V)
    (hJac : ∀ p ∈ U ×ˢ W, planeJacobian (fun y => F (p.1, y)) (G p) ≠ 0)
    (hright : ∀ p ∈ U ×ˢ W, F (p.1, G p) = p.2)
    (B : PolarPoint →L[ℝ] PolarPoint) (c : PolarPoint)
    (hBmap : MapsTo (fun q => c + B q) Ω W)
    (Qf : SmoothDirections (U ×ˢ W) (fun p => f (p.1, G p)))
    (Q : SmoothDirections (U ×ˢ Ω) (fun p => f (p.1, G (p.1, c + B p.2))))
    (low high : Seminorm ℝ E) (N paramOrder shift : ℕ) (hshift : 1 ≤ shift)
    {z : E} (hz : z ∈ U) {q : PolarPoint} (hq : q ∈ Ω)
    {C I T H L R t : ℝ} (hC : 0 ≤ C) (hI : 0 ≤ I) (hT : 0 ≤ T)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) (hR : 0 ≤ R) (ht : 0 ≤ t)
    (hdet : |planeJacobian (fun y => F (z, y)) (G (z, c + B q))|⁻¹ ≤ I)
    (hB : ‖B‖ ≤ T)
    (hforward : UnitPrefix J (z, G (z, c + B q)) low high N paramOrder shift C H R t)
    (hscalar : UnitPrefix Jf (z, G (z, c + B q)) low high N paramOrder shift C H R t)
    (n : ℕ) (hn : 0 < n) (hnN : n ≤ N)
    (w : StateAngleWord n) (hw : w.stateArity ≤ paramOrder) (v : Fin n → E × PolarPoint)
    (hlow : ∀ i, low (v i).1 ≤ 1) (hhigh : ∀ i, high (v i).1 ≤ R)
    (hphysical : ∀ i, ‖(v i).2‖ ≤ 1)
    (hstate : ∀ i, w.isState i = false → (v i).1 = 0)
    (hspatial : ∀ i, w.isState i = true → (v i).2 = 0) :
    ‖Q.D n (z, q) v‖ ≤
      (n04NegativeInverse_partitionMajorant C
        (n04NegativeInverse_prefixMajorant (2 * C * I) C L N) L n * T ^ w.angleArity) *
        parameterHeightWeight H w.stateArity *
          t ^ (w.angleArity + shift * w.stateArity - 1) := by
  let M := n04NegativeInverse_prefixMajorant (2 * C * I) C L N
  have hM : 1 ≤ M := n04NegativeInverse_prefixMajorant_one_le
    (mul_nonneg (mul_nonneg (by norm_num) hC) hI) hC (zero_le_one.trans hL) N
  have hK := inverse_unitPrefix_of_jacobian J K hU hV hW hmap hJac hright
    low high N paramOrder shift hshift (z, c + B q) ⟨hz, hBmap hq⟩
    hC hI hH hHL hL hR ht hdet hforward
  have hunit (y : Fin n → PolarPoint) (hy : ∀ i, ‖y i‖ ≤ 1) :
      ‖Qf.D n (z, c + B q)
        (fun i => if w.isState i then ((v i).1, 0) else (0, y i))‖ ≤
      n04NegativeInverse_partitionMajorant C M L n *
        parameterHeightWeight H w.stateArity *
          t ^ (w.angleArity + shift * w.stateArity - 1) := by
    apply scalar_prefix_norm_le Jf K hmap Qf low high N paramOrder shift hshift
      (z, c + B q) ⟨hz, hBmap hq⟩ hC hM hH hHL hL hR ht hscalar hK n hn hnN w hw
    · intro i
      cases hi : w.isState i <;> simp only [hi, Bool.false_eq_true, if_false, if_true]
      · simpa only [map_zero] using (zero_le_one : (0 : ℝ) ≤ 1)
      · exact hlow i
    · intro i
      cases hi : w.isState i <;> simp only [hi, Bool.false_eq_true, if_false, if_true]
      · simpa only [map_zero] using hR
      · exact hhigh i
    · intro i
      cases hi : w.isState i <;> simp only [hi, Bool.false_eq_true, if_false, if_true]
      · exact hy i
      · simp only [norm_zero, zero_le_one]
    · intro i hi
      simp only [hi, Bool.false_eq_true, if_false]
    · intro i hi
      simp only [hi, if_true]
  have hQ0 : 0 ≤ n04NegativeInverse_partitionMajorant C M L n :=
    n04NegativeInverse_partitionMajorant_nonneg hC (zero_le_one.trans hM)
      (zero_le_one.trans hL) n
  have hh := n04NegativeInverse_affineInput_norm_le Qf B c hU hΩ hBmap Q hz hq
    w v hphysical hstate hspatial
    (mul_nonneg (mul_nonneg hQ0 (parameterHeightWeight_nonneg hH _)) (pow_nonneg ht _))
    hT hB hunit
  exact hh.trans_eq (by ring)

end Scalar

end N04NegativeInverseJet
end ContinuousFlexibility.Analysis
