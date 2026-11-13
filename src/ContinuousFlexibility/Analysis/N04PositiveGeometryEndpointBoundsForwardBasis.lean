import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsAxisJets

/-!
# Finite forward chart words without an angular lift value

Every positive-order chart word uses either a radial trace of the odd
power and an even trace, or a derivative of the forward label slope.
The pure angular case therefore needs no bound on the label itself.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

def n04PositiveGeometry_forwardBasisValue
    (κ : ℝ) (O : ℕ → ℝ → ℝ) (E : Fin 8 → ℝ → ℝ) (B : ℝ → ℝ)
    (a b : ℕ) : ℝ → PolarPoint :=
  if a = 0 then fun θ => (0, iteratedDeriv (b - 1) B θ)
  else if ha : a ≤ 4 then fun θ =>
    ((a : ℝ) * κ * iteratedDeriv b (O (a - 1)) θ,
      iteratedDeriv b (E ⟨a - 1, by omega⟩) θ)
  else fun _ => 0

variable {X : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {U : Set X} {O : ℕ → X × ℝ → ℝ} {E : Fin 8 → X × ℝ → ℝ}
  {B : X × ℝ → ℝ}

def n04PositiveGeometry_forwardBasis_directions
    (JO : ∀ j, j ≤ 3 → SmoothDirections (U ×ˢ univ) (O j))
    (JE : ∀ j, SmoothDirections (U ×ˢ univ) (E j))
    (JB : SmoothDirections (U ×ˢ univ) B)
    (κ : ℝ) (a b : ℕ) (ha : a ≤ 4) :
    SmoothDirections (U ×ˢ univ) (fun y =>
      n04PositiveGeometry_forwardBasisValue κ
        (fun j θ => O j (y.1, θ)) (fun j θ => E j (y.1, θ))
        (fun θ => B (y.1, θ)) a b y.2) := by
  by_cases ha0 : a = 0
  · exact (smoothDirectionsProd (smoothDirections_constant JB.open_domain (0 : ℝ))
      (smoothDirections_angularIterate JB (b - 1))).congr
        (fun y _ => by simp only [n04PositiveGeometry_forwardBasisValue, if_pos ha0])
  · have hj : a - 1 ≤ 3 := by omega
    let J := smoothDirections_angularIterate (JO (a - 1) hj) b
    let L : ℝ →L[ℝ] ℝ := ((a : ℝ) * κ) • ContinuousLinearMap.id ℝ ℝ
    exact (smoothDirectionsProd (smoothDirections_postcompCLM J L)
      (smoothDirections_angularIterate (JE ⟨a - 1, by omega⟩) b)).congr
        (fun y _ => by simp only [n04PositiveGeometry_forwardBasisValue,
          if_neg ha0, dif_pos ha, Function.comp_apply, L, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.id_apply, smul_eq_mul])

/-- At most four intrinsic angular derivatives are spent. Scaling the
radial trace costs only the fixed coefficient and its radial index. -/
theorem n04PositiveGeometry_forwardBasis_word_bound
    (JO : ∀ j, j ≤ 3 → SmoothDirections (U ×ˢ univ) (O j))
    (JE : ∀ j, SmoothDirections (U ×ˢ univ) (E j))
    (JB : SmoothDirections (U ×ˢ univ) B)
    (κ : ℝ) (a b : ℕ) (ha : a ≤ 4) (hb : b ≤ 4)
    (Q : SmoothDirections (U ×ˢ univ) (fun y =>
      n04PositiveGeometry_forwardBasisValue κ
        (fun j θ => O j (y.1, θ)) (fun j θ => E j (y.1, θ))
        (fun θ => B (y.1, θ)) a b y.2))
    {K s d : ℕ} {x : X} (hx : x ∈ U) (hU : Convex ℝ U)
    {θ : ℝ} {P : X → Prop} (hP : P 0)
    {M H t : ℝ} {shift : ℕ} (hM : 0 ≤ M) (hH : 0 ≤ H) (ht : 1 ≤ t)
    (hO : ∀ j (hj : j ≤ 3),
      N04BoundaryWordBounds (JO j hj) K s (d + 4) x θ P M H t shift)
    (hE : ∀ j, N04BoundaryWordBounds (JE j) K s (d + 4) x θ P M H t shift)
    (hB : N04BoundaryWordBounds JB K s (d + 4) x θ P M H t shift) :
    N04BoundaryWordBounds Q K s d x θ P ((1 + 4 * |κ|) * M) H t shift := by
  have hC : 1 ≤ 1 + 4 * |κ| := le_add_of_nonneg_right (by positivity)
  have hcost : M ≤ (1 + 4 * |κ|) * M := le_mul_of_one_le_left hM hC
  by_cases ha0 : a = 0
  · have hreserve := hB.reserve hM hH ht
      (Nat.add_le_add_left (show b - 1 ≤ 4 by omega) d)
    have hs := N04BoundaryWordBounds.angularIterate (b - 1)
      (d := d) hreserve hx hU hP
    have hz := (hs.scale 0).enlarge hH (zero_le_one.trans ht)
      (show |(0 : ℝ)| * M ≤ (1 + 4 * |κ|) * M by
        simpa only [abs_zero, zero_mul] using hM.trans hcost)
    exact (hz.prod (hs.enlarge hH (zero_le_one.trans ht) hcost)).congr hx
      (fun y _ => by
        rw [n04PositiveGeometry_forwardBasisValue, if_pos ha0]
        apply Prod.ext
        · simp only [Function.comp_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.id_apply, smul_eq_mul, zero_mul]
        · rfl)
  · have hj : a - 1 ≤ 3 := by omega
    have hOr := (hO (a - 1) hj).reserve hM hH ht (Nat.add_le_add_left hb d)
    have hEr := (hE ⟨a - 1, by omega⟩).reserve hM hH ht
      (Nat.add_le_add_left hb d)
    have ho := N04BoundaryWordBounds.angularIterate b (d := d) hOr hx hU hP
    have he := N04BoundaryWordBounds.angularIterate b (d := d) hEr hx hU hP
    have haR : (a : ℝ) ≤ 4 := by exact_mod_cast ha
    have hcoeff : |(a : ℝ) * κ| ≤ 1 + 4 * |κ| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg a)]
      exact (mul_le_mul_of_nonneg_right haR (abs_nonneg κ)).trans
        (le_add_of_nonneg_left zero_le_one)
    have ho' := (ho.scale ((a : ℝ) * κ)).enlarge hH (zero_le_one.trans ht)
      (mul_le_mul_of_nonneg_right hcoeff hM)
    exact (ho'.prod (he.enlarge hH (zero_le_one.trans ht) hcost)).congr hx
      (fun y _ => by simp only [n04PositiveGeometry_forwardBasisValue,
        if_neg ha0, dif_pos ha, Function.comp_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul])

def n04PositiveGeometry_forwardJet_directions
    (JO : ∀ j, j ≤ 3 → SmoothDirections (U ×ˢ univ) (O j))
    (JE : ∀ j, SmoothDirections (U ×ˢ univ) (E j))
    (JB : SmoothDirections (U ×ˢ univ) B) (κ : ℝ)
    {n : ℕ} (hn : n ≤ 4) (A : X × ℝ → PolarPoint [×n]→L[ℝ] PolarPoint)
    (he : ∀ w : Fin n → Fin 2, ∀ y ∈ U ×ˢ (univ : Set ℝ),
      A y (fun i => cylinderBasisVector (w i)) =
        n04PositiveGeometry_forwardBasisValue κ
          (fun j θ => O j (y.1, θ)) (fun j θ => E j (y.1, θ))
          (fun θ => B (y.1, θ)) (n04PositiveGeometry_planeWordRadial w)
          (n04PositiveGeometry_planeWordAngular w) y.2) :
    SmoothDirections (U ×ˢ univ) A := by
  apply n04PositiveGeometry_planeBasis_directions n A
  intro w
  have ha : n04PositiveGeometry_planeWordRadial w ≤ 4 := by
    have hc := n04PositiveGeometry_planeWord_orders w
    omega
  exact (n04PositiveGeometry_forwardBasis_directions JO JE JB κ
    (n04PositiveGeometry_planeWordRadial w) (n04PositiveGeometry_planeWordAngular w) ha).congr
    (fun y hy => (he w y hy).symm)

theorem N04BoundaryWordBounds.of_forwardBasis
    (JO : ∀ j, j ≤ 3 → SmoothDirections (U ×ˢ univ) (O j))
    (JE : ∀ j, SmoothDirections (U ×ˢ univ) (E j))
    (JB : SmoothDirections (U ×ˢ univ) B) (κ : ℝ)
    {n : ℕ} (hn : n ≤ 4) {A : X × ℝ → PolarPoint [×n]→L[ℝ] PolarPoint}
    (Q : SmoothDirections (U ×ˢ univ) A)
    (he : ∀ w : Fin n → Fin 2, ∀ y ∈ U ×ˢ (univ : Set ℝ),
      A y (fun i => cylinderBasisVector (w i)) =
        n04PositiveGeometry_forwardBasisValue κ
          (fun j θ => O j (y.1, θ)) (fun j θ => E j (y.1, θ))
          (fun θ => B (y.1, θ)) (n04PositiveGeometry_planeWordRadial w)
          (n04PositiveGeometry_planeWordAngular w) y.2)
    {K s d : ℕ} {x : X} (hx : x ∈ U) (hU : Convex ℝ U)
    {θ : ℝ} {P : X → Prop} (hP : P 0)
    {M H t : ℝ} {shift : ℕ} (hM : 0 ≤ M) (hH : 0 ≤ H) (ht : 1 ≤ t)
    (hO : ∀ j (hj : j ≤ 3),
      N04BoundaryWordBounds (JO j hj) K s (d + 4) x θ P M H t shift)
    (hE : ∀ j, N04BoundaryWordBounds (JE j) K s (d + 4) x θ P M H t shift)
    (hB : N04BoundaryWordBounds JB K s (d + 4) x θ P M H t shift) :
    N04BoundaryWordBounds Q K s d x θ P
      ((2 : ℝ) ^ n * ((1 + 4 * |κ|) * M)) H t shift := by
  have ha (w : Fin n → Fin 2) : n04PositiveGeometry_planeWordRadial w ≤ 4 := by
    have hc := n04PositiveGeometry_planeWord_orders w
    omega
  have hb (w : Fin n → Fin 2) : n04PositiveGeometry_planeWordAngular w ≤ 4 := by
    have hc := n04PositiveGeometry_planeWord_orders w
    omega
  let J (w : Fin n → Fin 2) := n04PositiveGeometry_forwardBasis_directions
    JO JE JB κ (n04PositiveGeometry_planeWordRadial w)
      (n04PositiveGeometry_planeWordAngular w) (ha w)
  let Qw (w : Fin n → Fin 2) : SmoothDirections (U ×ˢ univ)
      (fun y => A y (fun i => cylinderBasisVector (w i))) :=
    (J w).congr (fun y hy => (he w y hy).symm)
  apply N04BoundaryWordBounds.of_planeBasis Q Qw hx
    (mul_nonneg (by positivity) hM) hH (zero_le_one.trans ht)
  intro w
  exact (n04PositiveGeometry_forwardBasis_word_bound JO JE JB κ
    (n04PositiveGeometry_planeWordRadial w) (n04PositiveGeometry_planeWordAngular w)
    (ha w) (hb w) (J w) hx hU hP hM hH ht hO hE hB).congr hx
      (fun y hy => (he w y hy).symm)

end ContinuousFlexibility.Analysis
