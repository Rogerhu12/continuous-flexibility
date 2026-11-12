import ContinuousFlexibility.Analysis.FlatMixedDiagonalRealization
import ContinuousFlexibility.Analysis.TameUniformFamilyJets

/-!
# Reflection and linear reconstruction of actual mixed jets

Angular reflection only changes the sign of odd angular derivatives.
Linear reconstruction and finite parameter-order maxima retain the
same label factor. These operations apply to any genuine tower of the
specified functions, by uniqueness of actual parameter derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open scoped ContDiff

theorem mixedDerivative_reflect_angle (f : PolarPoint → ℝ)
    (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => f (q.1, -q.2)) p =
      (-1 : ℝ) ^ b * mixedDerivative a b f (p.1, -p.2) := by
  have hangle (r : ℝ) :
      iteratedDeriv b (fun θ : ℝ => f (r, -θ)) p.2 =
        (-1 : ℝ) ^ b * iteratedDeriv b (fun θ : ℝ => f (r, θ)) (-p.2) := by
    simpa only [smul_eq_mul] using
      iteratedDeriv_comp_neg b (fun θ : ℝ => f (r, θ)) p.2
  exact (congrArg (fun g : ℝ → ℝ => iteratedDeriv a g p.1) (funext hangle)).trans
    (iteratedDeriv_const_mul_field (n := a) (x := p.1) ((-1 : ℝ) ^ b)
      (fun r : ℝ => iteratedDeriv b (fun θ : ℝ => f (r, θ)) (-p.2)))

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : I → Set PolarPoint}

theorem jointMixedDiagonal_linear_combination
    {V₀ : Set PolarPoint} {f g h : E × PolarPoint → ℝ}
    (J : SmoothDirections (U ×ˢ V₀) f) (K : SmoothDirections (U ×ˢ V₀) g)
    (H : SmoothDirections (U ×ˢ V₀) h) (hV : IsOpen V₀) (α β : ℝ)
    (hvalue : ∀ x ∈ U, ∀ y ∈ V₀, h (x, y) = α * f (x, y) + β * g (x, y))
    (n a b : ℕ) (x w : E) (hx : x ∈ U) {y : PolarPoint} (hy : y ∈ V₀) :
    jointMixedDiagonal H n a b x w y =
      α * jointMixedDiagonal J n a b x w y + β * jointMixedDiagonal K n a b x w y := by
  let A : (ℝ × ℝ) →L[ℝ] ℝ :=
    α • ContinuousLinearMap.fst ℝ ℝ ℝ + β • ContinuousLinearMap.snd ℝ ℝ ℝ
  let M := smoothDirectionsPostContinuousLinear (smoothDirectionsProd J K) A
  have hMH : EqOn (fun z => A (f z, g z)) h (U ×ˢ V₀) := by
    intro z hz
    exact (hvalue z.1 hz.1 z.2 hz.2).symm
  have hjet (q : PolarPoint) (hq : q ∈ V₀) :
      H.D n (x, q) (fun _ => (w, (0 : PolarPoint))) =
        α * J.D n (x, q) (fun _ => (w, (0 : PolarPoint))) +
          β * K.D n (x, q) (fun _ => (w, (0 : PolarPoint))) := by
    have heq := congrArg (fun B : (E × PolarPoint) [×n]→L[ℝ] ℝ =>
      B (fun _ => (w, (0 : PolarPoint)))) ((M.congrOn hMH).unique H n (x, q) ⟨hx, hq⟩)
    exact heq.symm
  have hlocal := mixedDerivative_congr_on_open hV hjet a b hy
  have hJ := J.jointJet_spatial_contDiffOn hV n x hx (fun _ => (w, (0 : PolarPoint)))
  have hK := K.jointJet_spatial_contDiffOn hV n x hx (fun _ => (w, (0 : PolarPoint)))
  have hrewrite : (fun q : PolarPoint =>
      α * J.D n (x, q) (fun _ => (w, (0 : PolarPoint))) +
        β * K.D n (x, q) (fun _ => (w, (0 : PolarPoint)))) =
      fun q => α * J.D n (x, q) (fun _ => (w, (0 : PolarPoint))) -
        (-β) * K.D n (x, q) (fun _ => (w, (0 : PolarPoint))) := by
    funext q
    ring
  rw [hrewrite, mixedDerivative_sub_of_contDiffOn hV
    (contDiffOn_const.mul hJ) (contDiffOn_const.mul hK) a b hy,
    mixedDerivative_const_mul, mixedDerivative_const_mul] at hlocal
  exact hlocal.trans (by simp only [jointMixedDiagonal]; ring)

theorem FlatMixedDiagonalGrowth.linear_combination
    {p : ℕ → Seminorm ℝ E} {W F : I → ℝ}
    (hW : ∀ i, 1 ≤ W i) (hF : ∀ i, 0 ≤ F i)
    {f g h : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    {K : ∀ i, SmoothDirections (U ×ˢ V i) (g i)}
    (H : ∀ i, SmoothDirections (U ×ˢ V i) (h i)) (hV : ∀ i, IsOpen (V i))
    (α β : ℝ)
    (hvalue : ∀ i x, x ∈ U → ∀ y ∈ V i,
      h i (x, y) = α * f i (x, y) + β * g i (x, y))
    {n B L : ℕ} (hJ : FlatMixedDiagonalGrowth p W F J n B L)
    (hK : FlatMixedDiagonalGrowth p W F K n B L) :
    FlatMixedDiagonalGrowth p W F H n B L := by
  intro R hR s
  obtain ⟨A, P, hA, hP, hAb⟩ := hJ R hR s
  obtain ⟨A', P', hA', hP', hA'b⟩ := hK R hR s
  refine ⟨|α| * A + |β| * A', P + P', by positivity, add_nonneg hP hP', ?_⟩
  intro i x hx hxB w hw y hy k hk a b hab
  let Z : ℝ := 1 + p (s + L) x + p (s + L) w
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hleft : |jointMixedDiagonal (J i) k a b x w y| ≤
      A * F i * W i ^ (P + P') * Z := by
    apply (hAb i x hx hxB w hw y hy k hk a b hab).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hW i) (le_add_of_nonneg_right hP'))
      (mul_nonneg hA (hF i))) hZ
  have hright : |jointMixedDiagonal (K i) k a b x w y| ≤
      A' * F i * W i ^ (P + P') * Z := by
    apply (hA'b i x hx hxB w hw y hy k hk a b hab).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hW i) (le_add_of_nonneg_left hP))
      (mul_nonneg hA' (hF i))) hZ
  rw [jointMixedDiagonal_linear_combination (J i) (K i) (H i) (hV i)
    α β (hvalue i) k a b x w hx hy]
  exact (abs_add_le _ _).trans ((add_le_add
    (by simpa only [abs_mul] using mul_le_mul_of_nonneg_left hleft (abs_nonneg α))
    (by simpa only [abs_mul] using mul_le_mul_of_nonneg_left hright (abs_nonneg β))).trans_eq
      (by dsimp only [Z]; ring))

theorem HasFlatMixedTameGrowth.linear_combination
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {W F : I → ℝ} (hW : ∀ i, 1 ≤ W i) (hF : ∀ i, 0 ≤ F i)
    {f g h : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    {K : ∀ i, SmoothDirections (U ×ˢ V i) (g i)}
    (H : ∀ i, SmoothDirections (U ×ˢ V i) (h i)) (hV : ∀ i, IsOpen (V i))
    (α β : ℝ)
    (hvalue : ∀ i x, x ∈ U → ∀ y ∈ V i,
      h i (x, y) = α * f i (x, y) + β * g i (x, y))
    (hJ : HasFlatMixedTameGrowth p W F J) (hK : HasFlatMixedTameGrowth p W F K) :
    HasFlatMixedTameGrowth p W F H := by
  intro n
  obtain ⟨B₀, L₀, hJ⟩ := hJ n
  obtain ⟨B₁, L₁, hK⟩ := hK n
  refine ⟨max B₀ B₁, max L₀ L₁, ?_⟩
  exact (hJ.mono hp (fun i => zero_le_one.trans (hW i)) hF
    (le_max_left _ _) (le_max_left _ _)).linear_combination hW hF H hV α β hvalue
      (hK.mono hp (fun i => zero_le_one.trans (hW i)) hF
        (le_max_right _ _) (le_max_right _ _))

theorem jointMixedDiagonal_reflect_angle
    {V₀ : Set PolarPoint} {f g : E × PolarPoint → ℝ}
    (J : SmoothDirections (U ×ˢ V₀) f) (K : SmoothDirections (U ×ˢ V₀) g)
    (hU : IsOpen U) (hV : IsOpen V₀)
    (hmap : ∀ y ∈ V₀, (y.1, -y.2) ∈ V₀)
    (hvalue : ∀ x ∈ U, ∀ y ∈ V₀, g (x, y) = f (x, (y.1, -y.2)))
    (n a b : ℕ) (x w : E) (hx : x ∈ U) {y : PolarPoint} (hy : y ∈ V₀) :
    jointMixedDiagonal K n a b x w y =
      (-1 : ℝ) ^ b * jointMixedDiagonal J n a b x w (y.1, -y.2) := by
  let P : (E × PolarPoint) →L[ℝ] E × PolarPoint :=
    (ContinuousLinearMap.fst ℝ E PolarPoint).prod
      (((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (-(ContinuousLinearMap.snd ℝ ℝ ℝ))).comp
        (ContinuousLinearMap.snd ℝ E PolarPoint))
  have hP (z : E) (q : PolarPoint) : P (z, q) = (z, (q.1, -q.2)) := rfl
  have hPzero : P (w, (0 : PolarPoint)) = (w, (0 : PolarPoint)) := by
    rw [hP]
    simp only [Prod.fst_zero, Prod.snd_zero, neg_zero, Prod.mk_zero_zero]
  have hmaps : MapsTo (fun z => (0 : E × PolarPoint) + P z) (U ×ˢ V₀) (U ×ˢ V₀) := by
    rintro ⟨z, q⟩ hz
    rw [zero_add, hP]
    exact ⟨hz.1, hmap q hz.2⟩
  let M := J.compAffine P 0 (hU.prod hV) hmaps
  have hMK : EqOn (fun z => f ((0 : E × PolarPoint) + P z)) g (U ×ˢ V₀) := by
    intro z hz
    simpa only [zero_add, hP] using (hvalue z.1 hz.1 z.2 hz.2).symm
  have hjet (q : PolarPoint) (hq : q ∈ V₀) :
      K.D n (x, q) (fun _ => (w, (0 : PolarPoint))) =
        J.D n (x, (q.1, -q.2)) (fun _ => (w, (0 : PolarPoint))) := by
    have heq := congrArg (fun A : (E × PolarPoint) [×n]→L[ℝ] ℝ =>
      A (fun _ => (w, (0 : PolarPoint)))) ((M.congrOn hMK).unique K n (x, q) ⟨hx, hq⟩)
    have heq' : J.D n ((0 : E × PolarPoint) + P (x, q))
        (fun _ : Fin n => P (w, (0 : PolarPoint))) =
      K.D n (x, q) (fun _ => (w, (0 : PolarPoint))) := heq
    have hpoint : (0 : E × PolarPoint) + P (x, q) = (x, (q.1, -q.2)) :=
      (zero_add (P (x, q))).trans (hP x q)
    have hdirs : (fun _ : Fin n => P (w, (0 : PolarPoint))) =
        (fun _ : Fin n => (w, (0 : PolarPoint))) := funext (fun _ => hPzero)
    exact heq'.symm.trans (congrArg₂
      (fun z : E × PolarPoint => fun v : Fin n → E × PolarPoint => J.D n z v)
      hpoint hdirs)
  exact (mixedDerivative_congr_on_open hV hjet a b hy).trans
    (mixedDerivative_reflect_angle (fun q => J.D n (x, q) (fun _ => (w, 0))) a b y)

theorem FlatMixedDiagonalGrowth.reflect_angle
    {p : ℕ → Seminorm ℝ E} {W F : I → ℝ}
    {f g : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    (K : ∀ i, SmoothDirections (U ×ˢ V i) (g i))
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hmap : ∀ i y, y ∈ V i → (y.1, -y.2) ∈ V i)
    (hvalue : ∀ i x, x ∈ U → ∀ y ∈ V i, g i (x, y) = f i (x, (y.1, -y.2)))
    {n B L : ℕ} (h : FlatMixedDiagonalGrowth p W F J n B L) :
    FlatMixedDiagonalGrowth p W F K n B L := by
  intro R hR s
  obtain ⟨C, Q, hC, hQ, hb⟩ := h R hR s
  refine ⟨C, Q, hC, hQ, fun i x hx hxB w hw y hy k hk a b hab => ?_⟩
  rw [jointMixedDiagonal_reflect_angle (J i) (K i) hU (hV i) (hmap i)
    (hvalue i) k a b x w hx hy]
  simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
    hb i x hx hxB w hw (y.1, -y.2) (hmap i y hy) k hk a b hab

theorem HasFlatMixedTameGrowth.reflect_angle
    {p : ℕ → Seminorm ℝ E} {W F : I → ℝ}
    {f g : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    (K : ∀ i, SmoothDirections (U ×ˢ V i) (g i))
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hmap : ∀ i y, y ∈ V i → (y.1, -y.2) ∈ V i)
    (hvalue : ∀ i x, x ∈ U → ∀ y ∈ V i, g i (x, y) = f i (x, (y.1, -y.2)))
    (h : HasFlatMixedTameGrowth p W F J) :
    HasFlatMixedTameGrowth p W F K := by
  intro n
  obtain ⟨B, L, hb⟩ := h n
  exact ⟨B, L, hb.reflect_angle K hU hV hmap hvalue⟩

end ContinuousFlexibility.Analysis
