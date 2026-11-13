import ContinuousFlexibility.Analysis.N04PulledFieldsOriginalDifferencePhysical
import ContinuousFlexibility.Analysis.SolveNewtonBridge
import ContinuousFlexibility.Analysis.MixedDerivativeLocality

/-!
# Subtraction and finite packing of physical height bounds

The jet identity is proved for arbitrary genuine towers.  The numerical
packing keeps one low base for the finite family, and chooses the high
loss before the spatial order.  No moving spatial point occurs here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

theorem n04PulledFields_subtraction_jet
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {U : Set X} {f g h : X → ℝ}
    (J : SmoothDirections U f) (K : SmoothDirections U g) (L : SmoothDirections U h)
    (heq : ∀ x ∈ U, f x = g x - h x)
    (k : ℕ) (x : X) (hx : x ∈ U) (v : Fin k → X) :
    J.D k x v = K.D k x v - L.D k x v := by
  let N := solveSmoothDirectionsPostcomp L (-ContinuousLinearMap.id ℝ ℝ)
  let M : SmoothDirections U f := (smoothDirectionsAdd K N).congrOn
    (fun y hy => by
      simpa only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
        sub_eq_add_neg] using (heq y hy).symm)
  have hjet := congrArg (fun A : X [×k]→L[ℝ] ℝ => A v) (J.unique M k x hx)
  simpa only [M, N, SmoothDirections.congrOn, smoothDirectionsAdd,
    solveSmoothDirectionsPostcomp, add_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, sub_eq_add_neg] using hjet

theorem n04PulledFields_mixedSubtraction_jet
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {U : Set X} {V : Set PolarPoint} {f g h : X → PolarPoint → ℝ}
    (hV : IsOpen V) (RF : MixedJetRegularity U V f)
    (RG : MixedJetRegularity U V g) (RH : MixedJetRegularity U V h)
    (heq : ∀ x ∈ U, ∀ y ∈ V, f x y = g x y - h x y)
    (k a b : ℕ) (x : X) (hx : x ∈ U) (y : PolarPoint) (hy : y ∈ V)
    (v : Fin k → X) :
    (RF.parameter a b y hy).D k x v =
      (RG.parameter a b y hy).D k x v - (RH.parameter a b y hy).D k x v := by
  apply n04PulledFields_subtraction_jet (RF.parameter a b y hy)
    (RG.parameter a b y hy) (RH.parameter a b y hy) _ k x hx v
  intro z hz
  exact (mixedDerivative_congr_on_open hV (heq z hz) a b hy).trans
    (mixedDerivative_sub_of_contDiffOn hV (RG.spatial z hz) (RH.spatial z hz) a b hy)

private theorem n04PulledFields_heightCost_mono
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p)
    {B B' L L' s k : ℕ} (hB : B ≤ B') (hL : L ≤ L')
    {C C' Q Q' E H : ℝ} (hC : 0 ≤ C) (hCC : C ≤ C')
    (hQQ : Q ≤ Q') (hE : 1 ≤ E) (hH : 0 ≤ H) (x : X) (v : Fin k → X) :
    C * E ^ Q * H * oneHighVariationWeight p B (s + L) x v ≤
      C' * E ^ Q' * H * oneHighVariationWeight p B' (s + L') x v := by
  have hpow := Real.rpow_le_rpow_of_exponent_le hE hQQ
  have hcoef : C * E ^ Q * H ≤ C' * E ^ Q' * H :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul hCC hpow (Real.rpow_nonneg (zero_le_one.trans hE) _) (hC.trans hCC)) hH
  have hcoef' : 0 ≤ C' * E ^ Q' * H := mul_nonneg
    (mul_nonneg (hC.trans hCC) (Real.rpow_nonneg (zero_le_one.trans hE) _)) hH
  exact (mul_le_mul_of_nonneg_right hcoef (oneHighVariationWeight_nonneg _ _ _ _ _)).trans
    (mul_le_mul_of_nonneg_left
      (oneHighVariationWeight_mono hp hB (Nat.add_le_add_left hL s) x v) hcoef')

/-- A finite set of correction errors can be subtracted from a uniformly
bounded original family without moving the low base after the jet order. -/
theorem n04PulledFields_finite_heightDifference
    {I X Y : Type*} [Fintype I] [AddCommGroup X] [Module ℝ X]
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (U : Set X)
    (E H : Y → ℝ) (hE : ∀ y, 1 ≤ E y) (hH : ∀ y, 0 ≤ H y)
    (base loss : ℕ)
    (D O A : ∀ k : ℕ, I → X → Y → ℕ → ℕ → (Fin k → X) → ℝ)
    (hD : ∀ k i x, x ∈ U → ∀ y a b v,
      D k i x y a b v = O k i x y a b v - A k i x y a b v)
    (hO : ∀ k s : ℕ, ∃ C Q : ℝ, 0 ≤ C ∧ 0 ≤ Q ∧
      ∀ i x, x ∈ U → ∀ y a b, a + b ≤ s → ∀ v : Fin k → X,
        |O k i x y a b v| ≤ C * E y ^ Q * H y *
          oneHighVariationWeight p base (s + loss) x v)
    (hA : ∀ i, ∃ B : ℕ, ∀ k : ℕ, ∃ L : ℕ, ∀ s : ℕ, ∃ C Q : ℝ,
      0 ≤ C ∧ 0 ≤ Q ∧ ∀ x, x ∈ U → p B x ≤ 1 →
      ∀ y a b, a + b ≤ s → ∀ v : Fin k → X,
        |A k i x y a b v| ≤ C * E y ^ Q * H y *
          oneHighVariationWeight p B (s + L) x v) :
    ∃ B : ℕ, ∀ k : ℕ, ∃ L : ℕ, ∀ s : ℕ, ∃ C Q : ℝ,
      0 ≤ C ∧ 0 ≤ Q ∧ ∀ i x, x ∈ U → p B x ≤ 1 →
      ∀ y a b, a + b ≤ s → ∀ v : Fin k → X,
        |D k i x y a b v| ≤ C * E y ^ Q * H y *
          oneHighVariationWeight p B (s + L) x v := by
  classical
  choose B hB using hA
  let B' : ℕ := base + ∑ i, B i
  have hbase : base ≤ B' := Nat.le_add_right _ _
  have hBi (i : I) : B i ≤ B' := by
    have hi := Finset.single_le_sum (f := B)
      (fun j _ => Nat.zero_le (B j)) (Finset.mem_univ i)
    dsimp only [B']
    omega
  refine ⟨B', fun k => ?_⟩
  choose L hL using fun i => hB i k
  let L' : ℕ := loss + ∑ i, L i
  have hloss : loss ≤ L' := Nat.le_add_right _ _
  have hLi (i : I) : L i ≤ L' := by
    have hi := Finset.single_le_sum (f := L)
      (fun j _ => Nat.zero_le (L j)) (Finset.mem_univ i)
    dsimp only [L']
    omega
  refine ⟨L', fun s => ?_⟩
  obtain ⟨C₀, Q₀, hC₀, hQ₀, hO'⟩ := hO k s
  choose C Q hC hQ hA' using fun i => hL i s
  let C₁ : ℝ := ∑ i, C i
  let Q' : ℝ := Q₀ + ∑ i, Q i
  have hC₁ : 0 ≤ C₁ := Finset.sum_nonneg (fun i _ => hC i)
  have hQsum : 0 ≤ ∑ i, Q i := Finset.sum_nonneg (fun i _ => hQ i)
  have hQ' : 0 ≤ Q' := add_nonneg hQ₀ hQsum
  have hQ₀' : Q₀ ≤ Q' := le_add_of_nonneg_right hQsum
  have hCi (i : I) : C i ≤ C₁ :=
    Finset.single_le_sum (f := C) (fun j _ => hC j) (Finset.mem_univ i)
  have hQi (i : I) : Q i ≤ Q' :=
    (Finset.single_le_sum (f := Q) (fun j _ => hQ j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left hQ₀)
  refine ⟨C₀ + C₁, Q', add_nonneg hC₀ hC₁, hQ', fun i x hx hxlow y a b hab v => ?_⟩
  have hlow : p (B i) x ≤ 1 := (hp (hBi i) x).trans hxlow
  have hfirst := (hO' i x hx y a b hab v).trans
    (n04PulledFields_heightCost_mono p hp hbase hloss hC₀ le_rfl hQ₀'
      (hE y) (hH y) x v)
  have hsecond := (hA' i x hx hlow y a b hab v).trans
    (n04PulledFields_heightCost_mono p hp (hBi i) (hLi i) (hC i) (hCi i) (hQi i)
      (hE y) (hH y) x v)
  rw [hD k i x hx y a b v]
  have htriangle : |O k i x y a b v - A k i x y a b v| ≤
      |O k i x y a b v| + |A k i x y a b v| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (O k i x y a b v) (-A k i x y a b v)
  exact htriangle.trans ((add_le_add hfirst hsecond).trans_eq (by ring))

end ContinuousFlexibility.Analysis
