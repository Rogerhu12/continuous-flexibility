import ContinuousFlexibility.Scalar.WeightedCompositionTower
import ContinuousFlexibility.Scalar.WeightedDecodedProduct
import ContinuousFlexibility.Scalar.WeightedOneHighCosts

/-!
# From value estimates to a uniform scalar composition tower

The only analytic input beyond finite-product estimates is the zeroth-order
composition estimate with a base and loss independent of the scalar function.
At directional order k, the actual decoded derivative is F^(k)(u) times the
k directions. Subtracting F^(k)(0) supplies one genuine height coefficient;
its low norm is bounded on the original common neighbourhood.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Zeroth composition bounds, proved for actual fields, imply uniform bounds
for every genuine directional tower. Both final orders precede the scalar
function, the domain and the directional order. -/
theorem uniformSobolevComposition_of_valueBounds
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ)
    (valueBase valueLoss : ℕ)
    (hmember : ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → F 0 = 0 →
      ∀ u : A.Space, HeightMember D T γ (fun p => F (A.decode u p)))
    (hvalue : ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → F 0 = 0 →
      ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ u : A.Space, A.grading valueBase u ≤ R →
          physicalNorm T γ s (fun p => F (A.decode u p)) ≤
            C * A.grading (s + valueLoss) u) :
    ∃ base loss : ℕ, ∀ {U : Set A.Space} {f : A.Space → A.Space},
      ∀ J : SmoothDirections U f, ∀ F : ℝ → ℝ,
        ContDiff ℝ ∞ F → F 0 = 0 →
        (∀ x ∈ U, ∀ p, A.decode (f x) p = F (A.decode x p)) →
        ∀ R : ℝ, 0 ≤ R → (∀ x ∈ U, A.grading base x ≤ R) →
          UniformScalarTowerEstimate A.grading A.grading U base loss f J := by
  have hp : Monotone A.grading := gradedSeminorm_monotone (fun n => A.level n) A.bond
  obtain ⟨productBase, productLoss, _, hproduct⟩ :=
    SobolevModelData.decodedProduct_oneHigh hT hA hinterp hγ
  let base := max valueBase (productBase + valueLoss)
  let loss := productLoss + valueLoss
  have hbaseValue : valueBase ≤ base := le_max_left _ _
  have hbaseProduct : productBase ≤ base :=
    (Nat.le_add_right _ _).trans (le_max_right _ _)
  have hbaseLow : productBase + valueLoss ≤ base := le_max_right _ _
  refine ⟨base, loss, ?_⟩
  intro U f J F hF hF0 hdecode R hR hU
  have hUvalue (x : A.Space) (hx : x ∈ U) : A.grading valueBase x ≤ R :=
    (hp hbaseValue x).trans (hU x hx)
  intro k s _
  cases k with
  | zero =>
    obtain ⟨C, hC, hCu⟩ := hvalue F hF hF0 R hR s
    refine ⟨C, hC, ?_⟩
    intro x hx v
    change A.grading s (J.D 0 x v) ≤ C * tameJetSize A.grading 0 s loss base x v
    have hv : v = Fin.elim0 := Subsingleton.elim _ _
    rw [hv, J.zero x hx, tameJetSize_zero]
    have heq : A.decode (f x) = fun p => F (A.decode x p) := funext (hdecode x hx)
    rw [sobolevGrading_eq_physicalNorm hA, heq]
    apply (hCu x (hUvalue x hx)).trans
    apply mul_le_mul_of_nonneg_left _ hC
    have hi : s + valueLoss ≤ s + loss := by dsimp [loss]; omega
    have hh := hp hi x
    linarith only [hh]
  | succ k =>
    have hk : ContDiff ℝ ∞ (iteratedDeriv (k + 1) F) := by
      rw [iteratedDeriv_eq_iterate]
      exact hF.iterate_deriv (k + 1)
    let G : ℝ → ℝ := fun z => iteratedDeriv (k + 1) F z - iteratedDeriv (k + 1) F 0
    have hG : ContDiff ℝ ∞ G := hk.sub contDiff_const
    have hG0 : G 0 = 0 := sub_self _
    let g : A.Space → A.Space := fun x =>
      SobolevModelData.liftHeight hA (fun p => G (A.decode x p)) (hmember G hG hG0 x)
    have hgdecode (x : A.Space) :
        A.decode (g x) = fun p => G (A.decode x p) :=
      SobolevModelData.decode_liftHeight hA _ (hmember G hG hG0 x)
    have hgbound (t : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U,
        A.grading t (g x) ≤ C * A.grading (t + valueLoss) x := by
      obtain ⟨C, hC, hCx⟩ := hvalue G hG hG0 R hR t
      refine ⟨C, hC, ?_⟩
      intro x hx
      rw [sobolevGrading_eq_physicalNorm hA, hgdecode]
      exact hCx x (hUvalue x hx)
    obtain ⟨Cₕ, hCₕ, hgHigh⟩ := hgbound (s + productLoss)
    obtain ⟨Cₗ, hCₗ, hgLow⟩ := hgbound productBase
    obtain ⟨P, hP, hPu⟩ := hproduct (k + 1) s
    obtain ⟨V, hV, hVu⟩ := hproduct k s
    let K : ℝ := P * (Cₕ + Cₗ * R) + ‖iteratedDeriv (k + 1) F 0‖ * V
    have hK : 0 ≤ K := add_nonneg
      (mul_nonneg hP (add_nonneg hCₕ (mul_nonneg hCₗ hR)))
      (mul_nonneg (norm_nonneg _) hV)
    refine ⟨K, hK, ?_⟩
    intro x hx v
    let y : A.Space := SobolevModelData.decodedProduct hT hA hinterp hγ
      (k + 1) (Fin.cons (g x) v)
    let z : A.Space := SobolevModelData.decodedProduct hT hA hinterp hγ k v
    have hydecode (p : PolarPoint) :
        A.decode y p = G (A.decode x p) * ∏ i, A.decode (v i) p := by
      dsimp only [y]
      rw [SobolevModelData.decode_decodedProduct]
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, hgdecode]
    have hzdecode (p : PolarPoint) : A.decode z p = ∏ i, A.decode (v i) p := by
      dsimp only [z]
      rw [SobolevModelData.decode_decodedProduct]
    have hactual : J.D (k + 1) x v = y + iteratedDeriv (k + 1) F 0 • z := by
      apply hA.2.2.2.2.2.1
      funext p
      simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [sobolevCompositionTower_decode hA J hF hdecode (k + 1) x hx v p,
        hydecode, hzdecode]
      dsimp only [G]
      ring
    have hindex : s + productLoss ≤ s + loss := by dsimp [loss]; omega
    have hgH : A.grading (s + productLoss) (g x) ≤
        Cₕ * (1 + A.grading (s + loss) x) := by
      have hh : A.grading (s + productLoss) (g x) ≤
          Cₕ * A.grading (s + loss) x := by
        simpa only [loss, Nat.add_assoc] using hgHigh x hx
      apply hh.trans
      exact mul_le_mul_of_nonneg_left (by linarith) hCₕ
    have hgL : A.grading productBase (g x) ≤ Cₗ * R :=
      (hgLow x hx).trans (mul_le_mul_of_nonneg_left
        ((hp hbaseLow x).trans (hU x hx)) hCₗ)
    have hybound : A.grading s y ≤
        (P * (Cₕ + Cₗ * R)) * tameJetSize A.grading (k + 1) s loss base x v := by
      have hh := scalarOneHighCost_cons_le_tameJetSize hp hbaseProduct hindex
        hCₕ (mul_nonneg hCₗ hR) x (g x) v hgH hgL
      exact ((hPu (Fin.cons (g x) v)).trans
        (mul_le_mul_of_nonneg_left hh hP)).trans_eq (by ring)
    have hzbound : A.grading s z ≤
        V * tameJetSize A.grading (k + 1) s loss base x v :=
      (hVu v).trans (mul_le_mul_of_nonneg_left
        (scalarOneHighCost_le_tameJetSize hp hbaseProduct hindex x v) hV)
    change A.grading s (J.D (k + 1) x v) ≤
      K * tameJetSize A.grading (k + 1) s loss base x v
    rw [hactual]
    calc
      _ ≤ A.grading s y + A.grading s (iteratedDeriv (k + 1) F 0 • z) :=
        map_add_le_add _ _ _
      _ = A.grading s y + ‖iteratedDeriv (k + 1) F 0‖ * A.grading s z := by
        rw [map_smul_eq_mul]
      _ ≤ (P * (Cₕ + Cₗ * R)) * tameJetSize A.grading (k + 1) s loss base x v +
          ‖iteratedDeriv (k + 1) F 0‖ *
            (V * tameJetSize A.grading (k + 1) s loss base x v) :=
        add_le_add hybound (mul_le_mul_of_nonneg_left hzbound (norm_nonneg _))
      _ = _ := by dsimp only [K]; ring

end ContinuousFlexibility.Statements
