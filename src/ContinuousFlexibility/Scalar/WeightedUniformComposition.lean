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

/-- The final estimate uses only the seminorm triangle inequality and the
two finite one-high-factor inequalities.  Keeping this arithmetic separate
also keeps the actual decoder constructions out of normalization. -/
private theorem uniformComposition_numeric
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {b base h s loss n : ℕ} (hb : b ≤ base) (hh : h ≤ s + loss)
    {P V Cₕ Cₗ d : ℝ}
    (hP : 0 ≤ P) (hV : 0 ≤ V) (hCₕ : 0 ≤ Cₕ) (hCₗ : 0 ≤ Cₗ)
    (x g y z : E) (v : Fin n → E)
    (hy : p s y ≤ P * ∑ i : Fin (n + 1),
      p h (Fin.cons (α := fun _ : Fin (n + 1) => E) g v i) *
        ∏ j ∈ Finset.univ.erase i, p b (Fin.cons (α := fun _ : Fin (n + 1) => E) g v j))
    (hz : p s z ≤ V * ∑ i, p h (v i) *
      ∏ j ∈ Finset.univ.erase i, p b (v j))
    (hgH : p h g ≤ Cₕ * (1 + p (s + loss) x))
    (hgL : p b g ≤ Cₗ) :
    p s (y + d • z) ≤
      (P * (Cₕ + Cₗ) + ‖d‖ * V) * tameJetSize p n s loss base x v := by
  have hybound : p s y ≤
      (P * (Cₕ + Cₗ)) * tameJetSize p n s loss base x v := by
    have hc := scalarOneHighCost_cons_le_tameJetSize hp hb hh hCₕ hCₗ x g v hgH hgL
    exact (hy.trans (mul_le_mul_of_nonneg_left hc hP)).trans_eq (by ring)
  have hzbound : p s z ≤ V * tameJetSize p n s loss base x v :=
    hz.trans (mul_le_mul_of_nonneg_left
      (scalarOneHighCost_le_tameJetSize hp hb hh x v) hV)
  calc
    _ ≤ p s y + p s (d • z) := map_add_le_add _ _ _
    _ = p s y + ‖d‖ * p s z := by rw [map_smul_eq_mul]
    _ ≤ (P * (Cₕ + Cₗ)) * tameJetSize p n s loss base x v +
        ‖d‖ * (V * tameJetSize p n s loss base x v) :=
      add_le_add hybound (mul_le_mul_of_nonneg_left hzbound (norm_nonneg _))
    _ = _ := by ring

/-- Center the scalar derivative before forming the true encoded products.
This is an equality in the prescribed Sobolev model, proved by its injective
physical decoder. -/
private theorem sobolevCompositionTower_centered_product
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ)
    {U : Set A.Space} {f : A.Space → A.Space} (J : SmoothDirections U f)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hdecode : ∀ x ∈ U, ∀ p, A.decode (f x) p = F (A.decode x p))
    (k : ℕ) (g : A.Space → A.Space)
    (hgdecode : ∀ x, A.decode (g x) =
      fun p => iteratedDeriv (k + 1) F (A.decode x p) - iteratedDeriv (k + 1) F 0)
    {x : A.Space} (hx : x ∈ U) (v : Fin (k + 1) → A.Space) :
    J.D (k + 1) x v =
      SobolevModelData.decodedProduct hT hA hinterp hγ (k + 1) (Fin.cons (g x) v) +
        iteratedDeriv (k + 1) F 0 •
          SobolevModelData.decodedProduct hT hA hinterp hγ k v := by
  have hydecode (p : PolarPoint) :
      A.decode (SobolevModelData.decodedProduct hT hA hinterp hγ
        (k + 1) (Fin.cons (g x) v)) p =
        (iteratedDeriv (k + 1) F (A.decode x p) - iteratedDeriv (k + 1) F 0) *
          ∏ i, A.decode (v i) p := by
    rw [SobolevModelData.decode_decodedProduct]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, hgdecode]
  have hzdecode (p : PolarPoint) :
      A.decode (SobolevModelData.decodedProduct hT hA hinterp hγ k v) p =
        ∏ i, A.decode (v i) p := by
    rw [SobolevModelData.decode_decodedProduct]
  apply hA.2.2.2.2.2.1
  funext p
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [sobolevCompositionTower_decode hA J hF hdecode (k + 1) x hx v p,
    hydecode, hzdecode]
  ring

private theorem uniformComposition_zero_bound
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hA : IsSobolevModel D T γ A)
    {U : Set A.Space} {f : A.Space → A.Space} (J : SmoothDirections U f)
    {F : ℝ → ℝ}
    (hdecode : ∀ x ∈ U, ∀ p, A.decode (f x) p = F (A.decode x p))
    {base loss valueLoss s : ℕ} (hloss : valueLoss ≤ loss)
    (hvalue : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U,
      physicalNorm T γ s (fun p => F (A.decode x p)) ≤
        C * A.grading (s + valueLoss) x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ v : Fin 0 → A.Space,
      A.grading s (J.D 0 x v) ≤ C * tameJetSize A.grading 0 s loss base x v := by
  obtain ⟨C, hC, hCx⟩ := hvalue
  refine ⟨C, hC, ?_⟩
  intro x hx v
  have hv : v = Fin.elim0 := Subsingleton.elim _ _
  rw [hv, J.zero x hx, tameJetSize_zero]
  have heq : A.decode (f x) = fun p => F (A.decode x p) := funext (hdecode x hx)
  rw [sobolevGrading_eq_physicalNorm hA, heq]
  apply (hCx x hx).trans
  apply mul_le_mul_of_nonneg_left _ hC
  have hh := gradedSeminorm_monotone (fun n => A.level n) A.bond
    (Nat.add_le_add_left hloss s) x
  change A.grading (s + valueLoss) x ≤ 1 + A.grading (s + loss) x
  change A.grading (s + valueLoss) x ≤ A.grading (s + loss) x at hh
  linarith only [hh]

/-- A single positive derivative order is estimated using two genuine
products.  The low coefficient is bounded on the original common domain. -/
private theorem uniformComposition_positive_bound
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ)
    {valueBase valueLoss productBase productLoss base : ℕ}
    (hbaseValue : valueBase ≤ base) (hbaseProduct : productBase ≤ base)
    (hbaseLow : productBase + valueLoss ≤ base)
    (hmember : ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → F 0 = 0 →
      ∀ u : A.Space, HeightMember D T γ (fun p => F (A.decode u p)))
    (hvalue : ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → F 0 = 0 →
      ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ u : A.Space, A.grading valueBase u ≤ R →
          physicalNorm T γ s (fun p => F (A.decode u p)) ≤
            C * A.grading (s + valueLoss) u)
    (hproduct : ∀ k s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : Fin (k + 1) → A.Space,
        A.grading s (SobolevModelData.decodedProduct hT hA hinterp hγ k u) ≤
          C * ∑ i, A.grading (s + productLoss) (u i) *
            ∏ j ∈ Finset.univ.erase i, A.grading productBase (u j))
    {U : Set A.Space} {f : A.Space → A.Space} (J : SmoothDirections U f)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hdecode : ∀ x ∈ U, ∀ p, A.decode (f x) p = F (A.decode x p))
    {R : ℝ} (hR : 0 ≤ R) (hU : ∀ x ∈ U, A.grading base x ≤ R)
    (k s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ v : Fin (k + 1) → A.Space,
      A.grading s (J.D (k + 1) x v) ≤
        C * tameJetSize A.grading (k + 1) s (productLoss + valueLoss) base x v := by
  have hp : Monotone A.grading := gradedSeminorm_monotone (fun n => A.level n) A.bond
  have hk : ContDiff ℝ ∞ (iteratedDeriv (k + 1) F) := by
    rw [iteratedDeriv_eq_iterate]
    exact hF.iterate_deriv (k + 1)
  let G : ℝ → ℝ := fun z => iteratedDeriv (k + 1) F z - iteratedDeriv (k + 1) F 0
  have hG : ContDiff ℝ ∞ G := hk.sub contDiff_const
  have hG0 : G 0 = 0 := sub_self _
  let g : A.Space → A.Space := fun x =>
    SobolevModelData.liftHeight hA (fun p => G (A.decode x p)) (hmember G hG hG0 x)
  have hgdecode (x : A.Space) : A.decode (g x) = fun p => G (A.decode x p) :=
    SobolevModelData.decode_liftHeight hA _ (hmember G hG hG0 x)
  have hgbound (t : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U,
      A.grading t (g x) ≤ C * A.grading (t + valueLoss) x := by
    obtain ⟨C, hC, hCx⟩ := hvalue G hG hG0 R hR t
    refine ⟨C, hC, ?_⟩
    intro x hx
    rw [sobolevGrading_eq_physicalNorm hA, hgdecode]
    exact hCx x ((hp hbaseValue x).trans (hU x hx))
  obtain ⟨Cₕ, hCₕ, hgHigh⟩ := hgbound (s + productLoss)
  obtain ⟨Cₗ, hCₗ, hgLow⟩ := hgbound productBase
  obtain ⟨P, hP, hPu⟩ := hproduct (k + 1) s
  obtain ⟨V, hV, hVu⟩ := hproduct k s
  refine ⟨P * (Cₕ + Cₗ * R) + ‖iteratedDeriv (k + 1) F 0‖ * V,
    add_nonneg (mul_nonneg hP (add_nonneg hCₕ (mul_nonneg hCₗ hR)))
      (mul_nonneg (norm_nonneg _) hV), ?_⟩
  intro x hx v
  have hgH : A.grading (s + productLoss) (g x) ≤
      Cₕ * (1 + A.grading (s + (productLoss + valueLoss)) x) := by
    have hh := hgHigh x hx
    rw [Nat.add_assoc] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith) hCₕ)
  have hgL : A.grading productBase (g x) ≤ Cₗ * R :=
    (hgLow x hx).trans (mul_le_mul_of_nonneg_left
      ((hp hbaseLow x).trans (hU x hx)) hCₗ)
  rw [sobolevCompositionTower_centered_product hT hA hinterp hγ J hF hdecode k g hgdecode hx v]
  exact uniformComposition_numeric (p := A.grading) hp hbaseProduct
    (show s + productLoss ≤ s + (productLoss + valueLoss) by omega)
    hP hV hCₕ (mul_nonneg hCₗ hR) x (g x) _ _ v
    (hPu (Fin.cons (g x) v)) (hVu v) hgH hgL

/-- Package individual orders without unfolding the Sobolev model while
introducing the quantifiers of the frozen uniform-tower interface. -/
private theorem uniformComposition_of_orders
    {E H : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace H] [AddCommGroup H] [Module ℝ H]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ H}
    {U : Set E} {f : E → H} (J : SmoothDirections U f) {base loss : ℕ}
    (hzero : ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ v : Fin 0 → E,
      q s (J.D 0 x v) ≤ C * tameJetSize p 0 s loss base x v)
    (hpos : ∀ k s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ v : Fin (k + 1) → E,
      q s (J.D (k + 1) x v) ≤ C * tameJetSize p (k + 1) s loss base x v) :
    UniformScalarTowerEstimate p q U base loss f J := by
  intro k s _
  cases k with
  | zero => exact hzero s
  | succ k => exact hpos k s

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
  obtain ⟨productBase, productLoss, _, hproduct⟩ :=
    SobolevModelData.decodedProduct_oneHigh hT hA hinterp hγ
  refine ⟨max valueBase (productBase + valueLoss), productLoss + valueLoss, ?_⟩
  intro U f J F hF hF0 hdecode R hR hU
  have hbaseValue : valueBase ≤ max valueBase (productBase + valueLoss) := le_max_left _ _
  have hbaseProduct : productBase ≤ max valueBase (productBase + valueLoss) :=
    (Nat.le_add_right _ _).trans (le_max_right _ _)
  have hbaseLow : productBase + valueLoss ≤ max valueBase (productBase + valueLoss) :=
    le_max_right _ _
  refine uniformComposition_of_orders (p := A.grading) (q := A.grading) J ?_ ?_
  · intro s
    apply uniformComposition_zero_bound (valueLoss := valueLoss)
      (loss := productLoss + valueLoss) hA J hdecode
      (show valueLoss ≤ productLoss + valueLoss by omega)
    obtain ⟨C, hC, hCx⟩ := hvalue F hF hF0 R hR s
    refine ⟨C, hC, ?_⟩
    intro x hx
    exact hCx x ((gradedSeminorm_monotone (fun n => A.level n) A.bond hbaseValue x).trans
      (hU x hx))
  · exact uniformComposition_positive_bound hT hA hinterp hγ
      hbaseValue hbaseProduct hbaseLow hmember hvalue hproduct J hF hdecode hR hU

end ContinuousFlexibility.Statements
