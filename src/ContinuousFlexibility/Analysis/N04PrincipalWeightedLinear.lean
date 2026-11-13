import ContinuousFlexibility.Analysis.N04PrincipalWeightedPrefix
import ContinuousFlexibility.Analysis.N04RealizationFixedSpatialProduct
import ContinuousFlexibility.Analysis.N04RealizationCubicRegularity
import ContinuousFlexibility.Analysis.N04RealizationPotentialRegularity
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization
import ContinuousFlexibility.Analysis.SpacesCylinderEvenJets

/-!
# Linear operations on weighted current towers

These estimates retain the same parameter domain and external piece
weight. Increasing the low order, changing an envelope, taking sums, and
taking coordinate derivatives only change the uniform constants or the
high-order loss. The regularity tower can always be replaced by any
genuine tower of the same actual family.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {ι : Type*} {U : Set X} {Ω : Set PolarPoint}

private theorem n04Principal_weightedTower_jet_congr
    {f g : X → ℝ} (J : SmoothDirections U f) (K : SmoothDirections U g)
    (heq : ∀ x ∈ U, f x = g x) (k : ℕ) {x : X} (hx : x ∈ U)
    (v : Fin k → X) : K.D k x v = J.D k x v := by
  have h := HasProjectiveJetsOn.unique K.open_domain
    K.hasProjectiveJetsOn (J.congr heq).hasProjectiveJetsOn k x hx
  exact congrArg (fun A : X [×k]→L[ℝ] ℝ => A v) h

/-- Increasing the low order preserves all weighted bounds. -/
theorem n04Principal_weightedTower_monoBase
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p)
    (E W : ι → ℝ) (hE : ∀ m, 1 ≤ E m) (hW : ∀ m, 0 ≤ W m)
    {base base' : ℕ} (hbase : base ≤ base')
    {f : ι → X → PolarPoint → ℝ}
    (R : ∀ m, MixedJetRegularity U Ω (f m))
    (hb : N04PrincipalWeightedTowerBounds p base E W R) :
    N04PrincipalWeightedTowerBounds p base' E W R := by
  intro k
  obtain ⟨loss, hloss⟩ := hb k
  refine ⟨loss, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := hloss s
  refine ⟨B, hB, ?_⟩
  intro m a b hab q hq x hx hlow v
  exact (hbound m a b hab q hq x hx ((hp hbase x).trans hlow) v).trans
    (mul_le_mul_of_nonneg_left (oneHighVariationWeight_mono hp hbase le_rfl x v)
      (mul_nonneg (mul_nonneg hB.le
        (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)) (hW m)))

/-- A larger external weight needs no change in the derivative loss. -/
theorem n04Principal_weightedTower_weight_mono
    (p : ℕ → Seminorm ℝ X) (base : ℕ) (E W V : ι → ℝ)
    (hE : ∀ m, 1 ≤ E m) (hWV : ∀ m, W m ≤ V m)
    {f : ι → X → PolarPoint → ℝ}
    (R : ∀ m, MixedJetRegularity U Ω (f m))
    (hb : N04PrincipalWeightedTowerBounds p base E W R) :
    N04PrincipalWeightedTowerBounds p base E V R := by
  intro k
  obtain ⟨loss, hloss⟩ := hb k
  refine ⟨loss, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := hloss s
  refine ⟨B, hB, ?_⟩
  intro m a b hab q hq x hx hlow v
  exact (hbound m a b hab q hq x hx hlow v).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hWV m)
        (mul_nonneg hB.le (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)))
      (oneHighVariationWeight_nonneg _ _ _ _ _))

/-- A piece weight dominated up to an envelope power can be replaced by
the dominating weight with one uniform change of coefficient. -/
theorem n04Principal_weightedTower_weight_envelope
    (p : ℕ → Seminorm ℝ X) (base : ℕ) (E W V : ι → ℝ)
    (hE : ∀ m, 1 ≤ E m) (hV : ∀ m, 0 ≤ V m) (C A : ℝ)
    (hWV : ∀ m, W m ≤ C * E m ^ A * V m)
    {f : ι → X → PolarPoint → ℝ}
    (R : ∀ m, MixedJetRegularity U Ω (f m))
    (hb : N04PrincipalWeightedTowerBounds p base E W R) :
    N04PrincipalWeightedTowerBounds p base E V R := by
  intro k
  obtain ⟨loss, hloss⟩ := hb k
  refine ⟨loss, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := hloss s
  obtain ⟨D, hD, hpack⟩ := coefficientEnvelope_pack (B * C) (B + A)
  refine ⟨D, hD, ?_⟩
  intro m a b hab q hq x hx hlow v
  have he : 0 < E m := zero_lt_one.trans_le (hE m)
  have hw := oneHighVariationWeight_nonneg p base (s + loss) x v
  have hfirst : B * E m ^ B * W m * oneHighVariationWeight p base (s + loss) x v ≤
      B * E m ^ B * (C * E m ^ A * V m) *
        oneHighVariationWeight p base (s + loss) x v := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hWV m)
      (mul_nonneg hB.le (Real.rpow_nonneg he.le B))) hw
  have hlast := mul_le_mul_of_nonneg_right (hpack (E m) (hE m))
    (mul_nonneg (hV m) hw)
  apply (hbound m a b hab q hq x hx hlow v).trans
  apply hfirst.trans
  rw [Real.rpow_add he] at hlast
  convert hlast using 1 <;> ring

/-- The numerical envelope itself may be enlarged. -/
theorem n04Principal_weightedTower_envelope_mono
    (p : ℕ → Seminorm ℝ X) (base : ℕ) (E F W : ι → ℝ)
    (hE : ∀ m, 1 ≤ E m) (hEF : ∀ m, E m ≤ F m) (hW : ∀ m, 0 ≤ W m)
    {f : ι → X → PolarPoint → ℝ}
    (R : ∀ m, MixedJetRegularity U Ω (f m))
    (hb : N04PrincipalWeightedTowerBounds p base E W R) :
    N04PrincipalWeightedTowerBounds p base F W R := by
  intro k
  obtain ⟨loss, hloss⟩ := hb k
  refine ⟨loss, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := hloss s
  refine ⟨B, hB, ?_⟩
  intro m a b hab q hq x hx hlow v
  exact (hbound m a b hab q hq x hx hlow v).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (zero_le_one.trans (hE m)) (hEF m) hB.le) hB.le)
        (hW m)) (oneHighVariationWeight_nonneg _ _ _ _ _))

/-- Equality of the actual spatial families transports estimates to an
arbitrary genuine output tower. -/
theorem n04Principal_weightedTower_congr
    (p : ℕ → Seminorm ℝ X) (base : ℕ) (E W : ι → ℝ)
    (hΩ : IsOpen Ω) {f g : ι → X → PolarPoint → ℝ}
    (R : ∀ m, MixedJetRegularity U Ω (f m))
    (S : ∀ m, MixedJetRegularity U Ω (g m))
    (heq : ∀ m x, x ∈ U → EqOn (f m x) (g m x) Ω)
    (hb : N04PrincipalWeightedTowerBounds p base E W R) :
    N04PrincipalWeightedTowerBounds p base E W S := by
  intro k
  obtain ⟨loss, hloss⟩ := hb k
  refine ⟨loss, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := hloss s
  refine ⟨B, hB, ?_⟩
  intro m a b hab q hq x hx hlow v
  rw [n04Principal_weightedTower_jet_congr
    ((R m).parameter a b q hq) ((S m).parameter a b q hq)
    (fun y hy => mixedDerivative_eq_of_eqOn hΩ
      ((R m).spatial y hy) ((S m).spatial y hy) (heq m y hy) a b hq) k hx v]
  exact hbound m a b hab q hq x hx hlow v

private theorem n04Principal_weightedTower_of_addNorm
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (base : ℕ) (E W : ι → ℝ)
    (hE : ∀ m, 1 ≤ E m) (hW : ∀ m, 0 ≤ W m)
    {f g h : ι → X → PolarPoint → ℝ}
    (RF : ∀ m, MixedJetRegularity U Ω (f m))
    (RG : ∀ m, MixedJetRegularity U Ω (g m))
    (RH : ∀ m, MixedJetRegularity U Ω (h m))
    (hnorm : ∀ m a b q (hq : q ∈ Ω) k x, x ∈ U → ∀ v : Fin k → X,
      ‖((RH m).parameter a b q hq).D k x v‖ ≤
        ‖((RF m).parameter a b q hq).D k x v‖ +
          ‖((RG m).parameter a b q hq).D k x v‖)
    (hf : N04PrincipalWeightedTowerBounds p base E W RF)
    (hg : N04PrincipalWeightedTowerBounds p base E W RG) :
    N04PrincipalWeightedTowerBounds p base E W RH := by
  intro k
  obtain ⟨lf, hlf⟩ := hf k
  obtain ⟨lg, hlg⟩ := hg k
  refine ⟨max lf lg, fun s => ?_⟩
  obtain ⟨Bf, hBf, hfb⟩ := hlf s
  obtain ⟨Bg, hBg, hgb⟩ := hlg s
  refine ⟨Bf + Bg, add_pos hBf hBg, ?_⟩
  intro m a b hab q hq x hx hlow v
  have he : 0 ≤ E m := zero_le_one.trans (hE m)
  have hw := oneHighVariationWeight_nonneg p base (s + max lf lg) x v
  have hbf := (hfb m a b hab q hq x hx hlow v).trans
    (mul_le_mul_of_nonneg_left
      (oneHighVariationWeight_mono hp le_rfl
        (Nat.add_le_add_left (le_max_left lf lg) s) x v)
      (mul_nonneg (mul_nonneg hBf.le (Real.rpow_nonneg he _)) (hW m)))
  have hbg := (hgb m a b hab q hq x hx hlow v).trans
    (mul_le_mul_of_nonneg_left
      (oneHighVariationWeight_mono hp le_rfl
        (Nat.add_le_add_left (le_max_right lf lg) s) x v)
      (mul_nonneg (mul_nonneg hBg.le (Real.rpow_nonneg he _)) (hW m)))
  have hraise (c : ℝ) (hc : 0 ≤ c) (hcB : c ≤ Bf + Bg) :
      c * E m ^ c * W m * oneHighVariationWeight p base (s + max lf lg) x v ≤
        c * E m ^ (Bf + Bg) * W m *
          oneHighVariationWeight p base (s + max lf lg) x v :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (hE m) hcB) hc) (hW m)) hw
  calc
    _ ≤ ‖((RF m).parameter a b q hq).D k x v‖ +
          ‖((RG m).parameter a b q hq).D k x v‖ := hnorm m a b q hq k x hx v
    _ ≤ Bf * E m ^ Bf * W m * oneHighVariationWeight p base (s + max lf lg) x v +
          Bg * E m ^ Bg * W m * oneHighVariationWeight p base (s + max lf lg) x v :=
      add_le_add hbf hbg
    _ ≤ Bf * E m ^ (Bf + Bg) * W m * oneHighVariationWeight p base (s + max lf lg) x v +
          Bg * E m ^ (Bf + Bg) * W m * oneHighVariationWeight p base (s + max lf lg) x v :=
      add_le_add (hraise Bf hBf.le (le_add_of_nonneg_right hBg.le))
        (hraise Bg hBg.le (le_add_of_nonneg_left hBf.le))
    _ = _ := by ring

/-- Addition retains one copy of the common external weight. -/
theorem n04Principal_weightedTower_add
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (base : ℕ) (E W : ι → ℝ)
    (hE : ∀ m, 1 ≤ E m) (hW : ∀ m, 0 ≤ W m) (hΩ : IsOpen Ω)
    {f g : ι → X → PolarPoint → ℝ}
    (RF : ∀ m, MixedJetRegularity U Ω (f m))
    (RG : ∀ m, MixedJetRegularity U Ω (g m))
    (RH : ∀ m, MixedJetRegularity U Ω (fun x q => f m x q + g m x q))
    (hf : N04PrincipalWeightedTowerBounds p base E W RF)
    (hg : N04PrincipalWeightedTowerBounds p base E W RG) :
    N04PrincipalWeightedTowerBounds p base E W RH := by
  apply n04Principal_weightedTower_of_addNorm p hp base E W hE hW RF RG RH ?_ hf hg
  intro m a b q hq k x hx v
  let J := smoothDirectionsAdd ((RF m).parameter a b q hq) ((RG m).parameter a b q hq)
  have hd := n04Principal_weightedTower_jet_congr J ((RH m).parameter a b q hq)
    (fun y hy => (mixedDerivative_add_on_open hΩ
      ((RF m).spatial y hy) ((RG m).spatial y hy) a b hq).symm) k hx v
  rw [hd]
  exact norm_add_le _ _

/-- Negation preserves the same constants and high-order loss. -/
theorem n04Principal_weightedTower_neg
    (p : ℕ → Seminorm ℝ X) (base : ℕ) (E W : ι → ℝ)
    {f : ι → X → PolarPoint → ℝ}
    (RF : ∀ m, MixedJetRegularity U Ω (f m))
    (RN : ∀ m, MixedJetRegularity U Ω (fun x q => -f m x q))
    (hf : N04PrincipalWeightedTowerBounds p base E W RF) :
    N04PrincipalWeightedTowerBounds p base E W RN := by
  intro k
  obtain ⟨loss, hloss⟩ := hf k
  refine ⟨loss, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := hloss s
  refine ⟨B, hB, ?_⟩
  intro m a b hab q hq x hx hlow v
  have hd := n04Realization_smoothDirections_D_const_mul
    ((RF m).parameter a b q hq) ((RN m).parameter a b q hq) (-1)
    (fun y _ => by
      simpa only [neg_one_mul] using
        spaces_mixedDerivative_const_mul (f m y) (-1) a b q) k hx v
  rw [hd, norm_mul]
  simpa only [norm_neg, norm_one, one_mul] using hbound m a b hab q hq x hx hlow v

/-- Subtraction also retains one copy of the common external weight. -/
theorem n04Principal_weightedTower_sub
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (base : ℕ) (E W : ι → ℝ)
    (hE : ∀ m, 1 ≤ E m) (hW : ∀ m, 0 ≤ W m) (hΩ : IsOpen Ω)
    {f g : ι → X → PolarPoint → ℝ}
    (RF : ∀ m, MixedJetRegularity U Ω (f m))
    (RG : ∀ m, MixedJetRegularity U Ω (g m))
    (RH : ∀ m, MixedJetRegularity U Ω (fun x q => f m x q - g m x q))
    (hf : N04PrincipalWeightedTowerBounds p base E W RF)
    (hg : N04PrincipalWeightedTowerBounds p base E W RG) :
    N04PrincipalWeightedTowerBounds p base E W RH := by
  apply n04Principal_weightedTower_of_addNorm p hp base E W hE hW RF RG RH ?_ hf hg
  intro m a b q hq k x hx v
  let Jf := (RF m).parameter a b q hq
  let Jg := (RG m).parameter a b q hq
  let L : ℝ →L[ℝ] ℝ := -ContinuousLinearMap.id ℝ ℝ
  let Jn := smoothDirections_postcompCLM Jg L
  let J := smoothDirectionsAdd Jf Jn
  have he : ∀ y ∈ U,
      mixedDerivative a b (f m y) q + L (mixedDerivative a b (g m y) q) =
        mixedDerivative a b (fun p => f m y p - g m y p) q := by
    intro y hy
    simpa only [L, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
      sub_eq_add_neg] using (mixedDerivative_sub_of_contDiffOn hΩ
        ((RF m).spatial y hy) ((RG m).spatial y hy) a b hq).symm
  have hd := n04Principal_weightedTower_jet_congr J ((RH m).parameter a b q hq) he k hx v
  have hd' : ((RH m).parameter a b q hq).D k x v = Jf.D k x v - Jg.D k x v := by
    calc
      _ = J.D k x v := hd
      _ = Jf.D k x v + Jn.D k x v := rfl
      _ = _ := by
        rw [smoothDirections_postcompCLM_D_apply]
        simp only [L, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
          sub_eq_add_neg]
  rw [hd']
  exact norm_sub_le _ _

/-- A fixed reference field has weight one: its positive parameter
derivatives vanish and its value is bounded by the spatial envelope. -/
theorem n04Principal_weightedTower_fixedSpatial
    (p : ℕ → Seminorm ℝ X) (base : ℕ) (E : ι → ℝ) (hE : ∀ m, 1 ≤ E m)
    (f₀ : ι → PolarPoint → ℝ)
    (R : ∀ m, MixedJetRegularity U Ω (fun _ => f₀ m))
    (hbound : ∀ s : ℕ, ∃ C A : ℝ,
      ∀ m a b, a + b ≤ s → ∀ q ∈ Ω,
        ‖mixedDerivative a b (f₀ m) q‖ ≤ C * E m ^ A) :
    N04PrincipalWeightedTowerBounds p base E (fun _ => 1) R := by
  intro k
  refine ⟨0, fun s => ?_⟩
  obtain ⟨C, A, hCA⟩ := hbound s
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack C A
  refine ⟨B, hB, ?_⟩
  intro m a b hab q hq x hx hlow v
  have he := Real.rpow_nonneg (zero_le_one.trans (hE m)) B
  by_cases hk : k = 0
  · subst k
    rw [smoothDirections_D_zero_apply ((R m).parameter a b q hq) hx v]
    have hb := (hCA m a b hab q hq).trans (hpack (E m) (hE m))
    have hle : 1 ≤ oneHighVariationWeight p base (s + 0) x v := by
      simp only [oneHighVariationWeight, Finset.univ_eq_empty, Finset.prod_empty,
        Finset.sum_empty, mul_one, add_zero]
      exact le_add_of_nonneg_right (apply_nonneg _ _)
    simpa only [mul_one] using hb.trans
      (le_mul_of_one_le_right (mul_nonneg hB.le he) hle)
  · rw [smoothDirections_D_constant ((R m).parameter a b q hq)
      (Nat.pos_of_ne_zero hk) hx v, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hB.le he) zero_le_one)
      (oneHighVariationWeight_nonneg _ _ _ _ _)

/-- A coordinate partial shifts one spatial order, uniformly in the
parameter order and piece index. -/
theorem n04Principal_weightedTower_coordinatePartial
    (p : ℕ → Seminorm ℝ X) (base : ℕ) (E W : ι → ℝ)
    (hΩ : IsOpen Ω) (radial : Bool) {f : ι → X → PolarPoint → ℝ}
    (R : ∀ m, MixedJetRegularity U Ω (f m))
    (RD : ∀ m, MixedJetRegularity U Ω
      (fun x => if radial then radialPartial (f m x) else angularPartial (f m x)))
    (hb : N04PrincipalWeightedTowerBounds p base E W R) :
    N04PrincipalWeightedTowerBounds p base E W RD := by
  intro k
  obtain ⟨loss, hloss⟩ := hb k
  refine ⟨loss + 1, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := hloss (s + 1)
  refine ⟨B, hB, ?_⟩
  intro m a b hab q hq x hx hlow v
  have hindex : s + 1 + loss = s + (loss + 1) := by omega
  cases radial with
  | false =>
      have hd := n04Principal_weightedTower_jet_congr
        ((R m).parameter a (b + 1) q hq) ((RD m).parameter a b q hq)
        (fun y hy => (mixedDerivative_angularPartial hΩ ((R m).spatial y hy) a b hq).symm)
        k hx v
      rw [hd]
      simpa only [hindex] using hbound m a (b + 1) (by omega) q hq x hx hlow v
  | true =>
      have hd := n04Principal_weightedTower_jet_congr
        ((R m).parameter (a + 1) b q hq) ((RD m).parameter a b q hq)
        (fun y hy => (mixedDerivative_radialPartial hΩ ((R m).spatial y hy) a b hq).symm)
        k hx v
      rw [hd]
      simpa only [hindex] using hbound m (a + 1) b (by omega) q hq x hx hlow v

end ContinuousFlexibility.Analysis
