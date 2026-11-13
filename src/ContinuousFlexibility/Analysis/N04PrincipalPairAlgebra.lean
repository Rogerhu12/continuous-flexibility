import ContinuousFlexibility.Analysis.N04PrincipalWeightedLinear
import ContinuousFlexibility.Analysis.N04PrincipalWeightedProduct

/-!
# Paired current and reference fields

The current field and its fixed reference have full envelope bounds. Their
actual difference has the designated external weight. This interface is
closed under the finite differential expressions used by the principal
and potential formulas, with one low seminorm chosen for each expression.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {ι : Type*} {U : Set X} {Ω : Set PolarPoint}

/-- Paired full, fixed-reference, and actual-difference estimates on a
single parameter domain. Only the difference carries the external weight. -/
def N04PrincipalPairBounds (p : ℕ → Seminorm ℝ X) (E W : ι → ℝ)
    (f : ι → X → PolarPoint → ℝ) (f₀ : ι → PolarPoint → ℝ) : Prop :=
  ∃ base : ℕ,
    ∃ RF : ∀ m, MixedJetRegularity U Ω (f m),
    ∃ RR : ∀ m, MixedJetRegularity U Ω (fun _ => f₀ m),
    ∃ RD : ∀ m, MixedJetRegularity U Ω (fun x q => f m x q - f₀ m q),
      N04PrincipalWeightedTowerBounds p base E (fun _ => 1) RF ∧
      N04PrincipalWeightedTowerBounds p base E (fun _ => 1) RR ∧
      N04PrincipalWeightedTowerBounds p base E W RD

private def n04Principal_pairRegularity_neg
    {f : X → PolarPoint → ℝ} (R : MixedJetRegularity U Ω f)
    (hU : IsOpen U) (hΩ : IsOpen Ω) :
    MixedJetRegularity U Ω (fun x q => -f x q) :=
  R.scalarComp hU hΩ isOpen_univ contDiffOn_id.neg (fun _ _ _ _ => mem_univ _)

private theorem n04Principal_pairRaise
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (E W : ι → ℝ)
    (hE : ∀ m, 1 ≤ E m) (hW : ∀ m, 0 ≤ W m) {b b' : ℕ} (hbb : b ≤ b')
    {f : ι → X → PolarPoint → ℝ} {f₀ : ι → PolarPoint → ℝ}
    (RF : ∀ m, MixedJetRegularity U Ω (f m))
    (RR : ∀ m, MixedJetRegularity U Ω (fun _ => f₀ m))
    (RD : ∀ m, MixedJetRegularity U Ω (fun x q => f m x q - f₀ m q))
    (hf : N04PrincipalWeightedTowerBounds p b E (fun _ => 1) RF)
    (hr : N04PrincipalWeightedTowerBounds p b E (fun _ => 1) RR)
    (hd : N04PrincipalWeightedTowerBounds p b E W RD) :
    N04PrincipalWeightedTowerBounds p b' E (fun _ => 1) RF ∧
      N04PrincipalWeightedTowerBounds p b' E (fun _ => 1) RR ∧
      N04PrincipalWeightedTowerBounds p b' E W RD :=
  ⟨n04Principal_weightedTower_monoBase p hp E (fun _ => 1) hE
      (fun _ => zero_le_one) hbb RF hf,
    n04Principal_weightedTower_monoBase p hp E (fun _ => 1) hE
      (fun _ => zero_le_one) hbb RR hr,
    n04Principal_weightedTower_monoBase p hp E W hE hW hbb RD hd⟩

namespace N04PrincipalPairBounds

variable {p : ℕ → Seminorm ℝ X} {E W : ι → ℝ}
  {f g : ι → X → PolarPoint → ℝ} {f₀ g₀ : ι → PolarPoint → ℝ}

theorem spatial (hf : N04PrincipalPairBounds (U := U) (Ω := Ω) p E W f f₀)
    (m : ι) (x : X) (hx : x ∈ U) : ContDiffOn ℝ ∞ (f m x) Ω :=
  (hf.choose_spec.choose m).spatial x hx

theorem reference_spatial (hf : N04PrincipalPairBounds (U := U) (Ω := Ω) p E W f f₀)
    (m : ι) (x : X) (hx : x ∈ U) : ContDiffOn ℝ ∞ (f₀ m) Ω :=
  (hf.choose_spec.choose_spec.choose m).spatial x hx

/-- Paired bounds depend only on the displayed fields on the open strip. -/
theorem congr (hf : N04PrincipalPairBounds (U := U) (Ω := Ω) p E W f f₀)
    (hΩ : IsOpen Ω)
    (he : ∀ m x, x ∈ U → EqOn (f m x) (g m x) Ω)
    (he₀ : ∀ m, EqOn (f₀ m) (g₀ m) Ω) :
    N04PrincipalPairBounds (U := U) (Ω := Ω) p E W g g₀ := by
  obtain ⟨base, RF, RR, RD, hF, hR, hD⟩ := hf
  let SF : ∀ m, MixedJetRegularity U Ω (g m) := fun m =>
    (RF m).congr hΩ
      (fun x hx => ((RF m).spatial x hx).congr (fun q hq => (he m x hx hq).symm))
      (he m)
  let SR : ∀ m, MixedJetRegularity U Ω (fun _ => g₀ m) := fun m =>
    (RR m).congr hΩ
      (fun x hx => ((RR m).spatial x hx).congr (fun q hq => (he₀ m hq).symm))
      (fun _ _ => he₀ m)
  have hed : ∀ m x, x ∈ U →
      EqOn (fun q => f m x q - f₀ m q) (fun q => g m x q - g₀ m q) Ω := by
    intro m x hx q hq
    rw [he m x hx hq, he₀ m hq]
  let SD : ∀ m, MixedJetRegularity U Ω (fun x q => g m x q - g₀ m q) := fun m =>
    (RD m).congr hΩ (fun x hx => ((SF m).spatial x hx).sub ((SR m).spatial x hx)) (hed m)
  exact ⟨base, SF, SR, SD,
    n04Principal_weightedTower_congr p base E (fun _ => 1) hΩ RF SF he hF,
    n04Principal_weightedTower_congr p base E (fun _ => 1) hΩ RR SR
      (fun m _ _ => he₀ m) hR,
    n04Principal_weightedTower_congr p base E W hΩ RD SD hed hD⟩

/-- A fixed spatial reference is paired with itself. Its difference is
identically zero, so any nonnegative external weight is allowed. -/
theorem fixedSpatial (p : ℕ → Seminorm ℝ X) (E W : ι → ℝ)
    (hU : IsOpen U) (hE : ∀ m, 1 ≤ E m) (hW : ∀ m, 0 ≤ W m)
    (f₀ : ι → PolarPoint → ℝ) (hspatial : ∀ m, ContDiffOn ℝ ∞ (f₀ m) Ω)
    (hbound : ∀ s : ℕ, ∃ C A : ℝ,
      ∀ m a b, a + b ≤ s → ∀ q ∈ Ω,
        ‖mixedDerivative a b (f₀ m) q‖ ≤ C * E m ^ A) :
    N04PrincipalPairBounds (U := U) (Ω := Ω) p E W (fun m _ => f₀ m) f₀ := by
  let R : ∀ m, MixedJetRegularity U Ω (fun _ => f₀ m) := fun m =>
    n04Realization_mixedJetRegularity_fixedSpatial hU (hspatial m)
  let RD : ∀ m, MixedJetRegularity U Ω (fun _ q => f₀ m q - f₀ m q) := fun m =>
    n04Realization_mixedJetRegularity_fixedSpatial hU ((hspatial m).sub (hspatial m))
  have hR := n04Principal_weightedTower_fixedSpatial p 0 E hE f₀ R hbound
  refine ⟨0, R, R, RD, hR, hR, ?_⟩
  intro k
  refine ⟨0, fun s => ⟨1, zero_lt_one, ?_⟩⟩
  intro m a b hab q hq x hx hlow v
  have hd := n04Realization_smoothDirections_D_const_mul
    ((RD m).parameter a b q hq) ((RD m).parameter a b q hq) 0
    (fun _ _ => by simp only [sub_self, mixedDerivative_fun_zero, zero_mul]) k hx v
  have hd0 : ((RD m).parameter a b q hq).D k x v = 0 := by
    simpa only [zero_mul] using hd
  rw [hd0, norm_zero]
  exact mul_nonneg
    (mul_nonneg (mul_nonneg zero_le_one
      (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)) (hW m))
    (oneHighVariationWeight_nonneg _ _ _ _ _)

theorem neg (hf : N04PrincipalPairBounds (U := U) (Ω := Ω) p E W f f₀)
    (hU : IsOpen U) (hΩ : IsOpen Ω) :
    N04PrincipalPairBounds (U := U) (Ω := Ω) p E W
      (fun m x q => -f m x q) (fun m q => -f₀ m q) := by
  obtain ⟨base, RF, RR, RD, hF, hR, hD⟩ := hf
  let NF := fun m => n04Principal_pairRegularity_neg (RF m) hU hΩ
  let NR := fun m => n04Principal_pairRegularity_neg (RR m) hU hΩ
  let ND := fun m => n04Principal_pairRegularity_neg (RD m) hU hΩ
  have he : ∀ m x, x ∈ U →
      EqOn (fun q => -(f m x q - f₀ m q)) (fun q => -f m x q - -f₀ m q) Ω := by
    intro m x hx q hq
    ring
  let SD : ∀ m, MixedJetRegularity U Ω (fun x q => -f m x q - -f₀ m q) := fun m =>
    (ND m).congr hΩ (fun x hx => ((NF m).spatial x hx).sub ((NR m).spatial x hx)) (he m)
  exact ⟨base, NF, NR, SD,
    n04Principal_weightedTower_neg p base E (fun _ => 1) RF NF hF,
    n04Principal_weightedTower_neg p base E (fun _ => 1) RR NR hR,
    n04Principal_weightedTower_congr p base E W hΩ ND SD he
      (n04Principal_weightedTower_neg p base E W RD ND hD)⟩

theorem add (hf : N04PrincipalPairBounds (U := U) (Ω := Ω) p E W f f₀)
    (hg : N04PrincipalPairBounds (U := U) (Ω := Ω) p E W g g₀)
    (hp : Monotone p) (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hE : ∀ m, 1 ≤ E m) (hW : ∀ m, 0 ≤ W m) :
    N04PrincipalPairBounds (U := U) (Ω := Ω) p E W
      (fun m x q => f m x q + g m x q) (fun m q => f₀ m q + g₀ m q) := by
  obtain ⟨bf, RF, RR, RD, hF, hR, hD⟩ := hf
  obtain ⟨bg, SF, SR, SD, hG, hS, hQ⟩ := hg
  have hf' := n04Principal_pairRaise p hp E W hE hW (le_max_left bf bg) RF RR RD hF hR hD
  have hg' := n04Principal_pairRaise p hp E W hE hW (le_max_right bf bg) SF SR SD hG hS hQ
  let TF := fun m => (RF m).add (SF m) hU hΩ
  let TR := fun m => (RR m).add (SR m) hU hΩ
  let TD := fun m => (RD m).add (SD m) hU hΩ
  have he : ∀ m x, x ∈ U →
      EqOn (fun q => (f m x q - f₀ m q) + (g m x q - g₀ m q))
        (fun q => (f m x q + g m x q) - (f₀ m q + g₀ m q)) Ω := by
    intro m x hx q hq
    ring
  let D : ∀ m, MixedJetRegularity U Ω
      (fun x q => (f m x q + g m x q) - (f₀ m q + g₀ m q)) := fun m =>
    (TD m).congr hΩ (fun x hx => ((TF m).spatial x hx).sub ((TR m).spatial x hx)) (he m)
  exact ⟨max bf bg, TF, TR, D,
    n04Principal_weightedTower_add p hp (max bf bg) E (fun _ => 1) hE
      (fun _ => zero_le_one) hΩ RF SF TF hf'.1 hg'.1,
    n04Principal_weightedTower_add p hp (max bf bg) E (fun _ => 1) hE
      (fun _ => zero_le_one) hΩ RR SR TR hf'.2.1 hg'.2.1,
    n04Principal_weightedTower_congr p (max bf bg) E W hΩ TD D he
      (n04Principal_weightedTower_add p hp (max bf bg) E W hE hW hΩ
        RD SD TD hf'.2.2 hg'.2.2)⟩

theorem sub (hf : N04PrincipalPairBounds (U := U) (Ω := Ω) p E W f f₀)
    (hg : N04PrincipalPairBounds (U := U) (Ω := Ω) p E W g g₀)
    (hp : Monotone p) (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hE : ∀ m, 1 ≤ E m) (hW : ∀ m, 0 ≤ W m) :
    N04PrincipalPairBounds (U := U) (Ω := Ω) p E W
      (fun m x q => f m x q - g m x q) (fun m q => f₀ m q - g₀ m q) := by
  exact (hf.add (hg.neg hU hΩ) hp hU hΩ hE hW).congr hΩ
    (fun _ _ _ _ _ => by ring) (fun _ _ _ => by ring)

end N04PrincipalPairBounds

private theorem n04Principal_pair_zeroMixed (f : PolarPoint → ℝ) (q : PolarPoint) :
    mixedDerivative 0 0 f q = f q := by
  simp only [mixedDerivative, iteratedDeriv_zero, Prod.eta]

private theorem n04Principal_pairPartial_sub
    {f g : PolarPoint → ℝ} (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    (radial : Bool) {q : PolarPoint} (hq : q ∈ Ω) :
    (if radial then radialPartial (fun p => f p - g p) else
      angularPartial (fun p => f p - g p)) q =
        (if radial then radialPartial f else angularPartial f) q -
          (if radial then radialPartial g else angularPartial g) q := by
  cases radial with
  | false =>
      change angularPartial (fun p => f p - g p) q = angularPartial f q - angularPartial g q
      have hδ : angularPartial (fun p => f p - g p) q =
          mixedDerivative 0 1 (fun p => f p - g p) q := by
        simpa only [n04Principal_pair_zeroMixed, zero_add] using
          mixedDerivative_angularPartial hΩ (hf.sub hg) 0 0 hq
      have hf' : angularPartial f q = mixedDerivative 0 1 f q := by
        simpa only [n04Principal_pair_zeroMixed, zero_add] using
          mixedDerivative_angularPartial hΩ hf 0 0 hq
      have hg' : angularPartial g q = mixedDerivative 0 1 g q := by
        simpa only [n04Principal_pair_zeroMixed, zero_add] using
          mixedDerivative_angularPartial hΩ hg 0 0 hq
      rw [hδ, hf', hg', mixedDerivative_sub_of_contDiffOn hΩ hf hg 0 1 hq]
  | true =>
      change radialPartial (fun p => f p - g p) q = radialPartial f q - radialPartial g q
      have hδ : radialPartial (fun p => f p - g p) q =
          mixedDerivative 1 0 (fun p => f p - g p) q := by
        simpa only [n04Principal_pair_zeroMixed, zero_add] using
          mixedDerivative_radialPartial hΩ (hf.sub hg) 0 0 hq
      have hf' : radialPartial f q = mixedDerivative 1 0 f q := by
        simpa only [n04Principal_pair_zeroMixed, zero_add] using
          mixedDerivative_radialPartial hΩ hf 0 0 hq
      have hg' : radialPartial g q = mixedDerivative 1 0 g q := by
        simpa only [n04Principal_pair_zeroMixed, zero_add] using
          mixedDerivative_radialPartial hΩ hg 0 0 hq
      rw [hδ, hf', hg', mixedDerivative_sub_of_contDiffOn hΩ hf hg 1 0 hq]

namespace N04PrincipalPairBounds

variable {p : ℕ → Seminorm ℝ X} {E W : ι → ℝ}
  {f g : ι → X → PolarPoint → ℝ} {f₀ g₀ : ι → PolarPoint → ℝ}

theorem coordinatePartial
    (hf : N04PrincipalPairBounds (U := U) (Ω := Ω) p E W f f₀)
    (hΩ : IsOpen Ω) (radial : Bool) :
    N04PrincipalPairBounds (U := U) (Ω := Ω) p E W
      (fun m x => if radial then radialPartial (f m x) else angularPartial (f m x))
      (fun m => if radial then radialPartial (f₀ m) else angularPartial (f₀ m)) := by
  obtain ⟨base, RF, RR, RD, hF, hR, hD⟩ := hf
  let PF := fun m => n04Realization_mixedJetRegularity_coordinatePartial (RF m) hΩ radial
  let PR := fun m => n04Realization_mixedJetRegularity_coordinatePartial (RR m) hΩ radial
  let PD := fun m => n04Realization_mixedJetRegularity_coordinatePartial (RD m) hΩ radial
  have he : ∀ m x, x ∈ U →
      EqOn (if radial then radialPartial (fun q => f m x q - f₀ m q) else
          angularPartial (fun q => f m x q - f₀ m q))
        (fun q => (if radial then radialPartial (f m x) else angularPartial (f m x)) q -
          (if radial then radialPartial (f₀ m) else angularPartial (f₀ m)) q) Ω := by
    intro m x hx q hq
    exact n04Principal_pairPartial_sub hΩ ((RF m).spatial x hx) ((RR m).spatial x hx) radial hq
  let D : ∀ m, MixedJetRegularity U Ω (fun x q =>
      (if radial then radialPartial (f m x) else angularPartial (f m x)) q -
        (if radial then radialPartial (f₀ m) else angularPartial (f₀ m)) q) := fun m =>
    (PD m).congr hΩ (fun x hx => ((PF m).spatial x hx).sub ((PR m).spatial x hx)) (he m)
  exact ⟨base, PF, PR, D,
    n04Principal_weightedTower_coordinatePartial p base E (fun _ => 1) hΩ radial RF PF hF,
    n04Principal_weightedTower_coordinatePartial p base E (fun _ => 1) hΩ radial RR PR hR,
    n04Principal_weightedTower_congr p base E W hΩ PD D he
      (n04Principal_weightedTower_coordinatePartial p base E W hΩ radial RD PD hD)⟩

end N04PrincipalPairBounds

/-- Binary specialization of the finite-product estimate. -/
private theorem n04Principal_pairProduct
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hI : HasInterpolation p)
    (base : ℕ) (hU : IsOpen U) (hΩ : IsOpen Ω)
    (E W V : ι → ℝ) (hE : ∀ m, 1 ≤ E m)
    (hW : ∀ m, 0 < W m) (hV : ∀ m, 0 < V m)
    {f g : ι → X → PolarPoint → ℝ}
    (RF : ∀ m, MixedJetRegularity U Ω (f m))
    (RG : ∀ m, MixedJetRegularity U Ω (g m))
    (RP : ∀ m, MixedJetRegularity U Ω (fun x q => f m x q * g m x q))
    (hf : N04PrincipalWeightedTowerBounds p base E W RF)
    (hg : N04PrincipalWeightedTowerBounds p base E V RG) :
    ∃ b : ℕ, base ≤ b ∧
      N04PrincipalWeightedTowerBounds p b E (fun m => W m * V m) RP := by
  let F : Fin 2 → ι → X → PolarPoint → ℝ := Fin.cases f (fun _ => g)
  let weights : Fin 2 → ι → ℝ := Fin.cases W (fun _ => V)
  let R : ∀ i m, MixedJetRegularity U Ω (F i m) :=
    Fin.cases (motive := fun i => ∀ m, MixedJetRegularity U Ω (F i m)) RF (fun _ => RG)
  have hF0 : F 0 = f := by simp only [F, Fin.cases_zero]
  have hF1 : F 1 = g := by
    rw [show (1 : Fin 2) = (0 : Fin 1).succ from by decide]
    simp only [F, Fin.cases_succ]
  have hW0 : weights 0 = W := by simp only [weights, Fin.cases_zero]
  have hW1 : weights 1 = V := by
    rw [show (1 : Fin 2) = (0 : Fin 1).succ from by decide]
    simp only [weights, Fin.cases_succ]
  have he : ∀ m x, x ∈ U →
      EqOn (fun q => f m x q * g m x q) (fun q => ∏ i : Fin 2, F i m x q) Ω := by
    intro m x hx q hq
    simp only [Fin.prod_univ_two, hF0, hF1]
  let T : ∀ m, MixedJetRegularity U Ω (fun x q => ∏ i : Fin 2, F i m x q) := fun m =>
    (RP m).congr hΩ
      (fun x hx => ((RP m).spatial x hx).congr (fun q hq => (he m x hx hq).symm)) (he m)
  have hweight : ∀ i m, 0 < weights i m := by
    intro i
    fin_cases i
    · exact hW
    · exact hV
  have hinput : ∀ i, N04PrincipalWeightedTowerBounds p base E (weights i) (R i) := by
    intro i
    fin_cases i
    · exact hf
    · exact hg
  obtain ⟨b, hbase, hb⟩ := n04Principal_weightedTower_product p hp hI base base
    hU hΩ E weights hE hweight F R T hinput
  have hweights : (fun m => ∏ i : Fin 2, weights i m) = (fun m => W m * V m) := by
    funext m
    simp only [Fin.prod_univ_two, hW0, hW1]
  rw [hweights] at hb
  refine ⟨b, (le_max_left _ _).trans hbase, ?_⟩
  exact n04Principal_weightedTower_congr p b E (fun m => W m * V m) hΩ T RP
    (fun m x hx q hq => (he m x hx hq).symm) hb

namespace N04PrincipalPairBounds

variable {p : ℕ → Seminorm ℝ X} {E W : ι → ℝ}
  {f g : ι → X → PolarPoint → ℝ} {f₀ g₀ : ι → PolarPoint → ℝ}

/-- The difference of a product is expanded with exactly one weighted
difference in each term. -/
theorem mul (hf : N04PrincipalPairBounds (U := U) (Ω := Ω) p E W f f₀)
    (hg : N04PrincipalPairBounds (U := U) (Ω := Ω) p E W g g₀)
    (hp : Monotone p) (hI : HasInterpolation p) (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hE : ∀ m, 1 ≤ E m) (hW : ∀ m, 0 < W m) :
    N04PrincipalPairBounds (U := U) (Ω := Ω) p E W
      (fun m x q => f m x q * g m x q) (fun m q => f₀ m q * g₀ m q) := by
  obtain ⟨bf, RF, RR, RD, hF, hR, hD⟩ := hf
  obtain ⟨bg, SF, SR, SD, hG, hS, hQ⟩ := hg
  have hf' := n04Principal_pairRaise p hp E W hE (fun m => (hW m).le)
    (le_max_left bf bg) RF RR RD hF hR hD
  have hg' := n04Principal_pairRaise p hp E W hE (fun m => (hW m).le)
    (le_max_right bf bg) SF SR SD hG hS hQ
  let TF := fun m => (RF m).mul (SF m) hU hΩ
  let TR := fun m => (RR m).mul (SR m) hU hΩ
  let TD₁ := fun m => (RD m).mul (SF m) hU hΩ
  let TD₂ := fun m => (RR m).mul (SD m) hU hΩ
  obtain ⟨bF, hbF, hTF⟩ := n04Principal_pairProduct p hp hI (max bf bg) hU hΩ
    E (fun _ => 1) (fun _ => 1) hE (fun _ => zero_lt_one) (fun _ => zero_lt_one)
    RF SF TF hf'.1 hg'.1
  obtain ⟨bR, hbR, hTR⟩ := n04Principal_pairProduct p hp hI (max bf bg) hU hΩ
    E (fun _ => 1) (fun _ => 1) hE (fun _ => zero_lt_one) (fun _ => zero_lt_one)
    RR SR TR hf'.2.1 hg'.2.1
  obtain ⟨b₁, hb₁, hTD₁⟩ := n04Principal_pairProduct p hp hI (max bf bg) hU hΩ
    E W (fun _ => 1) hE hW (fun _ => zero_lt_one) RD SF TD₁ hf'.2.2 hg'.1
  obtain ⟨b₂, hb₂, hTD₂⟩ := n04Principal_pairProduct p hp hI (max bf bg) hU hΩ
    E (fun _ => 1) W hE (fun _ => zero_lt_one) hW RR SD TD₂ hf'.2.1 hg'.2.2
  have hTF' : N04PrincipalWeightedTowerBounds p bF E (fun _ => 1) TF := by
    simpa only [one_mul] using hTF
  have hTR' : N04PrincipalWeightedTowerBounds p bR E (fun _ => 1) TR := by
    simpa only [one_mul] using hTR
  have hTD₁' : N04PrincipalWeightedTowerBounds p b₁ E W TD₁ := by
    simpa only [mul_one] using hTD₁
  have hTD₂' : N04PrincipalWeightedTowerBounds p b₂ E W TD₂ := by
    simpa only [one_mul] using hTD₂
  let base := max (max bF bR) (max b₁ b₂)
  have hFbase : bF ≤ base := (le_max_left bF bR).trans (le_max_left _ _)
  have hRbase : bR ≤ base := (le_max_right bF bR).trans (le_max_left _ _)
  have h₁base : b₁ ≤ base := (le_max_left b₁ b₂).trans (le_max_right _ _)
  have h₂base : b₂ ≤ base := (le_max_right b₁ b₂).trans (le_max_right _ _)
  have hfull := n04Principal_weightedTower_monoBase p hp E (fun _ => 1) hE
    (fun _ => zero_le_one) hFbase TF hTF'
  have href := n04Principal_weightedTower_monoBase p hp E (fun _ => 1) hE
    (fun _ => zero_le_one) hRbase TR hTR'
  have hd₁ := n04Principal_weightedTower_monoBase p hp E W hE
    (fun m => (hW m).le) h₁base TD₁ hTD₁'
  have hd₂ := n04Principal_weightedTower_monoBase p hp E W hE
    (fun m => (hW m).le) h₂base TD₂ hTD₂'
  let TD := fun m => (TD₁ m).add (TD₂ m) hU hΩ
  have he : ∀ m x, x ∈ U →
      EqOn (fun q => (f m x q - f₀ m q) * g m x q + f₀ m q * (g m x q - g₀ m q))
        (fun q => f m x q * g m x q - f₀ m q * g₀ m q) Ω := by
    intro m x hx q hq
    ring
  let D : ∀ m, MixedJetRegularity U Ω
      (fun x q => f m x q * g m x q - f₀ m q * g₀ m q) := fun m =>
    (TD m).congr hΩ (fun x hx => ((TF m).spatial x hx).sub ((TR m).spatial x hx)) (he m)
  exact ⟨base, TF, TR, D, hfull, href,
    n04Principal_weightedTower_congr p base E W hΩ TD D he
      (n04Principal_weightedTower_add p hp base E W hE (fun m => (hW m).le)
        hΩ TD₁ TD₂ TD hd₁ hd₂)⟩

end N04PrincipalPairBounds

end ContinuousFlexibility.Analysis
