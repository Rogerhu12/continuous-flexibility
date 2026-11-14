import ContinuousFlexibility.Analysis.N04NegativeChartFixedBaseFamilies
import ContinuousFlexibility.Analysis.N04RealizationFixedBasePrefix
import ContinuousFlexibility.Analysis.CircleJointEvaluation
import ContinuousFlexibility.Analysis.CircleSobolevPointwise

/-!
# The first angular order at one fixed low base

The scalar jets are the actual evaluations of the circle-valued tower.
The fixed low base pays for the value and first angular derivative. Every
remaining angular derivative and every state slot keeps its own power.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {X I : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

private theorem gradedFamily_first_prefix
    {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {U : Set X} {f : I → X → Y}
    (hf : N04FixedBaseSmoothFamilyOn p q U f) (hp : Monotone p) (hI : HasInterpolation p)
    (requestedBase : ℕ) :
    ∃ J₀ : ∀ i, SmoothDirections U (f i),
    ∃ base : ℕ, requestedBase ≤ base ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ℕ, k ≤ K → ∀ j : ℕ, j ≤ s + 1 → ∀ i,
      ∀ x ∈ U, p base x ≤ 1 → ∀ v : Fin k → X,
      (∀ d, p base (v d) ≤ 1) → ∀ R : ℝ, 1 ≤ R →
      p (base + s + shift * K + 1) x ≤ R →
      (∀ d, p (base + s + shift * K + 1) (v d) ≤ R) →
        q (j + 1) ((J₀ i).D k x v) ≤
          C * R ^ (((j - 1 + shift * k : ℕ) : ℝ) /
            (((s + shift * K : ℕ) : ℝ) + 1)) := by
  classical
  obtain ⟨J₀, oldBase, hjet⟩ := hf
  choose L hL using hjet
  obtain ⟨base, hbase, hprefix⟩ := n04Realization_fixedBase_prefix_power
    p hp hI (max requestedBase oldBase) (fun k => L k + 2)
  have hold : oldBase ≤ base := (le_max_right _ _).trans hbase
  refine ⟨J₀, base, (le_max_left _ _).trans hbase, fun K => ?_⟩
  obtain ⟨shift, hshift⟩ := hprefix K
  refine ⟨shift, fun s => ?_⟩
  let A : Type := Fin (K + 1) × Fin (s + 2)
  choose c hc hcb using fun a : A => hL a.1.val 1 zero_le_one (a.2.val + 1)
  let C₀ : ℝ := 1 + ∑ a : A, c a
  have hC₀ : 0 ≤ C₀ := add_nonneg zero_le_one (Finset.sum_nonneg (fun a _ => hc a))
  have hcC (a : A) : c a ≤ C₀ :=
    (Finset.single_le_sum (fun a _ => hc a) (Finset.mem_univ a)).trans
      (le_add_of_nonneg_left zero_le_one)
  obtain ⟨Ci, hCi, hpower⟩ := hshift s
  refine ⟨C₀ * Ci, mul_nonneg hC₀ (zero_le_one.trans hCi), ?_⟩
  intro k hk j hj i x hx hxlow v hvlow R hR hxhigh hvhigh
  let a : A := (⟨k, Nat.lt_succ_of_le hk⟩, ⟨j, by omega⟩)
  have hraw : q (j + 1) ((J₀ i).D k x v) ≤
      c a * oneHighVariationWeight p oldBase (j + 1 + L k) x v := by
    simpa only [a, tameJetSize, oneHighVariationWeight] using
      hcb a i x hx ((hp hold x).trans hxlow) v
  have hn : j - 1 ≤ s := by omega
  have horder : j + 1 + L k ≤ j - 1 + (L k + 2) := by omega
  have hw := (oneHighVariationWeight_mono hp hold horder x v).trans
    (hpower k hk (j - 1) hn x hxlow v hvlow R hR hxhigh hvhigh)
  calc
    _ ≤ c a * oneHighVariationWeight p oldBase (j + 1 + L k) x v := hraw
    _ ≤ C₀ * oneHighVariationWeight p oldBase (j + 1 + L k) x v :=
      mul_le_mul_of_nonneg_right (hcC a) (oneHighVariationWeight_nonneg _ _ _ _ _)
    _ ≤ C₀ * (Ci * R ^ (((j - 1 + shift * k : ℕ) : ℝ) /
        (((s + shift * K : ℕ) : ℝ) + 1))) := mul_le_mul_of_nonneg_left hw hC₀
    _ = _ := by ring

private theorem circleAngularJet_abs_le
    {T : MaterialData} {γ : ℝ} {H : CircleModelData} {U : Set X} {f : X → H.Space}
    (hH : IsCircleModel T γ H) (hpos : ∀ m, 0 < T.H (T.sample m))
    (J₀ : SmoothDirections U f) (j m : ℕ) (θ : ℝ)
    (J : SmoothDirections U (fun x => iteratedDeriv j (H.decode (f x) m) θ))
    (k : ℕ) (x : X) (hx : x ∈ U) (v : Fin k → X) :
    |J.D k x v| ≤ (2 * circleSobolevConstant * H.grading (j + 1) (J₀.D k x v)) *
      T.H (T.sample m) ^ γ := by
  let Jang := circleDecodedAngularDirections hH J₀ j m θ
  have heq : J.D k x v = iteratedDeriv j (H.decode (J₀.D k x v) m) θ :=
    (congrArg (fun B : X [×k]→L[ℝ] ℝ => B v) (J.unique Jang k x hx)).trans
      (circleDecodedAngularDirections_jet hH J₀ j m θ k x v)
  calc
    |J.D k x v| = |iteratedDeriv j (H.decode (J₀.D k x v) m) θ| := congrArg abs heq
    _ ≤ _ :=
      ContinuousFlexibility.Statements.circleModel_iteratedDeriv_abs_le hH hpos _ m j θ

/-- A circle family gives scalar angular prefixes on arbitrary state
slots. The base precedes the state prefix, and the coefficient is common
to every order in both finite prefixes, including order zero. -/
theorem N04FixedBaseSmoothFamilyOn.circle_angular_first_prefix
    {T : MaterialData} {γ : ℝ} {H : CircleModelData}
    {p : ℕ → Seminorm ℝ X} {U : Set X} {f : I → X → H.Space}
    (hf : N04FixedBaseSmoothFamilyOn p H.grading U f)
    (hp : Monotone p) (hI : HasInterpolation p)
    (hH : IsCircleModel T γ H) (hpos : ∀ m, 0 < T.H (T.sample m))
    (requestedBase : ℕ) :
    ∃ base : ℕ, requestedBase ≤ base ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ℕ, k ≤ K → ∀ j : ℕ, j ≤ s + 1 → ∀ i m θ,
      ∀ J : SmoothDirections U (fun x => iteratedDeriv j (H.decode (f i x) m) θ),
      ∀ x ∈ U, p base x ≤ 1 → ∀ v : Fin k → X,
      (∀ d, p base (v d) ≤ 1) → ∀ R : ℝ, 1 ≤ R →
      p (base + s + shift * K + 1) x ≤ R →
      (∀ d, p (base + s + shift * K + 1) (v d) ≤ R) →
        |J.D k x v| ≤ C * T.H (T.sample m) ^ γ *
          R ^ (((j - 1 + shift * k : ℕ) : ℝ) /
            (((s + shift * K : ℕ) : ℝ) + 1)) := by
  have hg := gradedFamily_first_prefix hf hp hI requestedBase
  let J₀ := hg.choose
  have hb := hg.choose_spec
  refine ⟨hb.choose, hb.choose_spec.1, fun K => ?_⟩
  have hk := hb.choose_spec.2 K
  refine ⟨hk.choose, fun s => ?_⟩
  have hc := hk.choose_spec s
  let Ce : ℝ := 2 * circleSobolevConstant
  have hCe : 0 ≤ Ce := mul_nonneg (by norm_num) circleSobolevConstant_nonneg
  refine ⟨Ce * hc.choose, mul_nonneg hCe hc.choose_spec.1, ?_⟩
  intro k hk' j hj i m θ J x hx hxlow v hvlow R hR hxhigh hvhigh
  have hgrade := hc.choose_spec.2 k hk' j hj i x hx hxlow v hvlow R hR hxhigh hvhigh
  calc
    |J.D k x v| ≤ (Ce * H.grading (j + 1) ((J₀ i).D k x v)) * T.H (T.sample m) ^ γ :=
      circleAngularJet_abs_le hH hpos (J₀ i) j m θ J k x hx v
    _ ≤ (Ce * (hc.choose * R ^ (((j - 1 + hk.choose * k : ℕ) : ℝ) /
        (((s + hk.choose * K : ℕ) : ℝ) + 1)))) * T.H (T.sample m) ^ γ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgrade hCe)
        (Real.rpow_nonneg (hpos m).le _)
    _ = _ := by ring

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04FixedBaseSmoothFamilyOn.circle_angular_first_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04FixedBaseSmoothFamilyOn.circle_angular_first_prefix
