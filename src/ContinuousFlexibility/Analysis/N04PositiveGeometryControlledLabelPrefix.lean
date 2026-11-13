import ContinuousFlexibility.Analysis.N04RealizationFixedBasePrefix
import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization

/-!
# Abstract fixed-base label prefixes

The numerical normalization for the two actual root labels is carried
out on an abstract parameter space. This keeps the physical state
implementation out of finite-prefix selection and scalar arithmetic.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- A displacement prefix at a fixed low order, with a fixed intrinsic
angular reserve and the actual parameter arity in the exponent. -/
def N04LabelDefectPrefix (p : ℕ → Seminorm ℝ E) (U : Set E)
    (F : ℕ → Bool → ℕ → ℝ → E → ℝ) (H : ℕ → ℝ) (base reserve : ℕ) : Prop :=
  ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
    ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ k : ℕ, k ≤ K → ∀ u : ℕ, u ≤ s → ∀ b : ℕ, b ≤ u + reserve →
      ∀ side : Bool, ∀ m : ℕ, ∀ θ : ℝ, ∀ J : SmoothDirections U (F b side m θ),
      ∀ x ∈ U, p low x ≤ 1 → ∀ v : Fin k → E,
      (∀ j, p low (v j) ≤ 1) → ∀ R : ℝ, 1 ≤ R →
      p (low + s + shift * K + 1) x ≤ R →
      (∀ j, p (low + s + shift * K + 1) (v j) ≤ R) →
      |J.D k x v| ≤ A * H m *
        R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1))

/-- The corresponding literal slope prefix retains its reference value
at parameter order zero. -/
def N04LabelSlopePrefix (p : ℕ → Seminorm ℝ E) (U : Set E)
    (G : ℕ → Bool → ℕ → ℝ → E → ℝ) (H : ℕ → ℝ) (base reserve : ℕ) : Prop :=
  ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
    ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ k : ℕ, k ≤ K → ∀ d : ℕ, d ≤ reserve → ∀ u : ℕ, u ≤ s →
      ∀ side : Bool, ∀ m : ℕ, ∀ θ : ℝ, ∀ J : SmoothDirections U (G (u + d) side m θ),
      ∀ x ∈ U, p low x ≤ 1 → ∀ v : Fin k → E,
      (∀ j, p low (v j) ≤ 1) → ∀ R : ℝ, 1 ≤ R →
      p (low + s + shift * K + 1) x ≤ R →
      (∀ j, p (low + s + shift * K + 1) (v j) ≤ R) →
      |J.D k x v| ≤ A * parameterHeightWeight (H m) k *
        R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1))

theorem n04PositiveGeometry_labelDefect_prefix_of_oneHigh
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hI : HasInterpolation p)
    (U : Set E) (F : ℕ → Bool → ℕ → ℝ → E → ℝ) (H : ℕ → ℝ)
    (hH : ∀ m, 0 ≤ H m) (base reserve : ℕ)
    (hraw : ∃ B : ℕ, ∀ n : ℕ, ∃ ell : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, ∃ A : ℝ, 0 ≤ A ∧
        ∀ b : ℕ, b ≤ s → ∀ side : Bool, ∀ m : ℕ, ∀ θ : ℝ,
        ∀ J : SmoothDirections U (F b side m θ),
        ∀ x ∈ U, p B x ≤ R → ∀ v : Fin n → E,
        |J.D n x v| ≤ A * H m * tameJetSize p n s ell B x v) :
    N04LabelDefectPrefix p U F H base reserve := by
  classical
  refine hraw.elim ?_
  intro B hB
  choose ell hell using hB
  let L : ℕ → ℕ := fun k => reserve + ell k
  refine (n04Realization_fixedBase_prefix_power p hp hI (max base B) L).elim ?_
  intro low hlowData
  have hlow := hlowData.1
  have hprefix := hlowData.2
  have hbase : base ≤ low := (le_max_left _ _).trans hlow
  have hBlow : B ≤ low := (le_max_right _ _).trans hlow
  refine ⟨low, hbase, fun K => ?_⟩
  refine (hprefix K).elim ?_
  intro shift hshift
  refine ⟨shift, fun s => ?_⟩
  refine (hshift s).elim ?_
  intro A₀ hA₀Data
  have hA₀ := hA₀Data.1
  have hinterp := hA₀Data.2
  let I : Type := Fin (K + 1) × Fin (s + 1)
  choose c hc hcb using fun i : I => hell i.1.val 1 zero_le_one (i.2.val + reserve)
  let C₀ : ℝ := 1 + ∑ i : I, c i
  have hC₀ : 1 ≤ C₀ := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun i _ => hc i))
  have hcC (i : I) : c i ≤ C₀ :=
    (Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨C₀ * A₀, one_le_mul_of_one_le_of_one_le hC₀ hA₀, ?_⟩
  intro k hk u hu b hb side m θ J x hx hxlow v hvlow R hR hxR hvR
  let i : I := (⟨k, Nat.lt_succ_of_le hk⟩, ⟨u, Nat.lt_succ_of_le hu⟩)
  have hxB : p B x ≤ 1 := (hp hBlow x).trans hxlow
  have hbnd := hcb i b hb side m θ J x hx hxB v
  change |J.D k x v| ≤ c i * H m *
    oneHighVariationWeight p B (u + reserve + ell k) x v at hbnd
  have hweight : oneHighVariationWeight p B (u + reserve + ell k) x v ≤
      oneHighVariationWeight p low (u + L k) x v :=
    oneHighVariationWeight_mono hp hBlow (by dsimp only [L]; omega) x v
  have hpower := hinterp k hk u hu x hxlow v hvlow R hR hxR hvR
  calc
    _ ≤ (c i * H m) * oneHighVariationWeight p low (u + L k) x v := hbnd.trans
      (mul_le_mul_of_nonneg_left hweight (mul_nonneg (hc i) (hH m)))
    _ ≤ (c i * H m) *
        (A₀ * R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hpower (mul_nonneg (hc i) (hH m))
    _ ≤ (C₀ * H m) *
        (A₀ * R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hcC i) (hH m))
        (mul_nonneg (zero_le_one.trans hA₀) (Real.rpow_nonneg (zero_le_one.trans hR) _))
    _ = _ := by ac_rfl

theorem n04PositiveGeometry_labelSlope_prefix_of_defect
    (p : ℕ → Seminorm ℝ E) (U : Set E)
    (F G : ℕ → Bool → ℕ → ℝ → E → ℝ) (H : ℕ → ℝ)
    (hH : ∀ m, 0 ≤ H m) (base reserve : ℕ) {RH : ℝ} (hRH : 0 < RH)
    (hHbound : ∀ m, H m ≤ RH)
    (JD : ∀ side m b θ, SmoothDirections U (F b side m θ))
    (hvalue : ∀ side m b θ x, x ∈ U →
      G b side m θ x = F (b + 1) side m θ x + if b = 0 then 1 else 0)
    (hprefix : N04LabelDefectPrefix p U F H base (reserve + 1)) :
    N04LabelSlopePrefix p U G H base reserve := by
  refine hprefix.elim ?_
  intro low hlowData
  have hlow := hlowData.1
  have hlowPrefix := hlowData.2
  refine ⟨low, hlow, fun K => ?_⟩
  refine (hlowPrefix K).elim ?_
  intro shift hshift
  refine ⟨shift, fun s => ?_⟩
  refine (hshift s).elim ?_
  intro A hAData
  have hA := hAData.1
  have hbound := hAData.2
  let C₁ : ℝ := A * (RH + 1) + 1
  have hC₁ : 1 ≤ C₁ := le_add_of_nonneg_left
    (mul_nonneg (zero_le_one.trans hA) (by positivity))
  have hAC₁ : A ≤ C₁ := by dsimp only [C₁]; nlinarith only [hA, hRH]
  have hAHC₁ : A * RH + 1 ≤ C₁ := by dsimp only [C₁]; nlinarith only [hA]
  refine ⟨C₁, hC₁, ?_⟩
  intro k hk d hd u hu side m θ J x hx hxlow v hvlow R hR hxR hvR
  let JF := JD side m (u + d + 1) θ
  have hb := hbound k hk u hu (u + d + 1) (by omega)
    side m θ JF x hx hxlow v hvlow R hR hxR hvR
  let P : ℝ := R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1))
  have hP : 0 ≤ P := Real.rpow_nonneg (zero_le_one.trans hR) _
  have hPone : 1 ≤ P := Real.one_le_rpow hR (div_nonneg (Nat.cast_nonneg _) (by positivity))
  by_cases hkzero : k = 0
  · subst k
    have heq : J.D 0 x v = JF.D 0 x v + (if u + d = 0 then 1 else 0) :=
      (smoothDirections_D_zero_apply J hx v).trans
        ((hvalue side m (u + d) θ x hx).trans
          (congrArg (fun t : ℝ => t + (if u + d = 0 then 1 else 0))
            (smoothDirections_D_zero_apply JF hx v).symm))
    have hconstant : |(if u + d = 0 then (1 : ℝ) else 0)| ≤ 1 := by
      split_ifs <;> norm_num
    have hfinal : |J.D 0 x v| ≤ C₁ * P := calc
      _ ≤ |JF.D 0 x v| + |(if u + d = 0 then (1 : ℝ) else 0)| :=
        (congrArg abs heq).trans_le (abs_add_le _ _)
      _ ≤ A * H m * P + 1 := add_le_add hb hconstant
      _ ≤ A * RH * P + P := add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hHbound m) (zero_le_one.trans hA)) hP) hPone
      _ = (A * RH + 1) * P := by rw [add_mul, one_mul]
      _ ≤ C₁ * P := mul_le_mul_of_nonneg_right hAHC₁ hP
    simpa only [parameterHeightWeight, ite_true, mul_one] using hfinal
  · let JF' := JF.congrOn (fun y hy => (eq_sub_iff_add_eq).mpr
      (hvalue side m (u + d) θ y hy).symm)
    have hjet : J.D k x v = JF.D k x v :=
      (smoothDirections_D_sub_constant J JF' (Nat.pos_of_ne_zero hkzero) hx v).symm
    have hfinal : |J.D k x v| ≤ C₁ * H m * P :=
      ((congrArg abs hjet).trans_le hb).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAC₁ (hH m)) hP)
    simpa only [parameterHeightWeight, if_neg hkzero] using hfinal

end ContinuousFlexibility.Analysis
