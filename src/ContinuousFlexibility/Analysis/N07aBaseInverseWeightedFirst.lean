import ContinuousFlexibility.Analysis.N07aAngularWeightedSolution
import ContinuousFlexibility.Analysis.N07aAngularMaterialLowering
import ContinuousFlexibility.Analysis.N07aAngularGraph
import ContinuousFlexibility.Analysis.N07aReferenceFiniteJets

/-!
# The two terminal normal orders of the same Banach solution

The fixed real material loss of N05 is paid by its natural ceiling once.
All lower material and angular realizations retain the exact same forget
map. The first radial class remains the original weak derivative.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {b : ℕ} {B : CanonicalDomainData S K V b} {P : RelativeInverseData S K V b B}

local instance n07aWeightedFirstLevelGroup (t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level (3 / 4 : ℝ) t s) := Submodule.normedAddCommGroup _

local instance n07aWeightedFirstLevelSpace (t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level (3 / 4 : ℝ) t s) := Submodule.normedSpace _

theorem n07aBaseInverse_weighted_firstPair
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h05 : N05Properties D T S C K V b B) :
    ∃ k : ℕ, ∀ c s : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ (z : AnnularState S × ℝ) (F₀ : V.level (3 / 4 : ℝ) 0 b)
        (Q : V.level (3 / 4 : ℝ) ((c + k : ℕ) : ℝ) (s + 1)),
        V.forget (3 / 4 : ℝ) ((c + k : ℕ) : ℝ) (s + 1) Q =
          V.forget (3 / 4 : ℝ) 0 b (P.inverse z F₀) →
        ∃ W Wr : V.level (3 / 4 : ℝ) (c : ℝ) s,
          V.forget (3 / 4 : ℝ) (c : ℝ) s W =
            (fun m => (n07aBaseInverse B P z F₀).val.1.1 m) ∧
          (∀ m, N07aWeakCanonicalMixedDerivative S K m
            ((n07aBaseInverse B P z F₀).val.1.1 m)
            (V.forget (3 / 4 : ℝ) (c : ℝ) s Wr m) 1 0) ∧
          ‖W‖ + ‖Wr‖ + canonicalUnknownScalars S K (n07aBaseInverse B P z F₀).val.1 ≤
            A * ‖Q‖ := by
  let k : ℕ := ⌈B.lossMaterial⌉₊
  have hk : B.lossMaterial ≤ (k : ℝ) := Nat.le_ceil _
  refine ⟨k, fun c s => ?_⟩
  let t : ℝ := (c + k : ℕ)
  have hct : (c : ℝ) ≤ t - B.lossMaterial := by
    dsimp only [t]
    push_cast
    linarith only [hk]
  let zeroData := n07aAngularBaseSolution_weighted (P := P) h05 t (s + 1)
  let A₀ : ℝ := zeroData.choose
  have hA₀ : 0 < A₀ := zeroData.choose_spec.1
  have hzero := zeroData.choose_spec.2
  let firstData := n07aAngularBaseSolution_firstNormal_weighted (P := P) h05 t s
  let A₁ : ℝ := firstData.choose
  have hA₁ : 0 < A₁ := firstData.choose_spec.1
  have hfirst := firstData.choose_spec.2
  refine ⟨A₀ + A₁, add_pos hA₀ hA₁, fun z F₀ Q hQ => ?_⟩
  let zeroPair := hzero z F₀ Q hQ
  let W₀ : V.level (3 / 4 : ℝ) (t - B.lossMaterial) (s + 1) := zeroPair.choose
  have hW₀ := zeroPair.choose_spec.1
  have hW₀bound := zeroPair.choose_spec.2
  let firstPair := hfirst z F₀ Q hQ
  let Wr₀ : V.level (3 / 4 : ℝ) (t - B.lossMaterial) s := firstPair.choose
  have hWr₀ := firstPair.choose_spec.1
  have hWr₀bound := firstPair.choose_spec.2
  let Wlow := n07aAngularMaterialLower hD hT h05.2.1 hct W₀
  let W := n07aAngularLevelTruncate h05.2.1 (3 / 4 : ℝ) (c : ℝ) (Nat.le_succ s) Wlow
  let Wr := n07aAngularMaterialLower hD hT h05.2.1 hct Wr₀
  have hWforget : V.forget (3 / 4 : ℝ) (c : ℝ) s W =
      V.forget (3 / 4 : ℝ) (t - B.lossMaterial) (s + 1) W₀ :=
    (n07aAngularLevelTruncate_forget h05.2.1 (3 / 4 : ℝ) (c : ℝ)
      (Nat.le_succ s) Wlow).trans (n07aAngularMaterialLower_forget hD hT h05.2.1 hct W₀)
  have hWrforget : V.forget (3 / 4 : ℝ) (c : ℝ) s Wr =
      V.forget (3 / 4 : ℝ) (t - B.lossMaterial) s Wr₀ :=
    n07aAngularMaterialLower_forget hD hT h05.2.1 hct Wr₀
  refine ⟨W, Wr, hWforget.trans hW₀, ?_, ?_⟩
  · intro m φ hφ
    rw [hWrforget]
    simpa only [Nat.add_zero, pow_one, neg_one_mul] using hWr₀ m φ hφ
  · have hWnorm : ‖W‖ ≤ ‖W₀‖ :=
      (n07aAngularLevelTruncate_norm_le h05.2.1 (3 / 4 : ℝ) (c : ℝ)
        (Nat.le_succ s) Wlow).trans (n07aAngularMaterialLower_norm_le hD hT h05.2.1 hct W₀)
    have hWrnorm : ‖Wr‖ ≤ ‖Wr₀‖ :=
      n07aAngularMaterialLower_norm_le hD hT h05.2.1 hct Wr₀
    nlinarith only [hWnorm, hWrnorm, hW₀bound, hWr₀bound]

end ContinuousFlexibility.Analysis
