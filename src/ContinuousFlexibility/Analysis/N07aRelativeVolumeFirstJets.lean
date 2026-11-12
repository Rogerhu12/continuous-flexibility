import ContinuousFlexibility.Analysis.N07aBaseInverseWeightedFirst
import ContinuousFlexibility.Analysis.N07aVolumeJetBounds
import ContinuousFlexibility.Analysis.N07aSampleLinearJets
import ContinuousFlexibility.Analysis.N07aParameterGrading

/-!
# The actual first-normal jet estimates from the lifted relative inverse

Only the reference inverse's fixed material loss and one angular order
are added. The weak derivatives all belong to the same Banach unknown.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {F : Type*} [AddCommGroup F] [Module ℝ F]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {b : ℕ} {B : CanonicalDomainData S K V b} {P : RelativeInverseData S K V b B}

local instance n07aRelativeFirstLevelGroup (t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level (3 / 4 : ℝ) t s) := Submodule.normedAddCommGroup _

local instance n07aRelativeFirstLevelSpace (t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level (3 / 4 : ℝ) t s) := Submodule.normedSpace _

theorem n07a_relativeVolume_firstJets
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h05 : N05Properties D T S C K V b B)
    (q : ℕ → Seminorm ℝ F) (hq : Monotone q)
    (U : Set (CanonicalGeometry.Parameter S)) (low d : ℕ)
    (F₀ : CanonicalGeometry.Parameter S → F → V.level (3 / 4 : ℝ) 0 b)
    (hlift : ∀ t s : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ z ∈ U, ∀ v,
      ∃ Q : V.level (3 / 4 : ℝ) (t : ℝ) (b + s),
        V.forget (3 / 4 : ℝ) (t : ℝ) (b + s) Q =
          V.forget (3 / 4 : ℝ) 0 b (P.inverse (liftSectorParameter S C z) (F₀ z v)) ∧
        ‖Q‖ ≤ A * (q (t + s + d) v +
          (1 + CanonicalGeometry.parameterGrading S (t + s + d) z) * q low v)) :
    ∃ d' : ℕ, ∀ a : ℕ, a ≤ 1 → ∀ n c : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ z ∈ U, ∀ v m, ∃ J : CanonicalL2 S K m,
        N07aWeakCanonicalMixedDerivative S K m
          ((n07aBaseInverse B P (liftSectorParameter S C z) (F₀ z v)).val.1.1 m) J a n ∧
        ‖J‖ ≤ A *
          (T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) * (T.M (T.sample (K.cell m)) ^ c)⁻¹) *
          (q (c + (a + n) + d') v +
            (1 + CanonicalGeometry.parameterGrading S (c + (a + n) + d') z) * q low v) := by
  let firstData := n07aBaseInverse_weighted_firstPair (P := P) hD hT h05
  let k : ℕ := firstData.choose
  have hfirst := firstData.choose_spec
  let d' := k + d + 1
  refine ⟨d', fun a ha n c => ?_⟩
  let pairData := hfirst c (b + n)
  let A₀ : ℝ := pairData.choose
  have hA₀ : 0 < A₀ := pairData.choose_spec.1
  have hpair := pairData.choose_spec.2
  let liftData := hlift (c + k) (n + 1)
  let A₁ : ℝ := liftData.choose
  have hA₁ : 0 < A₁ := liftData.choose_spec.1
  have hQ := liftData.choose_spec.2
  refine ⟨A₀ * A₁, mul_pos hA₀ hA₁, fun z hz v m => ?_⟩
  let QAt : ℕ → Prop := fun order =>
    ∃ Q' : V.level (3 / 4 : ℝ) ((c + k : ℕ) : ℝ) order,
      V.forget (3 / 4 : ℝ) ((c + k : ℕ) : ℝ) order Q' =
        V.forget (3 / 4 : ℝ) 0 b (P.inverse (liftSectorParameter S C z) (F₀ z v)) ∧
      ‖Q'‖ ≤ A₁ * (q ((c + k) + (n + 1) + d) v +
        (1 + CanonicalGeometry.parameterGrading S ((c + k) + (n + 1) + d) z) * q low v)
  have hQAt : QAt (b + (n + 1)) := hQ z hz v
  have hQ' : QAt ((b + n) + 1) :=
    Eq.mp (congrArg QAt (Nat.add_assoc b n 1).symm) hQAt
  let Q' : V.level (3 / 4 : ℝ) ((c + k : ℕ) : ℝ) ((b + n) + 1) := hQ'.choose
  have hQsame' := hQ'.choose_spec.1
  have hQbound' := hQ'.choose_spec.2
  let firstPair := hpair (liftSectorParameter S C z) (F₀ z v) Q' hQsame'
  let W : V.level (3 / 4 : ℝ) (c : ℝ) (b + n) := firstPair.choose
  let Wr : V.level (3 / 4 : ℝ) (c : ℝ) (b + n) := firstPair.choose_spec.choose
  have hW := firstPair.choose_spec.choose_spec.1
  have hWr := firstPair.choose_spec.choose_spec.2.1
  have hWbound := firstPair.choose_spec.choose_spec.2.2
  have hsc : 0 ≤ canonicalUnknownScalars S K
      (n07aBaseInverse B P (liftSectorParameter S C z) (F₀ z v)).val.1 := by
    unfold canonicalUnknownScalars
    positivity
  have hWn : ‖W‖ ≤ A₀ * ‖Q'‖ := by linarith only [hWbound, norm_nonneg Wr, hsc]
  have hWrn : ‖Wr‖ ≤ A₀ * ‖Q'‖ := by linarith only [hWbound, norm_nonneg W, hsc]
  let j : Fin ((b + n) + 1) := ⟨n, by omega⟩
  have hj0 := n07aVolumeAngularJet_weak h05.2.1 W m j
  rw [hW] at hj0
  have hj1 := (hWr m).comp (n07aVolumeAngularJet_weak h05.2.1 Wr m j)
  have hnorm (Z : V.level (3 / 4 : ℝ) (c : ℝ) (b + n)) (hZ : ‖Z‖ ≤ A₀ * ‖Q'‖) :
      ‖n07aVolumeAngularJet (T := T) Z m j‖ ≤ (A₀ * A₁) *
        (T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) * (T.M (T.sample (K.cell m)) ^ c)⁻¹) *
        (q (c + (a + n) + d') v +
          (1 + CanonicalGeometry.parameterGrading S (c + (a + n) + d') z) * q low v) := by
    let w := T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
      (T.M (T.sample (K.cell m)) ^ c)⁻¹
    have hsample := hT.2.1 _
      (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))
    have hw : 0 ≤ w := mul_nonneg (Real.rpow_nonneg hsample.2.1.le _)
      (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hsample.2.2.2) _))
    have horder : (c + k) + (n + 1) + d ≤ c + (a + n) + d' := by
      dsimp only [d']
      omega
    have hfactor :
        q ((c + k) + (n + 1) + d) v +
            (1 + CanonicalGeometry.parameterGrading S ((c + k) + (n + 1) + d) z) * q low v ≤
          q (c + (a + n) + d') v +
            (1 + CanonicalGeometry.parameterGrading S (c + (a + n) + d') z) * q low v :=
      add_le_add (hq horder v)
      (mul_le_mul_of_nonneg_right
        (add_le_add (le_refl (1 : ℝ)) (n07aParameterGrading_monotone S horder z))
        (apply_nonneg (q low) v))
    have hbound := hZ.trans (mul_le_mul_of_nonneg_left
      (hQbound'.trans (mul_le_mul_of_nonneg_left hfactor hA₁.le)) hA₀.le)
    exact ((n07aVolumeAngularJet_nat_norm_le hD hT Z m j).trans
      (mul_le_mul_of_nonneg_left hbound hw)).trans_eq (by ring)
  cases a with
  | zero => exact ⟨_, hj0, hnorm W hWn⟩
  | succ a =>
    have ha0 : a = 0 := by omega
    subst a
    exact ⟨_, by simpa only [Nat.add_zero, Nat.zero_add] using hj1, hnorm Wr hWrn⟩

end ContinuousFlexibility.Analysis
