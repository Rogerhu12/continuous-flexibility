import ContinuousFlexibility.Analysis.N01RootFieldLocalization
import ContinuousFlexibility.Analysis.RootControlledFlow

/-!
# A genuinely controlled root flow from the actual N01 coefficients

All low orders and losses are chosen before the root. The fixed radial
localization provides globally smooth periodic fields and preserves all
ordinary jets on the region used by the flow. The n=1 actual field bound
on one additional common low-seminorm ball chooses an angular control
collar before the state. Actual Picard existence and the proved flow-jet
theorem then produce a solution and its fixed-loss estimates.

The geometric input remains the actual common strip and an actual cell
containing its physical image. Numerical constants may depend on that
root; no component-uniform material-envelope conclusion is asserted here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n01_exists_controlled_root_flow
    (hFlow : N04FlowJetsTarget)
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ low outLoss : ℕ, ∀ r σ : ℝ, ∀ g : ℝ → ℝ, ∀ R : ℝ,
      (σ = 1 ∨ σ = -1) → ∀ hR : 0 < R, ContDiff ℝ ∞ g →
      Ioo ((r - R) - R) ((r + R) + R) ⊆ Ioo D.a D.b →
      ∀ m : ℕ, Ioo (r - R) (r + R) ⊆ D.cells m →
      (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
          (stateHeight D S C z) r σ R) →
      ∀ Λ : ℝ, 0 < Λ →
      ∃ δ : ℝ, ∃ B : ℕ → ℝ,
        0 < δ ∧ δ ≤ R / 4 ∧ δ ≤ 1 ∧ (∀ n, 0 < B n) ∧
        ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
        N04FlowAngularControl
          (rootRescaledField (localizedRootDrift D S C r σ hR z)
            (localizedRootSpeed D S C g r σ hR z) δ) Λ ∧
        ∃ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
          N04FlowEquations
            (rootRescaledField (localizedRootDrift D S C r σ hR z)
              (localizedRootSpeed D S C g r σ hR z) δ) Θ ∧
          N04FlowJetBounds (pairGrading (stateGrading S) realGrading)
            outLoss B (z - (C.referenceState, 0)) 1 Λ Θ := by
  let p := pairGrading (stateGrading S) realGrading
  have hp : Monotone p :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI : HasInterpolation p :=
    coordinate_hasInterpolation_pair (stateGrading_monotone S)
      (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  obtain ⟨lowF, lossF, hfield⟩ := n01_rootCharacteristicField_fixed_loss_bound hS hT hN
  obtain ⟨lowFlow, outLoss, hflow⟩ := exists_rootRescaledFlow_fixed_loss hFlow hp hI lossF
  let low := max lowF (max (1 + lossF) lowFlow)
  refine ⟨low, outLoss, ?_⟩
  intro r σ g R hσ hR hg hphysical m hcell hstrip Λ hΛ
  obtain ⟨A₀, hA₀, hraw⟩ := hfield r σ g R hσ hR hg hphysical m hcell hstrip
  let A : ℕ → ℝ := fun n => 1 + A₀ n
  have hA (n : ℕ) : 1 ≤ A n := by dsimp only [A]; linarith [hA₀ n]
  obtain ⟨B, hB, hflowBound⟩ := hflow A hA Λ hΛ.le
  let V : Set (AnnularState S × ℝ) :=
    {z | z ∈ stateNeighborhood S C base ε ∧ stateSector S z.1 ∧
      p low (z - (C.referenceState, 0)) ≤ 1}
  let d := localizedRootDrift D S C r σ hR
  let c := localizedRootSpeed D S C g r σ hR
  have hregular (z : AnnularState S × ℝ) (hz : z ∈ V) :
      ContDiff ℝ ∞ (d z) ∧ ContDiff ℝ ∞ (c z) :=
    contDiff_localizedRootFields_of_n01 hS hT hN hg hR (hstrip z hz.1 hz.2.1)
  have hfieldLow (z : AnnularState S × ℝ) (hz : z ∈ V) :
      p lowF (z - (C.referenceState, 0)) ≤ 1 :=
    (hp (Nat.le_max_left lowF _) _).trans hz.2.2
  have hfirstLow (z : AnnularState S × ℝ) (hz : z ∈ V) :
      p (1 + lossF) (z - (C.referenceState, 0)) ≤ 1 :=
    (hp ((Nat.le_max_left (1 + lossF) lowFlow).trans (Nat.le_max_right lowF _)) _).trans hz.2.2
  have hlocalized (z : AnnularState S × ℝ) (hz : z ∈ V) (n : ℕ)
      (t : ℝ) (ht : |t| ≤ R / 4) (θ : ℝ) :
      ‖iteratedFDeriv ℝ n (d z) (t, θ)‖ + ‖iteratedFDeriv ℝ n (c z) (t, θ)‖ ≤
        A₀ n * (1 + p (n + lossF) (z - (C.referenceState, 0))) := by
    have he := iteratedFDeriv_localizedRootFields_eq D S C g r σ hR z n (q := (t, θ)) ht
    change ‖iteratedFDeriv ℝ n (localizedRootDrift D S C r σ hR z) (t, θ)‖ +
      ‖iteratedFDeriv ℝ n (localizedRootSpeed D S C g r σ hR z) (t, θ)‖ ≤ _
    rw [he.1, he.2]
    apply hraw z hz.1 hz.2.1 (hfieldLow z hz) n (t, θ)
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith [(abs_le.mp ht).1, (abs_le.mp ht).2]
  let M : ℝ := 2 * A₀ 1
  have hM : 0 ≤ M := mul_nonneg (by norm_num) (hA₀ 1).le
  have hfirst (z : AnnularState S × ℝ) (hz : z ∈ V)
      (t : ℝ) (ht : |t| ≤ R / 4) (θ : ℝ) :
      |deriv (fun η => d z (t, η)) θ| ≤ M ∧
        |deriv (fun η => c z (t, η)) θ| ≤ M := by
    have hcap : A₀ 1 * (1 + p (1 + lossF) (z - (C.referenceState, 0))) ≤ M := by
      have hh := mul_le_mul_of_nonneg_left
        (show 1 + p (1 + lossF) (z - (C.referenceState, 0)) ≤ 2 by linarith [hfirstLow z hz])
        (hA₀ 1).le
      simpa only [M, mul_comm] using hh
    have hsum := (hlocalized z hz 1 t ht θ).trans hcap
    exact ⟨(abs_deriv_angular_le_first_frechet (hregular z hz).1 t θ).trans
      ((le_add_of_nonneg_right (norm_nonneg _)).trans hsum),
      (abs_deriv_angular_le_first_frechet (hregular z hz).2 t θ).trans
      ((le_add_of_nonneg_left (norm_nonneg _)).trans hsum)⟩
  obtain ⟨δ, hδ, hδR, hδone, hcontrol⟩ := exists_rootRescaledField_angularControl
    (U := V) d c (div_pos hR (by norm_num)) hM hΛ
    (fun z hz => (hregular z hz).1) (fun z hz => (hregular z hz).2)
    (fun z hz t ht θ => (hfirst z hz t ht θ).1)
    (fun z hz t ht θ => (hfirst z hz t ht θ).2)
  refine ⟨δ, B, hδ, hδR, hδone, hB, ?_⟩
  intro z hz hsector hlow
  have hzV : z ∈ V := ⟨hz, hsector, hlow⟩
  refine ⟨hcontrol z hzV, ?_⟩
  have hlowFlow : p lowFlow (z - (C.referenceState, 0)) ≤ 1 :=
    (hp ((Nat.le_max_right (1 + lossF) lowFlow).trans (Nat.le_max_right lowF _)) _).trans hlow
  have hcoef (n : ℕ) (t : ℝ) (ht : |t| ≤ δ) (θ : ℝ) :
      ‖iteratedFDeriv ℝ n (d z) (t, θ)‖ ≤
          A n * (1 : ℝ) ^ (A n) * (1 + p (n + lossF) (z - (C.referenceState, 0))) ∧
        ‖iteratedFDeriv ℝ n (c z) (t, θ)‖ ≤
          A n * (1 : ℝ) ^ (A n) * (1 + p (n + lossF) (z - (C.referenceState, 0))) := by
    have hpack : A₀ n * (1 + p (n + lossF) (z - (C.referenceState, 0))) ≤
        A n * (1 + p (n + lossF) (z - (C.referenceState, 0))) :=
      mul_le_mul_of_nonneg_right (by dsimp only [A]; linarith)
        (add_nonneg zero_le_one (apply_nonneg _ _))
    have hsum := (hlocalized z hzV n t (ht.trans hδR) θ).trans hpack
    simpa only [Real.one_rpow, mul_one] using
      And.intro ((le_add_of_nonneg_right (norm_nonneg _)).trans hsum)
        ((le_add_of_nonneg_left (norm_nonneg _)).trans hsum)
  have hperiod := periodic_localizedRootFields hS C g r σ hR z
  exact hflowBound (z - (C.referenceState, 0)) hlowFlow 1 le_rfl δ hδ.le hδone
    (d z) (c z) (hregular z hzV).1 (hregular z hzV).2 hperiod.1 hperiod.2
    (fun n t ht θ => (hcoef n t ht θ).1) (fun n t ht θ => (hcoef n t ht θ).2)
    (hcontrol z hzV)

end ContinuousFlexibility.Analysis
