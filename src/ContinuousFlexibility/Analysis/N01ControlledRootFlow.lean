import ContinuousFlexibility.Analysis.N01RootFieldLocalization
import ContinuousFlexibility.Analysis.RootControlledFlow

/-!
# A genuinely controlled root flow from the actual N01 coefficients

All low orders and losses precede the root. The numerical argument uses
an abstract state grading; the concrete adapter supplies the genuinely
localized coefficient fields and their actual ordinary jets. A collar
chosen before the state bounds the angular Gronwall exponent, and the
independent flow theorem supplies the actual solution and all its jets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def RootControlledFlowAtState
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (loss : ℕ) (B : ℕ → ℝ)
    (x : E) (δ Λ : ℝ) (d c : PolarPoint → ℝ) : Prop :=
  N04FlowAngularControl (rootRescaledField d c δ) Λ ∧
    ∃ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      N04FlowEquations (rootRescaledField d c δ) Θ ∧
      N04FlowJetBounds p loss B x 1 Λ Θ

/-- Select the common low order before the family and its collar. The
arithmetic never unfolds a concrete projective state space. -/
private theorem exists_controlledRootFlow_of_frechet_family
    (hFlow : N04FlowJetsTarget)
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ low outLoss : ℕ, ∀ A₀ : ℕ → ℝ, (∀ n, 0 < A₀ n) →
      ∀ Λ : ℝ, 0 < Λ → ∀ ρ : ℝ, 0 < ρ →
      ∀ (ι : Type) (V : Set ι) (w : ι → E) (d c : ι → PolarPoint → ℝ),
      (∀ i ∈ V, ContDiff ℝ ∞ (d i) ∧ ContDiff ℝ ∞ (c i)) →
      (∀ i ∈ V,
        (∀ r, Function.Periodic (fun θ => d i (r, θ)) Real.pi) ∧
        (∀ r, Function.Periodic (fun θ => c i (r, θ)) Real.pi)) →
      (∀ i ∈ V, p low (w i) ≤ 1) →
      (∀ i ∈ V, ∀ n : ℕ, ∀ r : ℝ, |r| ≤ ρ → ∀ θ : ℝ,
        ‖iteratedFDeriv ℝ n (d i) (r, θ)‖ + ‖iteratedFDeriv ℝ n (c i) (r, θ)‖ ≤
          A₀ n * (1 + p (n + inputLoss) (w i))) →
      ∃ δ : ℝ, ∃ B : ℕ → ℝ, 0 < δ ∧ δ ≤ ρ ∧ δ ≤ 1 ∧
        (∀ n, 0 < B n) ∧
        ∀ i ∈ V, RootControlledFlowAtState p outLoss B (w i) δ Λ (d i) (c i) := by
  obtain ⟨lowFlow, outLoss, hflow⟩ := exists_rootRescaledFlow_fixed_loss hFlow hp hI inputLoss
  refine ⟨max (1 + inputLoss) lowFlow, outLoss, ?_⟩
  intro A₀ hA₀ Λ hΛ ρ hρ ι V w d c hregular hperiod hlow hraw
  let A : ℕ → ℝ := fun n => 1 + A₀ n
  have hA (n : ℕ) : 1 ≤ A n := by dsimp only [A]; linarith [hA₀ n]
  obtain ⟨B, hB, hflowBound⟩ := hflow A hA Λ hΛ.le
  have hfirstLow (i : ι) (hi : i ∈ V) : p (1 + inputLoss) (w i) ≤ 1 :=
    (hp (Nat.le_max_left (1 + inputLoss) lowFlow) _).trans (hlow i hi)
  let M : ℝ := 2 * A₀ 1
  have hM : 0 ≤ M := mul_nonneg (by norm_num) (hA₀ 1).le
  have hfirst (i : ι) (hi : i ∈ V) (r : ℝ) (hr : |r| ≤ ρ) (θ : ℝ) :
      |deriv (fun η => d i (r, η)) θ| ≤ M ∧
        |deriv (fun η => c i (r, η)) θ| ≤ M := by
    have hcap : A₀ 1 * (1 + p (1 + inputLoss) (w i)) ≤ M := by
      have hh := mul_le_mul_of_nonneg_left
        (show 1 + p (1 + inputLoss) (w i) ≤ 2 by linarith [hfirstLow i hi])
        (hA₀ 1).le
      simpa only [M, mul_comm] using hh
    have hsum := (hraw i hi 1 r hr θ).trans hcap
    exact ⟨(abs_deriv_angular_le_first_frechet (hregular i hi).1 r θ).trans
      ((le_add_of_nonneg_right (norm_nonneg _)).trans hsum),
      (abs_deriv_angular_le_first_frechet (hregular i hi).2 r θ).trans
      ((le_add_of_nonneg_left (norm_nonneg _)).trans hsum)⟩
  obtain ⟨δ, hδ, hδρ, hδone, hcontrol⟩ := exists_rootRescaledField_angularControl
    (U := V) d c hρ hM hΛ
    (fun i hi => (hregular i hi).1) (fun i hi => (hregular i hi).2)
    (fun i hi r hr θ => (hfirst i hi r hr θ).1)
    (fun i hi r hr θ => (hfirst i hi r hr θ).2)
  refine ⟨δ, B, hδ, hδρ, hδone, hB, ?_⟩
  intro i hi
  refine ⟨hcontrol i hi, ?_⟩
  have hlowFlow : p lowFlow (w i) ≤ 1 :=
    (hp (Nat.le_max_right (1 + inputLoss) lowFlow) _).trans (hlow i hi)
  have hcoef (n : ℕ) (r : ℝ) (hr : |r| ≤ δ) (θ : ℝ) :
      ‖iteratedFDeriv ℝ n (d i) (r, θ)‖ ≤
          A n * (1 : ℝ) ^ (A n) * (1 + p (n + inputLoss) (w i)) ∧
        ‖iteratedFDeriv ℝ n (c i) (r, θ)‖ ≤
          A n * (1 : ℝ) ^ (A n) * (1 + p (n + inputLoss) (w i)) := by
    have hpack : A₀ n * (1 + p (n + inputLoss) (w i)) ≤
        A n * (1 + p (n + inputLoss) (w i)) :=
      mul_le_mul_of_nonneg_right (by dsimp only [A]; linarith)
        (add_nonneg zero_le_one (apply_nonneg _ _))
    have hsum := (hraw i hi n r (hr.trans hδρ) θ).trans hpack
    simpa only [Real.one_rpow, mul_one] using
      And.intro ((le_add_of_nonneg_right (norm_nonneg _)).trans hsum)
        ((le_add_of_nonneg_left (norm_nonneg _)).trans hsum)
  exact hflowBound (w i) hlowFlow 1 le_rfl δ hδ.le hδone
    (d i) (c i) (hregular i hi).1 (hregular i hi).2 (hperiod i hi).1 (hperiod i hi).2
    (fun n r hr θ => (hcoef n r hr θ).1) (fun n r hr θ => (hcoef n r hr θ).2)
    (hcontrol i hi)

/-- Exactly the original state-wise controlled-flow output. -/
def N01ControlledRootFlowBound
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base low outLoss : ℕ) (ε r σ : ℝ) (g : ℝ → ℝ)
    {R : ℝ} (hR : 0 < R) (δ Λ : ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
    RootControlledFlowAtState (pairGrading (stateGrading S) realGrading) outLoss B
      (z - (C.referenceState, 0)) δ Λ
      (localizedRootDrift D S C r σ hR z) (localizedRootSpeed D S C g r σ hR z)

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
        N01ControlledRootFlowBound D S C base low outLoss ε r σ g hR δ Λ B := by
  let p := pairGrading (stateGrading S) realGrading
  have hp : Monotone p :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI : HasInterpolation p :=
    coordinate_hasInterpolation_pair (stateGrading_monotone S)
      (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  obtain ⟨lowF, lossF, hfield⟩ := n01_rootCharacteristicField_fixed_loss_bound hS hT hN
  obtain ⟨lowG, outLoss, hfamily⟩ := exists_controlledRootFlow_of_frechet_family hFlow hp hI lossF
  refine ⟨max lowF lowG, outLoss, ?_⟩
  intro r σ g R hσ hR hg hphysical m hcell hstrip Λ hΛ
  obtain ⟨A, hA, hraw⟩ := hfield r σ g R hσ hR hg hphysical m hcell hstrip
  let V : Set (AnnularState S × ℝ) :=
    {z | z ∈ stateNeighborhood S C base ε ∧ stateSector S z.1 ∧
      p (max lowF lowG) (z - (C.referenceState, 0)) ≤ 1}
  let w : (AnnularState S × ℝ) → (AnnularState S × ℝ) :=
    fun z => z - (C.referenceState, 0)
  let d := localizedRootDrift D S C r σ hR
  let c := localizedRootSpeed D S C g r σ hR
  have hregular (z : AnnularState S × ℝ) (hz : z ∈ V) :
      ContDiff ℝ ∞ (d z) ∧ ContDiff ℝ ∞ (c z) :=
    contDiff_localizedRootFields_of_n01 hS hT hN hg hR (hstrip z hz.1 hz.2.1)
  have hlowF (z : AnnularState S × ℝ) (hz : z ∈ V) : p lowF (w z) ≤ 1 :=
    (hp (Nat.le_max_left lowF lowG) _).trans hz.2.2
  have hlowG (z : AnnularState S × ℝ) (hz : z ∈ V) : p lowG (w z) ≤ 1 :=
    (hp (Nat.le_max_right lowF lowG) _).trans hz.2.2
  have hlocalized (z : AnnularState S × ℝ) (hz : z ∈ V) (n : ℕ)
      (t : ℝ) (ht : |t| ≤ R / 4) (θ : ℝ) :
      ‖iteratedFDeriv ℝ n (d z) (t, θ)‖ + ‖iteratedFDeriv ℝ n (c z) (t, θ)‖ ≤
        A n * (1 + p (n + lossF) (w z)) := by
    have he := iteratedFDeriv_localizedRootFields_eq D S C g r σ hR z n (q := (t, θ)) ht
    change ‖iteratedFDeriv ℝ n (localizedRootDrift D S C r σ hR z) (t, θ)‖ +
      ‖iteratedFDeriv ℝ n (localizedRootSpeed D S C g r σ hR z) (t, θ)‖ ≤ _
    rw [he.1, he.2]
    apply hraw z hz.1 hz.2.1 (hlowF z hz) n (t, θ)
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith [(abs_le.mp ht).1, (abs_le.mp ht).2]
  obtain ⟨δ, B, hδ, hδR, hδone, hB, hresult⟩ := hfamily A hA Λ hΛ
    (R / 4) (div_pos hR (by norm_num)) (AnnularState S × ℝ) V w d c hregular
    (fun z _ => periodic_localizedRootFields hS C g r σ hR z) hlowG hlocalized
  exact ⟨δ, B, hδ, hδR, hδone, hB, fun z hz hs hlow => hresult z ⟨hz, hs, hlow⟩⟩

end ContinuousFlexibility.Analysis
