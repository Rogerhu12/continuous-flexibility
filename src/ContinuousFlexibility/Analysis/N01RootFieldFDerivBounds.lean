import ContinuousFlexibility.Analysis.N01RootSpeedJetBounds
import ContinuousFlexibility.Analysis.N01RootDriftJetBounds

/-!
# One common fixed loss for both actual normalized root fields

The actual drift and positive speed factor have ordinary Fréchet jets
on the same two-sided root strip. Their mixed bounds give these jets
with only the order-dependent factor 2^n, absorbed in a numerical
constant selected before the state. The root itself is an interior
point of this genuine smooth strip; no totalized one-sided derivative
is substituted for its ordinary derivative.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n01_rootCharacteristicField_fixed_loss_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ low outLoss : ℕ, ∀ r σ : ℝ, ∀ g : ℝ → ℝ, ∀ R : ℝ,
      (σ = 1 ∨ σ = -1) → 0 < R → ContDiff ℝ ∞ g →
      Ioo ((r - R) - R) ((r + R) + R) ⊆ Ioo D.a D.b →
      ∀ m : ℕ, Ioo (r - R) (r + R) ⊆ D.cells m →
      (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
          (stateHeight D S C z) r σ R) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
      ∀ n : ℕ, ∀ q ∈ Ioo (-R) R ×ˢ (univ : Set ℝ),
        ‖iteratedFDeriv ℝ n
          (orientedCharacteristicDrift (stateProfile D S C z.1)
            (stateHeight D S C z) r σ) q‖ +
        ‖iteratedFDeriv ℝ n
          (factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
            (stateHeight D S C z) r σ) q‖ ≤
          B n * (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
            (z - (C.referenceState, 0))) := by
  let p := pairGrading (stateGrading S) realGrading
  have hp : Monotone p :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  obtain ⟨lowD, lossD, hdrift⟩ := n01_orientedCharacteristicDrift_fixed_loss_bound hS hT hN
  obtain ⟨lowC, lossC, hspeed⟩ := n01_factoredCharacteristicSpeed_fixed_loss_bound hS hT hN
  refine ⟨max lowD lowC, max lossD lossC, ?_⟩
  intro r σ g R hσ hR hg hphysical m hcell hstrip
  obtain ⟨BD, hBD, hDbound⟩ := hdrift r σ g R hσ hR hg hphysical m hcell hstrip
  obtain ⟨BC, hBC, hCbound⟩ := hspeed r σ g R hσ hR hg hphysical m hcell hstrip
  let B : ℕ → ℝ := fun n => (2 : ℝ) ^ n * (BD n + BC n)
  refine ⟨B, fun n => mul_pos (pow_pos (by norm_num) n) (add_pos (hBD n) (hBC n)), ?_⟩
  intro z hz hsector hlow
  let x : AnnularState S × ℝ := z - (C.referenceState, 0)
  have hlowD : p lowD x ≤ 1 := (hp (Nat.le_max_left lowD lowC) x).trans hlow
  have hlowC : p lowC x ≤ 1 := (hp (Nat.le_max_right lowD lowC) x).trans hlow
  let U : Set PolarPoint := Ioo (-R) R ×ˢ (univ : Set ℝ)
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  let d := orientedCharacteristicDrift (stateProfile D S C z.1) (stateHeight D S C z) r σ
  let c := factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
    (stateHeight D S C z) r σ
  obtain ⟨_, hD⟩ := hN.1.1
  have hwref : ContDiff ℝ ∞ D.w := hD.1.2.2.1.1
  have hw := contDiff_stateProfile_of_n01 hS hT hN z.1
  have hZ := contDiff_stateHeight_of_n01 hS hT hN z
  have hregular (q : PolarPoint) (hq : q ∈ U) :
      ContDiffAt ℝ ∞ c q ∧ ContDiffAt ℝ ∞ d q := by
    have hpouter : q ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) := by
      refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith [hq.1.1, hq.1.2]
    obtain ⟨hrq, hwq, hgq, hDq, hQq, _, _⟩ := hstrip z hz hsector q hpouter
    exact contDiffAt_factoredCharacteristicField hwref hg hw hZ hrq hwq hgq hDq hQq
  have hd : ContDiffOn ℝ ∞ d U := fun q hq => (hregular q hq).2.contDiffWithinAt
  have hc : ContDiffOn ℝ ∞ c U := fun q hq => (hregular q hq).1.contDiffWithinAt
  intro n q hq
  have hdM : 0 ≤ BD n * (1 + p (n + lossD) x) :=
    mul_nonneg (hBD n).le (add_nonneg zero_le_one (apply_nonneg _ _))
  have hcM : 0 ≤ BC n * (1 + p (n + lossC) x) :=
    mul_nonneg (hBC n).le (add_nonneg zero_le_one (apply_nonneg _ _))
  have hdnorm : ‖iteratedFDeriv ℝ n d q‖ ≤
      (2 : ℝ) ^ n * (BD n * (1 + p (n + lossD) x)) := by
    apply norm_iteratedFDeriv_le_of_mixedDerivative hU hd n hq hdM
    intro a b hab
    simpa only [Real.norm_eq_abs, hab] using hDbound z hz hsector hlowD a b q hq
  have hcnorm : ‖iteratedFDeriv ℝ n c q‖ ≤
      (2 : ℝ) ^ n * (BC n * (1 + p (n + lossC) x)) := by
    apply norm_iteratedFDeriv_le_of_mixedDerivative hU hc n hq hcM
    intro a b hab
    simpa only [Real.norm_eq_abs, hab] using hCbound z hz hsector hlowC a b q hq
  have hhighD : 1 + p (n + lossD) x ≤ 1 + p (n + max lossD lossC) x :=
    add_le_add (le_refl (1 : ℝ))
      (hp (Nat.add_le_add_left (Nat.le_max_left lossD lossC) n) x)
  have hhighC : 1 + p (n + lossC) x ≤ 1 + p (n + max lossD lossC) x :=
    add_le_add (le_refl (1 : ℝ))
      (hp (Nat.add_le_add_left (Nat.le_max_right lossD lossC) n) x)
  have hdnorm' := hdnorm.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hhighD (hBD n).le) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n))
  have hcnorm' := hcnorm.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hhighC (hBC n).le) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n))
  exact (add_le_add hdnorm' hcnorm').trans_eq (by dsimp only [B]; ring)

end ContinuousFlexibility.Analysis
