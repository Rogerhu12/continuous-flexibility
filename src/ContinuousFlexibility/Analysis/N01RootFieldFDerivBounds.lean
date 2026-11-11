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

private def rootFieldFDerivMajorant (BD BC : ℕ → ℝ) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * (BD n + BC n)

private theorem rootFieldFDerivMajorant_pos
    {BD BC : ℕ → ℝ} (hBD : ∀ n, 0 < BD n) (hBC : ∀ n, 0 < BC n) (n : ℕ) :
    0 < rootFieldFDerivMajorant BD BC n :=
  mul_pos (pow_pos (by norm_num) n) (add_pos (hBD n) (hBC n))

/-- Mixed-to-Fréchet comparison and every seminorm promotion are kept in
an abstract state space, before actual N01 fields are substituted. -/
private theorem rootField_frechet_pair_bound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {lowD lowC lossD lossC : ℕ} (BD BC : ℕ → ℝ)
    (hBD : ∀ n, 0 < BD n) (hBC : ∀ n, 0 < BC n)
    (x : E) (hlow : p (max lowD lowC) x ≤ 1)
    {U : Set PolarPoint} (hU : IsOpen U) {d c : PolarPoint → ℝ}
    (hd : ContDiffOn ℝ ∞ d U) (hc : ContDiffOn ℝ ∞ c U)
    (hdjet : p lowD x ≤ 1 → ∀ a b : ℕ, ∀ q ∈ U,
      |mixedDerivative a b d q| ≤ BD (a + b) * (1 + p (a + b + lossD) x))
    (hcjet : p lowC x ≤ 1 → ∀ a b : ℕ, ∀ q ∈ U,
      |mixedDerivative a b c q| ≤ BC (a + b) * (1 + p (a + b + lossC) x))
    (n : ℕ) (q : PolarPoint) (hq : q ∈ U) :
    ‖iteratedFDeriv ℝ n d q‖ + ‖iteratedFDeriv ℝ n c q‖ ≤
      rootFieldFDerivMajorant BD BC n * (1 + p (n + max lossD lossC) x) := by
  have hlowD : p lowD x ≤ 1 := (hp (Nat.le_max_left lowD lowC) x).trans hlow
  have hlowC : p lowC x ≤ 1 := (hp (Nat.le_max_right lowD lowC) x).trans hlow
  have hdM : 0 ≤ BD n * (1 + p (n + lossD) x) :=
    mul_nonneg (hBD n).le (add_nonneg zero_le_one (apply_nonneg _ _))
  have hcM : 0 ≤ BC n * (1 + p (n + lossC) x) :=
    mul_nonneg (hBC n).le (add_nonneg zero_le_one (apply_nonneg _ _))
  have hdnorm : ‖iteratedFDeriv ℝ n d q‖ ≤
      (2 : ℝ) ^ n * (BD n * (1 + p (n + lossD) x)) := by
    apply norm_iteratedFDeriv_le_of_mixedDerivative hU hd n hq hdM
    intro a b hab
    simpa only [Real.norm_eq_abs, hab] using hdjet hlowD a b q hq
  have hcnorm : ‖iteratedFDeriv ℝ n c q‖ ≤
      (2 : ℝ) ^ n * (BC n * (1 + p (n + lossC) x)) := by
    apply norm_iteratedFDeriv_le_of_mixedDerivative hU hc n hq hcM
    intro a b hab
    simpa only [Real.norm_eq_abs, hab] using hcjet hlowC a b q hq
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
  exact (add_le_add hdnorm' hcnorm').trans_eq (by
    dsimp only [rootFieldFDerivMajorant]
    ring)

/-- The exact complete Fréchet-jet conclusion, named before selecting
the drift and speed constants. -/
def N01RootCharacteristicFieldFDerivBound
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base low outLoss : ℕ) (ε r σ : ℝ) (g : ℝ → ℝ) (R : ℝ) (B : ℕ → ℝ) : Prop :=
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
          (z - (C.referenceState, 0)))

private theorem n01_rootCharacteristicField_contDiffOn
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {r σ R : ℝ} {g : ℝ → ℝ} (hR : 0 < R) (hg : ContDiff ℝ ∞ g)
    (z : AnnularState S × ℝ)
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) r σ R) :
    ContDiffOn ℝ ∞
        (orientedCharacteristicDrift (stateProfile D S C z.1)
          (stateHeight D S C z) r σ) (Ioo (-R) R ×ˢ (univ : Set ℝ)) ∧
      ContDiffOn ℝ ∞
        (factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
          (stateHeight D S C z) r σ) (Ioo (-R) R ×ˢ (univ : Set ℝ)) := by
  obtain ⟨_, hD⟩ := hN.1.1
  have hwref : ContDiff ℝ ∞ D.w := hD.1.2.2.1.1
  have hw := contDiff_stateProfile_of_n01 hS hT hN z.1
  have hZ := contDiff_stateHeight_of_n01 hS hT hN z
  have hregular (q : PolarPoint) (hq : q ∈ Ioo (-R) R ×ˢ (univ : Set ℝ)) :
      ContDiffAt ℝ ∞
          (factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
            (stateHeight D S C z) r σ) q ∧
        ContDiffAt ℝ ∞
          (orientedCharacteristicDrift (stateProfile D S C z.1)
            (stateHeight D S C z) r σ) q := by
    have hpouter : q ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) := by
      refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith [hq.1.1, hq.1.2]
    obtain ⟨hrq, hwq, hgq, hDq, hQq, _, _⟩ := hstrip q hpouter
    exact contDiffAt_factoredCharacteristicField hwref hg hw hZ hrq hwq hgq hDq hQq
  exact ⟨fun q hq => (hregular q hq).2.contDiffWithinAt,
    fun q hq => (hregular q hq).1.contDiffWithinAt⟩

private theorem n01_rootField_frechet_bound_of_mixed
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss lowD lowC lossD lossC : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {r σ R : ℝ} {g : ℝ → ℝ} (hR : 0 < R) (hg : ContDiff ℝ ∞ g)
    (hstrip : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) r σ R)
    (BD BC : ℕ → ℝ) (hBD : ∀ n, 0 < BD n) (hBC : ∀ n, 0 < BC n)
    (hd : N01OrientedDriftBound D S C base lowD lossD ε r σ R BD)
    (hc : N01FactoredSpeedBound D S C base lowC lossC ε r σ g R BC) :
    N01RootCharacteristicFieldFDerivBound D S C base (max lowD lowC)
      (max lossD lossC) ε r σ g R (rootFieldFDerivMajorant BD BC) := by
  intro z hz hs hlow n q hq
  have hregular := n01_rootCharacteristicField_contDiffOn hS hT hN hR hg z (hstrip z hz hs)
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  exact rootField_frechet_pair_bound
    (p := pairGrading (stateGrading S) realGrading) hp
    (lowD := lowD) (lowC := lowC) (lossD := lossD) (lossC := lossC)
    BD BC hBD hBC (z - (C.referenceState, 0)) hlow
    (isOpen_Ioo.prod isOpen_univ) hregular.1 hregular.2
    (hd z hz hs) (hc z hz hs) n q hq

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
        N01RootCharacteristicFieldFDerivBound D S C base low outLoss ε r σ g R B := by
  obtain ⟨lowD, lossD, hdrift⟩ := n01_orientedCharacteristicDrift_fixed_loss_bound hS hT hN
  obtain ⟨lowC, lossC, hspeed⟩ := n01_factoredCharacteristicSpeed_fixed_loss_bound hS hT hN
  refine ⟨max lowD lowC, max lossD lossC, ?_⟩
  intro r σ g R hσ hR hg hphysical m hcell hstrip
  obtain ⟨BD, hBD, hDbound⟩ := hdrift r σ g R hσ hR hg hphysical m hcell hstrip
  obtain ⟨BC, hBC, hCbound⟩ := hspeed r σ g R hσ hR hg hphysical m hcell hstrip
  exact ⟨rootFieldFDerivMajorant BD BC, rootFieldFDerivMajorant_pos hBD hBC,
    n01_rootField_frechet_bound_of_mixed hS hT hN hR hg hstrip BD BC hBD hBC hDbound hCbound⟩

end ContinuousFlexibility.Analysis
