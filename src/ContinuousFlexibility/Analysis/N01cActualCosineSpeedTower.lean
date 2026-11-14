module

public import ContinuousFlexibility.Analysis.N01cEndpointCosineTower
public import ContinuousFlexibility.Analysis.N01cWholeSpeedPowerBounds
public import ContinuousFlexibility.Analysis.N01cStateInterpolation

/-!
# The actual cosine speed on the original state space

The genuine whole characteristic-speed and drift fields supply all
angular state jets. Their endpoint estimates, together with the exact
signed cosine formula, give joint time, state and direction continuity.
Only the actual projective state topology is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

private theorem continuous_pairRealGrading
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    (p : ℕ → Seminorm ℝ X) (n : ℕ) (hp : Continuous (p n)) :
    Continuous (pairGrading p realGrading n) := by
  have he : (pairGrading p realGrading n : X × ℝ → ℝ) =
      (fun z => p n z.1 + ‖z.2‖) := by
    funext z
    simp only [pairGrading_apply, realGrading, coe_normSeminorm]
  rw [he]
  exact (hp.comp continuous_fst).add continuous_snd.norm

private theorem convex_productSeminormNeighborhood
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    (p : Seminorm ℝ X) (center : X) (ε : ℝ) :
    Convex ℝ {z : X × ℝ | p (z.1 - center) < ε ∧ |z.2| < ε} := by
  have he : {z : X × ℝ | p (z.1 - center) < ε ∧ |z.2| < ε} =
      ({x : X | p (x - center) < ε} ×ˢ {t : ℝ | |t| < ε}) := by
    ext z
    simp only [Set.mem_prod, Set.mem_ofPred_eq]
  rw [he]
  have h := (convex_seminormDisplacement_lt p center ε).prod
    (convex_seminormDisplacement_lt (normSeminorm ℝ ℝ) 0 ε)
  simpa only [sub_zero, coe_normSeminorm, Real.norm_eq_abs] using h

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

/-- Continuity of the actual joint grading is inherited from its two summands. -/
theorem n01c_continuous_jointStateGrading (S : PhysicalSpacesData) (n : ℕ) :
    Continuous (pairGrading (stateGrading S) realGrading n) :=
  continuous_pairRealGrading (stateGrading S) n (continuous_stateGrading S n)

/-- The original separate state and scalar bounds form a convex neighbourhood. -/
theorem n01c_convex_stateNeighborhood (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base : ℕ) (ε : ℝ) :
    Convex ℝ (stateNeighborhood S C base ε) :=
  convex_productSeminormNeighborhood (stateGrading S base) C.referenceState ε

/-- Every actual component has a genuine joint state-angle tower whose
evaluations are jointly continuous at all real cosine times. The optical
input below is the already constructed primitive root field, not a flow
regularity or flow estimate hypothesis. -/
def componentCosineSpeed_continuousTimeSpeedTower
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hB : N01PartB D S C base ε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b)
    (hI : ∀ s : ℕ, ∃ B : ℝ, 1 ≤ B ∧
      ∀ n : ℕ, n ≤ s → ∀ x : AnnularState S × ℝ,
      pairGrading (stateGrading S) realGrading base x ≤ 1 →
      ∀ R : ℝ, 1 ≤ R → pairGrading (stateGrading S) realGrading (s + loss) x ≤ R →
        pairGrading (stateGrading S) realGrading (n + 4) x ≤
          B * R ^ ((n : ℝ) / ((s : ℝ) + 1)))
    (G : ∀ m, MixedJetRegularity (stateNeighborhood S C base ε)
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) (stateOpticalRootField D S C))
    (hG : EndpointMixedPowerBounds (pairGrading (stateGrading S) realGrading)
      (C.referenceState, 0) base loss (stateNeighborhood S C base ε)
      (fun m => Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
      (fun m q => min (q.1 - C.left m) (C.right m - q.1))
      (fun m _ => T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ))
      (fun m _ => T.E0 (T.sample (C.cell m))) (fun _ => stateOpticalRootField D S C))
    (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ m r,
      r ∈ Icc (C.left m) (C.right m) →
        0 < twoRootDivided (componentOpticalSquare D S C m z)
          (C.left m) (C.right m) r)
    (m : ℕ) :
    ContinuousTimeSpeedTower (stateNeighborhood S C base ε)
      (componentCosineSpeed D S C m) := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  let U := stateNeighborhood S C base ε
  let Ω : ℕ → Set PolarPoint := fun i => Ioo (C.left i) (C.right i) ×ˢ univ
  let δ : ℕ → PolarPoint → ℝ := fun i q => min (q.1 - C.left i) (C.right i - q.1)
  let H : ℕ → ℝ := fun i => T.H (T.sample (C.cell i)) ^ (3 / 4 : ℝ)
  let E : ℕ → ℝ := fun i => T.E0 (T.sample (C.cell i))
  let p := pairGrading (stateGrading S) realGrading
  have hε1 : ε ≤ 1 := hε2.trans (by norm_num)
  let F := wholeCharacteristicSpeed_powerControl
    hS hT hA hε hε1 hB hE hloc hχloc hI G hG
  let A := normalizedSpeedFactor_controlled
    hS hT hA hε hε1 hB hE hloc hχloc hI (0 : Fin 2)
  have hAval : A.value = normalizedSpeedFactor D S C 0 :=
    normalizedSpeedFactor_controlled_value hS hT hA hε hε1 hB hE hloc hχloc hI 0
  have hcore (i : ℕ) {q : PolarPoint} (hq : q ∈ Ω i) : q ∈ annularOpen D :=
    ⟨⟨(hA.2.2.1.1 i).1.trans hq.1.1, hq.1.2.trans (hA.2.2.1.1 i).2.2⟩, mem_univ _⟩
  let RA : MixedJetRegularity U (Ω m) A.value :=
    ⟨fun z hz => (A.regular.spatial z hz).mono (fun q hq => hcore m hq),
      fun a b q hq => A.regular.parameter a b q (hcore m hq)⟩
  have hAR : EndpointMixedPowerBounds p (C.referenceState, 0) base loss U Ω δ
      (fun i _ => H i) (fun i _ => E i) (fun _ => A.value) :=
    mixedPowerBounds_to_componentSamples hT hA.1.1 hA.2.2.1 hloc hE A.bounds
  have hs := materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m)
  have hfinite : IsFiniteAffineTimeSmooth U (componentCosineSpeed D S C m) :=
    fun n x L => contDiffOn_componentCosineSpeed_finiteAffine hS hT hA hB hpos m x L
  exact continuousTimeSpeedTower_of_signedEndpointBounds
    (X := AnnularState S × ℝ) (ι := ℕ)
    p (jointStateGrading_monotone S) (n01c_continuous_jointStateGrading S)
    (C.referenceState, 0) base loss
    (isOpen_stateNeighborhood S C base ε) (n01c_convex_stateNeighborhood S C base ε)
    (fun z hz => (jointStateGrading_displacement_lt_one hε2 hz).le)
    C.left C.right δ H E
    (fun _ z => minusCharacteristicSpeed (originalCoefficients D S C z))
    (fun _ => A.value) F.bounds hAR m (hA.2.2.1.1 m).2.1 (hE _ hs)
    (F.regular m) RA (componentCosineSpeed D S C m) hfinite
    (fun z hz t θ => by
      rw [hAval]
      exact componentCosineSpeed_eq_signed hS hT hA hB hz m t θ)

end ContinuousFlexibility.Statements
