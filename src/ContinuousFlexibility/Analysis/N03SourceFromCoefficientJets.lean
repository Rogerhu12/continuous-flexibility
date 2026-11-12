import ContinuousFlexibility.Analysis.ReturnCorrectionSourceSmoothTame
import ContinuousFlexibility.Analysis.ReturnCorrectionSourceRealization
import ContinuousFlexibility.Analysis.N01ResidualSectorCoordinates
import ContinuousFlexibility.Analysis.PhysicalGradeEnergy
import ContinuousFlexibility.Analysis.TameSmoothingCalculus

/-!
# The original N03 source operator from its actual coefficient jets

The coefficient tower is tied by its zeroth decoder to the same cutoff
error. Its material bounds supply membership on all admissible sector
states through the original affine sector coordinates. The existing
bilinear source realization then has the full smooth tame tower proved
by the divergence calculus; no source membership or tame assumption is
introduced here.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n03SourceFromCoefficientJetsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

local instance n03SourceFromCoefficientJetsParameterSMul (S : PhysicalSpacesData) :
    SMul ℝ ((StateDirections S × ℝ) × CircleSpace S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.symmetricDivergenceBilinear_actual_of_eq
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ)
    (ρ : CircleSpace S) (η : HeightPair S) (A : annularSmoothCoefficientSpace D)
    (hA : A.val = fun p => returnCorrectionCoefficientError D S C R χ z p ρ) :
    symmetricDivergenceBilinear hS hT A η =
      returnCorrectionResidualErrorField D S C R χ z ρ η := by
  have hregular : ContDiffOn ℝ ∞
      (fun p => returnCorrectionCoefficientError D S C R χ z p ρ) (annularOpen D) :=
    hA ▸ A.property
  have heq : A = ⟨_, hregular⟩ := Subtype.ext hA
  exact (congrArg (fun B => symmetricDivergenceBilinear hS hT B η) heq).trans
    (hN.symmetricDivergenceBilinear_actual hS hT R χ z ρ η hregular)

theorem N01Properties.exists_returnCorrectionSource_of_coefficient_jets
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ)
    (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (hsupp : ∀ m, Function.support (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m))
    (hend : ∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
      χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1))
    (hdisc : ∀ z ∈ stateNeighborhood S C base ε, ∀ m p,
      p.1 ∈ tsupport (deriv (χ m)) →
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
    (A : ∀ n : ℕ, ((StateDirections S × ℝ) × CircleSpace S) →
      MultilinearMap ℝ (fun _ : Fin n => (StateDirections S × ℝ) × CircleSpace S)
        (annularSmoothCoefficientSpace D))
    (hzero : ∀ x ∈ sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S)),
      (A 0 x Fin.elim0).val =
        fun p => returnCorrectionCoefficientError D S C R χ (liftSectorParameter S C x.1) p x.2)
    (hcoeff : LocalCoefficientMaterialTameBounds (T := T)
      (U := sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S)))
      (pairGrading (pairGrading (sectorGrading S) realGrading)
        (S.circle (3 / 4 : ℝ)).grading) A)
    (hsym : ∀ n x, x ∈ sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S)) →
      ∀ v, SymmetricErrorCoefficientSymmetry (A n x v).val)
    (hderiv : ∀ n (x w : (StateDirections S × ℝ) × CircleSpace S)
      (v : Fin n → (StateDirections S × ℝ) × CircleSpace S) (t : ℝ),
      x + t • w ∈ sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S)) →
      MixedJetHasDerivAt
        (fun s r => ((A n (x + s • w) v).val (T.radius r.1, r.2)).1)
        (fun r => ((A (n + 1) (x + t • w) (Fin.cons w v)).val
          (T.radius r.1, r.2)).1) t ∧
      MixedJetHasDerivAt
        (fun s r => ((A n (x + s • w) v).val (T.radius r.1, r.2)).2)
        (fun r => ((A (n + 1) (x + t • w) (Fin.cons w v)).val
          (T.radius r.1, r.2)).2) t) :
    ∃ E : AnnularState S × ℝ → CircleSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] S.Source,
      (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ ρ η p,
        physicalSourceDecode S (E z ρ η) p = returnCorrectionResidualErrorField D S C R χ z ρ η p) ∧
      SmoothTameOn
        (pairGrading (pairGrading (pairGrading (sectorGrading S) realGrading)
          (S.circle (3 / 4 : ℝ)).grading) (heightPairGrading S))
        S.sourceGrading ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ univ)
        (fun z : ((StateDirections S × ℝ) × CircleSpace S) × HeightPair S =>
          E (liftSectorParameter S C z.1.1) z.1.2 z.2) := by
  have hsectorMember (x : (StateDirections S × ℝ) × CircleSpace S)
      (hx : x ∈ sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S)))
      (η : HeightPair S) : HeightMember D T (3 / 4 : ℝ)
      (returnCorrectionResidualErrorField D S C R χ (liftSectorParameter S C x.1) x.2 η) := by
    have hm := hcoeff.divergence_heightMember hS hT hsym 0 x hx Fin.elim0 η
    have heq := hN.symmetricDivergenceBilinear_actual_of_eq hS hT R χ
      (liftSectorParameter S C x.1) x.2 η (A 0 x Fin.elim0) (hzero x hx)
    exact (congrArg (HeightMember D T (3 / 4 : ℝ)) heq).mp hm
  have hmember (z : AnnularState S × ℝ) (hz : z ∈ stateNeighborhood S C base ε)
      (hs : stateSector S z.1) (ρ : CircleSpace S) (η : HeightPair S) :
      HeightMember D T (3 / 4 : ℝ) (returnCorrectionResidualErrorField D S C R χ z ρ η) := by
    let y := hN.2.2.1.sectorParameterOfState z hs
    have hy : y ∈ sectorNeighborhood S base ε ε :=
      hN.2.2.1.sectorParameterOfState_mem z hs hz
    have hm := hsectorMember (y, ρ) ⟨hy, mem_univ _⟩ η
    have heq := congrArg (fun u => returnCorrectionResidualErrorField D S C R χ u ρ η)
      (hN.2.2.1.lift_sectorParameterOfState z hs)
    exact (congrArg (HeightMember D T (3 / 4 : ℝ)) heq).mp hm
  let E : AnnularState S × ℝ → CircleSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] S.Source :=
    returnCorrectionSourceError hN hS hT R χ hχ hχrange hsupp hend hdisc hmember
  have hdecode (z : AnnularState S × ℝ) (hz : z ∈ stateNeighborhood S C base ε)
      (hs : stateSector S z.1) (ρ : CircleSpace S) (η : HeightPair S) :
      physicalSourceDecode S (E z ρ η) = returnCorrectionResidualErrorField D S C R χ z ρ η :=
    returnCorrectionSourceError_decode hN hS hT R χ hχ hχrange hsupp hend hdisc hmember hz hs ρ η
  refine ⟨E, fun z hz hs ρ η p => congrFun (hdecode z hz hs ρ η) p, ?_⟩
  let p : ℕ → Seminorm ℝ ((StateDirections S × ℝ) × CircleSpace S) :=
    pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading
  let q : ℕ → Seminorm ℝ (HeightPair S) := heightPairGrading S
  have hp : Monotone p := pairGrading_monotone (sectorPairGrading_monotone S)
    (gradedSeminorm_monotone _ _)
  have hq : Monotone q := pairGrading_monotone (gradedSeminorm_monotone _ _) (fun _ _ _ _ => le_rfl)
  have hpcont (s : ℕ) : Continuous (p s) := by
    change Continuous (fun x : (StateDirections S × ℝ) × CircleSpace S =>
      pairGrading (sectorGrading S) realGrading s x.1 + (S.circle (3 / 4 : ℝ)).grading s x.2)
    exact ((sectorPairGrading_continuous S s).comp continuous_fst).add
      (((withSeminorms_graded _ _).continuous_seminorm s).comp continuous_snd)
  have hqcont (s : ℕ) : Continuous (q s) := by
    change Continuous (fun η : HeightPair S => (S.height (3 / 4 : ℝ)).grading s η.1 + ‖η.2‖)
    exact (((withSeminorms_graded _ _).continuous_seminorm s).comp continuous_fst).add
      continuous_snd.norm
  have hIp : HasInterpolation p := hasInterpolation_of_hasSmoothing hp
    (hasSmoothing_pairGrading
      (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)
      (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.1)
  have hIq : HasInterpolation q := hasInterpolation_of_hasSmoothing hq
    (hasSmoothing_pairGrading (hS.2.2.2.1 (3 / 4 : ℝ)).2.1 hasSmoothing_realGrading)
  have hheight (s : ℕ) (η : HeightPair S) : physicalNorm T (3 / 4 : ℝ) s
      ((S.height (3 / 4 : ℝ)).decode η.1) ≤ q s η :=
    (sobolevModel_physicalNorm_le_grading (hS.1 (3 / 4 : ℝ)) η.1 s).trans
      (le_add_of_nonneg_right (apply_nonneg (realGrading s) η.2))
  refine smoothTameOn_symmetricSource_of_coefficient_jets
    (E := (StateDirections S × ℝ) × CircleSpace S) (D := D) (T := T) (S := S)
    (U := sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S))) hS hT
    ((sectorNeighborhood_isOpen S base ε ε).prod isOpen_univ)
    ((sectorNeighborhood_convex S base ε ε).prod convex_univ)
    p q hpcont hqcont hp hq hIp hIq hheight A hcoeff hsym hderiv
    (fun z : ((StateDirections S × ℝ) × CircleSpace S) × HeightPair S =>
      E (liftSectorParameter S C z.1.1) z.1.2 z.2) ?_
  intro z hz
  exact (hdecode (liftSectorParameter S C z.1.1)
    (liftSectorParameter_mem_stateNeighborhood hz.1.1 le_rfl)
    (hN.2.2.1.liftSectorParameter_sector _) z.1.2 z.2).trans
      (hN.symmetricDivergenceBilinear_actual_of_eq hS hT R χ
        (liftSectorParameter S C z.1.1) z.1.2 z.2 (A 0 z.1 Fin.elim0) (hzero z.1 hz.1)).symm

end ContinuousFlexibility.Statements
