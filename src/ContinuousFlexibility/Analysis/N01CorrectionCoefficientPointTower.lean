import ContinuousFlexibility.Analysis.N01ReturnVelocityAtResidual
import ContinuousFlexibility.Analysis.N01CoefficientParameterTower
import ContinuousFlexibility.Analysis.ReturnCorrectionCoefficientAlgebra
import ContinuousFlexibility.Analysis.ReturnCorrectionCoefficientJetSymmetry
import ContinuousFlexibility.Analysis.SmoothDirectionsNormedComposition

/-!
# Genuine parameter towers for the actual corrected coefficient error

The coefficient error is assembled from the actual N01 coefficients and
the same cutoff velocity already realized in the circle space. The
actual N02 residual is substituted before differentiating. The square
root is used only on the proved positive transition region; inactive
points have the identically zero tower.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

section ScalarOperations

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
  {U : Set E} {f : E → G}

def SmoothDirections.fstProduct (J : SmoothDirections U f) :
    SmoothDirections (U ×ˢ (univ : Set F)) (fun x : E × F => f x.1) := by
  let L : (E × F) →L[ℝ] E := ContinuousLinearMap.fst ℝ E F
  have hmap : MapsTo (fun x : E × F => (0 : E) + L x) (U ×ˢ univ) U := by
    intro x hx
    simpa only [zero_add, L, ContinuousLinearMap.coe_fst'] using hx.1
  apply (J.compAffine L 0 (J.open_domain.prod isOpen_univ) hmap).congrOn
  intro x hx
  simp only [zero_add, L, ContinuousLinearMap.coe_fst']

def reflectedVelocityDirections {f g : E → ℝ}
    (J : SmoothDirections U f) (K : SmoothDirections U g) :
    SmoothDirections U (fun x => ((f x - g x) / 2, (-g x - f x) / 2)) := by
  let P : (ℝ × ℝ) → ℝ × ℝ := fun q => ((q.1 - q.2) / 2, (-q.2 - q.1) / 2)
  have hP : ContDiff ℝ ∞ P :=
    ((contDiff_fst.sub contDiff_snd).div_const 2).prodMk
      ((contDiff_snd.neg.sub contDiff_fst).div_const 2)
  exact (smoothDirectionsProd J K).comp_contDiff isOpen_univ hP.contDiffOn
    (fun _ _ => mem_univ _)

def coefficientPolynomialDirections
    {a b q : E → ℝ} {e ρ : E → ℝ × ℝ}
    (Ja : SmoothDirections U a) (Jb : SmoothDirections U b) (Jq : SmoothDirections U q)
    (Je : SmoothDirections U e) (Jρ : SmoothDirections U ρ) :
    SmoothDirections U (fun x =>
      (-a x * (ρ x).1,
        -2 * b x * (ρ x).1 - a x * (e x).1 * (ρ x).1 +
          2 * q x * (ρ x).2 + a x * (e x).2 * (ρ x).2)) := by
  let P : (ℝ × (ℝ × (ℝ × ((ℝ × ℝ) × (ℝ × ℝ))))) → ℝ × ℝ := fun y =>
    (-y.1 * y.2.2.2.2.1,
      -2 * y.2.1 * y.2.2.2.2.1 - y.1 * y.2.2.2.1.1 * y.2.2.2.2.1 +
        2 * y.2.2.1 * y.2.2.2.2.2 + y.1 * y.2.2.2.1.2 * y.2.2.2.2.2)
  have hP : ContDiff ℝ ∞ P := by
    dsimp only [P]
    fun_prop
  exact (smoothDirectionsProd Ja (smoothDirectionsProd Jb
    (smoothDirectionsProd Jq (smoothDirectionsProd Je Jρ)))).comp_contDiff
      isOpen_univ hP.contDiffOn (fun _ _ => mem_univ _)

private def coefficientPolynomialSqrtDirections
    {a b c : E → ℝ} {e ρ : E → ℝ × ℝ}
    (Ja : SmoothDirections U a) (Jb : SmoothDirections U b) (Jc : SmoothDirections U c)
    (Je : SmoothDirections U e) (Jρ : SmoothDirections U ρ)
    (hpos : ∀ x ∈ U, 0 < b x ^ 2 - a x * c x) :
    SmoothDirections U (fun x =>
      (-a x * (ρ x).1,
        -2 * b x * (ρ x).1 - a x * (e x).1 * (ρ x).1 +
          2 * Real.sqrt (b x ^ 2 - a x * c x) * (ρ x).2 +
            a x * (e x).2 * (ρ x).2)) := by
  let Jdisc : SmoothDirections U (fun x => b x ^ 2 - a x * c x) :=
    ((smoothDirectionsProd (Jb.mul Jb) (Ja.mul Jc)).comp_contDiff
      (g := fun y : ℝ × ℝ => y.1 - y.2) (V := univ) isOpen_univ
      (contDiff_fst.sub contDiff_snd).contDiffOn (fun _ _ => mem_univ _)).congrOn
        (by intro x hx; simp only [pow_two])
  let Jq : SmoothDirections U (fun x => Real.sqrt (b x ^ 2 - a x * c x)) :=
    Jdisc.comp_contDiff (g := Real.sqrt) (V := Ioi (0 : ℝ)) isOpen_Ioi
      (contDiffOn_id.sqrt (fun q hq => ne_of_gt hq)) (fun x hx => hpos x hx)
  exact coefficientPolynomialDirections Ja Jb Jq Je Jρ

end ScalarOperations

local instance n01CorrectionCoefficientPointTowerStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hR : N02Properties D T S C R base ε)
  (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
  (χ : ℕ → ℝ → ℝ)
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (hcutoff : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
    |iteratedDeriv k (χ m) r| ≤ A * radialE (D.cellIndex (j m)) ^ P)

include hN hS hT hR j hcell hχrange hcutoff in
private theorem returnCorrectionLocalCoefficient_pointTower_nonempty
    (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m))
    (hdisc : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) :
    Nonempty (SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun x : (StateDirections S × ℝ) × CircleSpace S =>
        returnCorrectionLocalCoefficientError D S C R χ (liftSectorParameter S C x.1)
          m p x.2)) := by
  classical
  let rsel : ℕ → ℝ := Function.update C.left m p.1
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have hrsel : ∀ n, rsel n ∈ Icc (C.left n) (C.right n) := by
    intro n
    by_cases hn : n = m
    · subst n
      simpa only [rsel, Function.update_self] using
        (show p.1 ∈ Icc (C.left m) (C.right m) from ⟨hp.1.le, hp.2.le⟩)
    · simpa only [rsel, Function.update_of_ne hn] using
        (show C.left n ∈ Icc (C.left n) (C.right n) from
          ⟨le_rfl, (hcontrol.1 n).2.1.le⟩)
  have hr : rsel m = p.1 := by simp only [rsel, Function.update_self]
  let V (θ : ℝ) : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun x : (StateDirections S × ℝ) × CircleSpace S =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1)
          m (rsel m, θ) x.2) :=
    hN.returnCorrectionVelocity_pointTower hS hT j hcell χ hχrange hcutoff rsel hrsel m θ
  let Ve (θ : ℝ) : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun x : (StateDirections S × ℝ) × CircleSpace S =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1)
          m (rsel m, θ) (R.residual (liftSectorParameter S C x.1))) :=
    (hN.returnCorrectionVelocity_actual_pointTower
      hS hT j hcell χ hχrange hcutoff rsel hrsel hR m θ).fstProduct (F := CircleSpace S)
  let JD : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun x : (StateDirections S × ℝ) × CircleSpace S =>
        (returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1) m p x.2,
          returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1) m p x.2)) :=
    (reflectedVelocityDirections (V p.2) (V (-p.2))).congrOn (by
      intro x hx
      simp only [hr, returnCorrectionDriftLinear_apply, returnCorrectionSpeedLinear_apply])
  let JE : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun x : (StateDirections S × ℝ) × CircleSpace S =>
        (returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1) m p
            (R.residual (liftSectorParameter S C x.1)),
          returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1) m p
            (R.residual (liftSectorParameter S C x.1)))) :=
    (reflectedVelocityDirections (Ve p.2) (Ve (-p.2))).congrOn (by
      intro x hx
      simp only [hr, returnCorrectionDriftLinear_apply, returnCorrectionSpeedLinear_apply])
  let JA0 := hN.originalCoefficientSectorTower (j m) 0 p (hcell m hp)
  let JB0 := hN.originalCoefficientSectorTower (j m) 1 p (hcell m hp)
  let JC0 := hN.originalCoefficientSectorTower (j m) 2 p (hcell m hp)
  let JA : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun x : (StateDirections S × ℝ) × CircleSpace S =>
        (originalCoefficients D S C (liftSectorParameter S C x.1)).a p) :=
    (JA0.congrOn (g := fun z =>
      (originalCoefficients D S C (liftSectorParameter S C z)).a p)
      (by intro z hz; norm_num)).fstProduct (F := CircleSpace S)
  let JB : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun x : (StateDirections S × ℝ) × CircleSpace S =>
        (originalCoefficients D S C (liftSectorParameter S C x.1)).b p) :=
    (JB0.congrOn (g := fun z =>
      (originalCoefficients D S C (liftSectorParameter S C z)).b p)
      (by intro z hz; norm_num)).fstProduct (F := CircleSpace S)
  let JC : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun x : (StateDirections S × ℝ) × CircleSpace S =>
        (originalCoefficients D S C (liftSectorParameter S C x.1)).c p) :=
    (JC0.congrOn (g := fun z =>
      (originalCoefficients D S C (liftSectorParameter S C z)).c p)
      (by intro z hz; norm_num)).fstProduct (F := CircleSpace S)
  let F : ((StateDirections S × ℝ) × CircleSpace S) → ℝ × ℝ := fun x =>
    (-(originalCoefficients D S C (liftSectorParameter S C x.1)).a p *
        returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1) m p x.2,
      -2 * (originalCoefficients D S C (liftSectorParameter S C x.1)).b p *
          returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1) m p x.2 -
        (originalCoefficients D S C (liftSectorParameter S C x.1)).a p *
          returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1) m p
            (R.residual (liftSectorParameter S C x.1)) *
          returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1) m p x.2 +
        2 * Real.sqrt ((originalCoefficients D S C (liftSectorParameter S C x.1)).b p ^ 2 -
          (originalCoefficients D S C (liftSectorParameter S C x.1)).a p *
            (originalCoefficients D S C (liftSectorParameter S C x.1)).c p) *
          returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1) m p x.2 +
        (originalCoefficients D S C (liftSectorParameter S C x.1)).a p *
          returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1) m p
            (R.residual (liftSectorParameter S C x.1)) *
          returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1) m p x.2)
  let K : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ) F :=
    coefficientPolynomialSqrtDirections JA JB JC JE JD (fun x hx =>
      hdisc (liftSectorParameter S C x.1)
        (liftSectorParameter_mem_stateNeighborhood hx.1 le_rfl)
        (hN.2.2.1.liftSectorParameter_sector x.1))
  have hF : EqOn F
      (fun x : (StateDirections S × ℝ) × CircleSpace S =>
        returnCorrectionLocalCoefficientError D S C R χ (liftSectorParameter S C x.1)
          m p x.2) (sectorNeighborhood S base ε ε ×ˢ univ) := by
    intro x hx
    have hpD : p ∈ annularOpen D :=
      ⟨⟨(hcontrol.1 m).1.trans hp.1, hp.2.trans (hcontrol.1 m).2.2⟩, mem_univ _⟩
    exact (returnCorrectionLocalCoefficientError_cancel_denominators D S C R χ
      (liftSectorParameter S C x.1) m p x.2
      (hN.originalRadialCoefficient_pos
        (liftSectorParameter_mem_stateNeighborhood hx.1 le_rfl)
        (hN.2.2.1.liftSectorParameter_sector x.1) hpD).ne').symm
  exact ⟨K.congrOn hF⟩

def N01Properties.returnCorrectionLocalCoefficient_pointTower
    (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m))
    (hdisc : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun x : (StateDirections S × ℝ) × CircleSpace S =>
        returnCorrectionLocalCoefficientError D S C R χ (liftSectorParameter S C x.1)
          m p x.2) :=
  Classical.choice (returnCorrectionLocalCoefficient_pointTower_nonempty
    (hN := hN) (hS := hS) (hT := hT) (hR := hR) (j := j) (hcell := hcell)
    (χ := χ) (hχrange := hχrange) (hcutoff := hcutoff) m p hp hdisc)

def N01Properties.returnCorrectionCoefficient_pointTower
    (hdisc : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m p, p.1 ∈ Ioo (C.left m) (C.right m) → deriv (χ m) p.1 ≠ 0 →
        0 < (originalCoefficients D S C z).b p ^ 2 -
          (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
    (p : PolarPoint) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun x : (StateDirections S × ℝ) × CircleSpace S =>
        returnCorrectionCoefficientError D S C R χ (liftSectorParameter S C x.1) p x.2) := by
  classical
  by_cases h : ∃ m, p.1 ∈ Ioo (C.left m) (C.right m) ∧ deriv (χ m) p.1 ≠ 0
  · have hm := Classical.choose_spec h
    apply (hN.returnCorrectionLocalCoefficient_pointTower hS hT hR j hcell χ hχrange hcutoff
      (Classical.choose h) p hm.1 (fun z hz hs => hdisc z hz hs _ p hm.1 hm.2)).congrOn
    intro x hx
    simp only [returnCorrectionCoefficientError, dif_pos h]
  · let J := (smoothDirectionsLinear
        (0 : ((StateDirections S × ℝ) × CircleSpace S) →L[ℝ] (ℝ × ℝ))).compAffine
        (ContinuousLinearMap.id ℝ ((StateDirections S × ℝ) × CircleSpace S)) 0
        ((sectorNeighborhood_isOpen S base ε ε).prod isOpen_univ)
        (fun _ _ => mem_univ _)
    apply J.congrOn
    intro x hx
    simp only [ContinuousLinearMap.zero_apply, returnCorrectionCoefficientError,
      dif_neg h, LinearMap.zero_apply]

end ContinuousFlexibility.Statements
