import ContinuousFlexibility.Analysis.N01CorrectionOriginalFactorGrowth
import ContinuousFlexibility.Analysis.N01CorrectionCoefficientTameTransfer
import ContinuousFlexibility.Analysis.FlatMixedPolynomialCoefficients

/-!
# Actual coefficient growth from the same-cutoff velocity estimates

The original coefficients and square-root factor have proved N01
growth. The two genuine velocity families provide the remaining input.
Reflection gives the actual drift and speed, the division-free identity
gives the original coefficient error, and uniqueness applies all bounds
to its previously selected joint towers.
-/

noncomputable section

/- Temporary CI diagnostics for slow completed elaboration tasks.
The heartbeat and per-file watchdog limits are unchanged. -/
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace ContinuousFlexibility.Statements

local instance n01CorrectionCoefficientPolynomialGrowthStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped ContDiff Topology

private def correctionPolynomialValue (a b q ve ver vr vrr : ℝ) : ℝ × ℝ :=
  let ed := (ve - ver) / 2
  let ev := (-ver - ve) / 2
  let rd := (vr - vrr) / 2
  let rv := (-vrr - vr) / 2
  (-a * rd, -2 * b * rd - a * ed * rd + 2 * q * rv + a * ev * rv)

private theorem correctionPolynomial_entry_zero_apply
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (p : PolarPoint) :
    originalCoefficientEntry D S C 0 z p = (originalCoefficients D S C z).a p := by
  simp only [originalCoefficientEntry, eq_self_iff_true, ite_true]

private theorem correctionPolynomial_entry_one_apply
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (p : PolarPoint) :
    originalCoefficientEntry D S C 1 z p = (originalCoefficients D S C z).b p := by
  norm_num [originalCoefficientEntry]

private theorem correctionPolynomial_entry_two_apply
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (p : PolarPoint) :
    originalCoefficientEntry D S C 2 z p = (originalCoefficients D S C z).c p := by
  norm_num [originalCoefficientEntry]

private def correctionPolynomial_sqrtDirections
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {U : Set X} {a b c : X → ℝ}
    (Ja : SmoothDirections U a) (Jb : SmoothDirections U b) (Jc : SmoothDirections U c)
    (hpos : ∀ x ∈ U, 0 < b x ^ 2 - a x * c x) :
    SmoothDirections U (fun x => Real.sqrt (b x ^ 2 - a x * c x)) := by
  let Jdisc : SmoothDirections U (fun x => b x ^ 2 - a x * c x) :=
    ((smoothDirectionsProd (Jb.mul Jb) (Ja.mul Jc)).comp_contDiff isOpen_univ
      (contDiff_fst.sub contDiff_snd).contDiffOn (fun _ _ => mem_univ _)).congrOn
        (fun x _ => by simp only [pow_two])
  exact Jdisc.comp_contDiff isOpen_Ioi
    (contDiffOn_id.sqrt (fun q (hq : q ∈ Ioi (0 : ℝ)) => hq.ne')) hpos

section GenericPolynomial

variable {I E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

private def correctionPolynomial_reflectedDirections
    {U : Set E} {V : Set PolarPoint} {f : E × PolarPoint → ℝ}
    (J : SmoothDirections (U ×ˢ V) f) (hU : IsOpen U) (hV : IsOpen V)
    (hmap : ∀ y ∈ V, (y.1, -y.2) ∈ V) :
    SmoothDirections (U ×ˢ V) (fun z => f (z.1, (z.2.1, -z.2.2))) := by
  let L := parameterAngularReflection E
  have hL (z : E × PolarPoint) : L z = (z.1, (z.2.1, -z.2.2)) := by
    simp only [L, parameterAngularReflection, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', neg_apply]
  have hmaps : MapsTo L (U ×ˢ V) (U ×ˢ V) := by
    intro z hz
    simpa only [hL] using
      (show (z.1, (z.2.1, -z.2.2)) ∈ U ×ˢ V from ⟨hz.1, hmap z.2 hz.2⟩)
  exact (J.compLinear L (hU.prod hV) hmaps).congrOn
    (fun z _ => congrArg f (hL z))

private theorem correctionPolynomial_growth_from_velocity
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hIp : HasInterpolation p)
    (W F : I → ℝ) (hW : ∀ i, 1 ≤ W i) (hF : ∀ i, 0 ≤ F i)
    {U : Set E} {V : I → Set PolarPoint}
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hc : ∀ i, Convex ℝ (U ×ˢ V i))
    (hmap : ∀ i y, y ∈ V i → (y.1, -y.2) ∈ V i)
    {a b q ve vr : I → E × PolarPoint → ℝ} {out : I → E × PolarPoint → ℝ × ℝ}
    (Ja : ∀ i, SmoothDirections (U ×ˢ V i) (a i))
    (Jb : ∀ i, SmoothDirections (U ×ˢ V i) (b i))
    (Jq : ∀ i, SmoothDirections (U ×ˢ V i) (q i))
    (Je : ∀ i, SmoothDirections (U ×ˢ V i) (ve i))
    (Jρ : ∀ i, SmoothDirections (U ×ˢ V i) (vr i))
    (Jout : ∀ i, SmoothDirections (U ×ˢ V i) (out i))
    (hfactor : HasFlatMixedTameGrowth p W (fun _ => 1) Ja ∧
      HasFlatMixedTameGrowth p W (fun _ => 1) Jb ∧
        HasFlatMixedTameGrowth p W (fun _ => 1) Jq)
    (hJe : HasFlatMixedTameGrowth p W (fun _ => 1) Je)
    (hJρ : HasFlatMixedTameGrowth p W F Jρ)
    (hpoly : ∀ i x, x ∈ U → ∀ y ∈ V i,
      out i (x, y) = correctionPolynomialValue
        (a i (x, y)) (b i (x, y)) (q i (x, y))
        (ve i (x, y)) (ve i (x, (y.1, -y.2)))
        (vr i (x, y)) (vr i (x, (y.1, -y.2)))) :
    HasFlatMixedTameGrowth p W F
      (fun i => solveSmoothDirectionsPostcomp (Jout i) (ContinuousLinearMap.fst ℝ ℝ ℝ)) ∧
    HasFlatMixedTameGrowth p W F
      (fun i => solveSmoothDirectionsPostcomp (Jout i) (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
  let Jρr : ∀ i, SmoothDirections (U ×ˢ V i)
      (fun z => vr i (z.1, (z.2.1, -z.2.2))) :=
    fun i => correctionPolynomial_reflectedDirections (Jρ i) hU (hV i) (hmap i)
  let Jer : ∀ i, SmoothDirections (U ×ˢ V i)
      (fun z => ve i (z.1, (z.2.1, -z.2.2))) :=
    fun i => correctionPolynomial_reflectedDirections (Je i) hU (hV i) (hmap i)
  have hJρr : HasFlatMixedTameGrowth p W F Jρr :=
    hJρ.reflect_angle Jρr hU hV hmap (fun _ _ _ _ _ => rfl)
  have hJer : HasFlatMixedTameGrowth p W (fun _ => 1) Jer :=
    hJe.reflect_angle Jer hU hV hmap (fun _ _ _ _ _ => rfl)
  let JD : ∀ i, SmoothDirections (U ×ˢ V i)
      (fun z => ((vr i z - vr i (z.1, (z.2.1, -z.2.2))) / 2,
        (-vr i (z.1, (z.2.1, -z.2.2)) - vr i z) / 2)) :=
    fun i => reflectedVelocityDirections (Jρ i) (Jρr i)
  let JE : ∀ i, SmoothDirections (U ×ˢ V i)
      (fun z => ((ve i z - ve i (z.1, (z.2.1, -z.2.2))) / 2,
        (-ve i (z.1, (z.2.1, -z.2.2)) - ve i z) / 2)) :=
    fun i => reflectedVelocityDirections (Je i) (Jer i)
  let Jrd : ∀ i, SmoothDirections (U ×ˢ V i)
      (fun z => (vr i z - vr i (z.1, (z.2.1, -z.2.2))) / 2) :=
    fun i => solveSmoothDirectionsPostcomp (JD i) (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let Jrv : ∀ i, SmoothDirections (U ×ˢ V i)
      (fun z => (-vr i (z.1, (z.2.1, -z.2.2)) - vr i z) / 2) :=
    fun i => solveSmoothDirectionsPostcomp (JD i) (ContinuousLinearMap.snd ℝ ℝ ℝ)
  let Jed : ∀ i, SmoothDirections (U ×ˢ V i)
      (fun z => (ve i z - ve i (z.1, (z.2.1, -z.2.2))) / 2) :=
    fun i => solveSmoothDirectionsPostcomp (JE i) (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let Jev : ∀ i, SmoothDirections (U ×ˢ V i)
      (fun z => (-ve i (z.1, (z.2.1, -z.2.2)) - ve i z) / 2) :=
    fun i => solveSmoothDirectionsPostcomp (JE i) (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hrd : HasFlatMixedTameGrowth p W F Jrd := by
    apply HasFlatMixedTameGrowth.linear_combination hp hW hF Jrd hV
      (1 / 2) (-1 / 2) (hJ := hJρ) (hK := hJρr)
    intro i x hx y hy
    ring
  have hrv : HasFlatMixedTameGrowth p W F Jrv := by
    apply HasFlatMixedTameGrowth.linear_combination hp hW hF Jrv hV
      (-1 / 2) (-1 / 2) (hJ := hJρ) (hK := hJρr)
    intro i x hx y hy
    ring
  have hed : HasFlatMixedTameGrowth p W (fun _ => 1) Jed := by
    apply HasFlatMixedTameGrowth.linear_combination hp hW (fun _ => zero_le_one) Jed hV
      (1 / 2) (-1 / 2) (hJ := hJe) (hK := hJer)
    intro i x hx y hy
    ring
  have hev : HasFlatMixedTameGrowth p W (fun _ => 1) Jev := by
    apply HasFlatMixedTameGrowth.linear_combination hp hW (fun _ => zero_le_one) Jev hV
      (-1 / 2) (-1 / 2) (hJ := hJe) (hK := hJer)
    intro i x hx y hy
    ring
  let JB : ∀ i, SmoothDirections (U ×ˢ V i) (fun z => (out i z).1) :=
    fun i => solveSmoothDirectionsPostcomp (Jout i) (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let JC : ∀ i, SmoothDirections (U ×ˢ V i) (fun z => (out i z).2) :=
    fun i => solveSmoothDirectionsPostcomp (Jout i) (ContinuousLinearMap.snd ℝ ℝ ℝ)
  exact flatMixed_polynomial_coefficient_growth
    (I := I) (E := E) (U := U) (V := V)
    p hp hIp W F hW hF hU hV hc Ja Jb Jq Jed Jev Jrd Jrv JB JC
    (fun i x hx y hy => by
      simpa only [correctionPolynomialValue] using congrArg (fun z : ℝ × ℝ => z.1) (hpoly i x hx y hy))
    (fun i x hx y hy => by
      simpa only [correctionPolynomialValue] using congrArg (fun z : ℝ × ℝ => z.2) (hpoly i x hx y hy))
    hfactor.1 hfactor.2.1 hfactor.2.2 hed hev hrd hrv

end GenericPolynomial

private theorem correctionPolynomial_actual_error
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (χ : ℕ → ℝ → ℝ)
    (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
    (m : ℕ) (x : (StateDirections S × ℝ) × CircleSpace S)
    (hx : x ∈ sectorNeighborhood S base ε ε ×ˢ univ)
    (y : PolarPoint) (hy : y ∈ Ioo (l m) (h m) ×ˢ (univ : Set ℝ)) :
    returnCorrectionCoefficientError D S C R χ (liftSectorParameter S C x.1) y x.2 =
      correctionPolynomialValue
        ((originalCoefficients D S C (liftSectorParameter S C x.1)).a y)
        ((originalCoefficients D S C (liftSectorParameter S C x.1)).b y)
        (Real.sqrt ((originalCoefficients D S C (liftSectorParameter S C x.1)).b y ^ 2 -
          (originalCoefficients D S C (liftSectorParameter S C x.1)).a y *
            (originalCoefficients D S C (liftSectorParameter S C x.1)).c y))
        (returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1) m y
          (R.residual (liftSectorParameter S C x.1)))
        (returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1) m (y.1, -y.2)
          (R.residual (liftSectorParameter S C x.1)))
        (returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1) m y x.2)
        (returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1) m (y.1, -y.2) x.2) := by
  have hy' : y.1 ∈ Ioo (C.left m) (C.right m) :=
    ⟨(hl m).trans hy.1.1, hy.1.2.trans (hh m)⟩
  have hpoint : y ∈ annularOpen D := hN.negativeComponent_subset_annularOpen m ⟨hy', hy.2⟩
  have hapos : 0 < (originalCoefficients D S C (liftSectorParameter S C x.1)).a y :=
    hN.originalRadialCoefficient_pos
      (liftSectorParameter_mem_stateNeighborhood (C := C) hx.1 le_rfl)
      (hN.2.2.1.liftSectorParameter_sector x.1) hpoint
  have hlocal := returnCorrectionLocalCoefficientError_cancel_denominators D S C R χ
    (liftSectorParameter S C x.1) m y x.2 hapos.ne'
  have heq :
      returnCorrectionCoefficientError D S C R χ (liftSectorParameter S C x.1) y x.2 =
        returnCorrectionLocalCoefficientError D S C R χ (liftSectorParameter S C x.1) m y x.2 :=
    congrArg (fun A : CircleSpace S →ₗ[ℝ] (ℝ × ℝ) => A x.2)
      (returnCorrectionCoefficientError_eq_local hN.2.2.2.1.2.2.1 R χ
        (liftSectorParameter S C x.1) m y hy')
  simpa only [correctionPolynomialValue, returnCorrectionDriftLinear_apply,
    returnCorrectionSpeedLinear_apply] using heq.trans hlocal

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hR : N02Properties D T S C R base ε)
  (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
  (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
  (hstripDisc : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m (p : PolarPoint),
    p.1 ∈ Ioo (l m) (h m) →
      0 < (originalCoefficients D S C (liftSectorParameter S C z)).b p ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C z)).a p *
          (originalCoefficients D S C (liftSectorParameter S C z)).c p)
  {lam P : ℝ} (hlam : 0 < lam) (hP : 0 ≤ P)
  (hpositive : ∀ z ∈ stateNeighborhood S C base ε, ∀ (m : ℕ) (p : PolarPoint),
    p.1 ∈ Ioo (l m) (h m) →
    let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
    d ≤ (originalCoefficients D S C z).a p ∧
    d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)

include hlam hP hpositive

theorem N01Properties.returnCorrectionCoefficient_joint_growth_of_velocity
    (Jρ : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2))
    (Je : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
          (R.residual (liftSectorParameter S C x.1.1))))
    (hJρ : HasFlatMixedTameGrowth
      (pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading)
      (fun m => radialE (D.cellIndex (j m)))
      (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)) Jρ)
    (hJe : HasFlatMixedTameGrowth
      (pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading)
      (fun m => radialE (D.cellIndex (j m))) (fun _ => 1) Je) :
    let p := pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading
    let W := fun m => radialE (D.cellIndex (j m))
    let F := fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)
    HasFlatMixedTameGrowth p W F
      (fun m => solveSmoothDirectionsPostcomp
        (hN.returnCorrectionCoefficient_parameterSpatialTower hS hT hR χ hχ hχrange
          m (j m) (hcell m) (l m) (h m) (hl m) (hh m)
          (fun z hz q hq => hstripDisc z hz m q hq)) (ContinuousLinearMap.fst ℝ ℝ ℝ)) ∧
    HasFlatMixedTameGrowth p W F
      (fun m => solveSmoothDirectionsPostcomp
        (hN.returnCorrectionCoefficient_parameterSpatialTower hS hT hR χ hχ hχrange
          m (j m) (hcell m) (l m) (h m) (hl m) (hh m)
          (fun z hz q hq => hstripDisc z hz m q hq)) (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
  let E := (StateDirections S × ℝ) × CircleSpace S
  let U : Set E := sectorNeighborhood S base ε ε ×ˢ univ
  let V : ℕ → Set PolarPoint := fun m => Ioo (l m) (h m) ×ˢ univ
  let p := pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading
  let W : ℕ → ℝ := fun m => radialE (D.cellIndex (j m))
  let F : ℕ → ℝ := fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)
  let a : ℕ → E × PolarPoint → ℝ := fun _ x =>
    (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2
  let b : ℕ → E × PolarPoint → ℝ := fun _ x =>
    (originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2
  let c : ℕ → E × PolarPoint → ℝ := fun _ x =>
    (originalCoefficients D S C (liftSectorParameter S C x.1.1)).c x.2
  let q : ℕ → E × PolarPoint → ℝ := fun m x => Real.sqrt (b m x ^ 2 - a m x * c m x)
  let ve : ℕ → E × PolarPoint → ℝ := fun m x =>
    returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
      (R.residual (liftSectorParameter S C x.1.1))
  let vr : ℕ → E × PolarPoint → ℝ := fun m x =>
    returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2
  let out : ℕ → E × PolarPoint → ℝ × ℝ := fun _ x =>
    returnCorrectionCoefficientError D S C R χ (liftSectorParameter S C x.1.1) x.2 x.1.2
  have hp : Monotone p := correctionParameterGrading_monotone S
  have hIp : HasInterpolation p := correctionParameterGrading_hasInterpolation hS
  have hW (m : ℕ) : 1 ≤ W m := one_le_radialE_of_nat _
  have hF (m : ℕ) : 0 ≤ F m :=
    (Real.rpow_pos_of_pos ((material_circle_sample_weights_pos hT hN.1.1).2 m) _).le
  have hU : IsOpen U := (sectorNeighborhood_isOpen S base ε ε).prod
    (isOpen_univ : IsOpen (univ : Set (CircleSpace S)))
  have hV (m : ℕ) : IsOpen (V m) :=
    (isOpen_Ioo : IsOpen (Ioo (l m) (h m))).prod
      (isOpen_univ : IsOpen (univ : Set ℝ))
  have hc (m : ℕ) : Convex ℝ (U ×ˢ V m) :=
    ((sectorNeighborhood_convex S base ε ε).prod convex_univ).prod
      ((convex_Ioo (l m) (h m)).prod convex_univ)
  let Jentry : ∀ (i : Fin 3) (m : ℕ), SmoothDirections (U ×ˢ V m)
      (fun x : E × PolarPoint => originalCoefficientEntry D S C i
        (liftSectorParameter S C x.1.1) x.2) := fun i m =>
    (N01Properties.originalCoefficient_stripTower
      (D := D) (T := T) (S := S) (C := C)
      (base := base) (loss := loss) (ε := ε) hN hS hT j hcell l h hl hh i m).fstParameter
        (F := CircleSpace S) (sectorNeighborhood_isOpen S base ε ε) (hV m)
  let Ja : ∀ m, SmoothDirections (U ×ˢ V m) (a m) := fun m =>
    (Jentry 0 m).congrOn (fun x _ => correctionPolynomial_entry_zero_apply D S C
      (liftSectorParameter S C x.1.1) x.2)
  let Jb : ∀ m, SmoothDirections (U ×ˢ V m) (b m) := fun m =>
    (Jentry 1 m).congrOn (fun x _ => correctionPolynomial_entry_one_apply D S C
      (liftSectorParameter S C x.1.1) x.2)
  let Jc : ∀ m, SmoothDirections (U ×ˢ V m) (c m) := fun m =>
    (Jentry 2 m).congrOn (fun x _ => correctionPolynomial_entry_two_apply D S C
      (liftSectorParameter S C x.1.1) x.2)
  let Jq : ∀ m, SmoothDirections (U ×ˢ V m) (q m) := fun m =>
    correctionPolynomial_sqrtDirections (X := E × PolarPoint) (U := U ×ˢ V m)
      (a := a m) (b := b m) (c := c m) (Ja m) (Jb m) (Jc m)
      (fun x hx => hstripDisc x.1.1 hx.1.1 m x.2 hx.2.1)
  have hfactor : HasFlatMixedTameGrowth p W (fun _ => 1) Ja ∧
      HasFlatMixedTameGrowth p W (fun _ => 1) Jb ∧
        HasFlatMixedTameGrowth p W (fun _ => 1) Jq :=
    N01Properties.originalCorrectionFactors_flat_mixed_growth
      (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
      (lam := lam) (P := P) hN hS hT j hcell l h hl hh hlam hP hpositive Ja Jb Jq
  let Jout : ∀ m, SmoothDirections (U ×ˢ V m) (out m) := fun m =>
    N01Properties.returnCorrectionCoefficient_parameterSpatialTower
      (D := D) (T := T) (S := S) (C := C) (R := R)
      (base := base) (loss := loss) (ε := ε) hN hS hT hR χ hχ hχrange
      m (j m) (hcell m) (l m) (h m) (hl m) (hh m)
      (fun z hz y hy => hstripDisc z hz m y hy)
  exact correctionPolynomial_growth_from_velocity
    (I := ℕ) (E := E) (U := U) (V := V)
    (a := a) (b := b) (q := q) (ve := ve) (vr := vr) (out := out)
    p hp hIp W F hW hF hU hV hc (fun _ y hy => ⟨hy.1, mem_univ _⟩)
    Ja Jb Jq Je Jρ Jout hfactor hJe hJρ
    (fun m x hx y hy => correctionPolynomial_actual_error
      (D := D) (T := T) (S := S) (C := C) (R := R)
      (base := base) (loss := loss) (ε := ε) hN χ l h hl hh m x hx y hy)

end ContinuousFlexibility.Statements
