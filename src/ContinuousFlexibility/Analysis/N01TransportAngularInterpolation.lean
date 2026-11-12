import ContinuousFlexibility.Analysis.CircleStripAngularInterpolation
import ContinuousFlexibility.Analysis.N01ResidualUniformBounds
import ContinuousFlexibility.Analysis.N01ReturnTransportSpatialTowers
import ContinuousFlexibility.Analysis.MaterialSampleDiscreteEnvelope

/-!
# The actual angular boundary estimates for the transport system

All closed-radius selectors are estimated before a radius is chosen.
The actual spatial towers are then identified with the same circle
families. The independent displacement retains its positive sample
height; the bounded height factors of the other two fields are absorbed
only into numerical constants.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff Topology

local instance n01TransportAngularInterpolationStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

theorem correctionParameterGrading_monotone (S : PhysicalSpacesData) :
    Monotone (pairGrading (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading) :=
  tamePairGrading_monotone (sectorPairGrading_monotone S)
    (gradedSeminorm_monotone (fun n => (S.circle (3 / 4 : ℝ)).level n)
      (S.circle (3 / 4 : ℝ)).bond)

theorem correctionParameterGrading_hasInterpolation
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) :
    HasInterpolation (pairGrading (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading) :=
  hasInterpolation_of_hasSmoothing (correctionParameterGrading_monotone S)
    (hasSmoothing_pairGrading
      (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)
      (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.1)

private theorem transportAngular_one_add_sub_one (a : ℝ) :
    1 + (a - 1) = a := by
  ring

private theorem transportAngular_sample_height_bound
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) :
    ∃ KH : ℝ, 0 ≤ KH ∧ ∀ m, T.H (T.sample m) ^ (3 / 4 : ℝ) ≤ KH := by
  have data : ∃ KH : ℝ, 0 < KH ∧ ∀ m,
      T.H (T.sample m) ^ (3 / 4 : ℝ) * T.M (T.sample m) ^ (0 : ℝ) ≤ KH :=
    materialSample_H_M_envelope hT hRef (γ := (3 / 4 : ℝ)) (by norm_num) 0
  refine ⟨data.choose, data.choose_spec.1.le, fun m => ?_⟩
  simpa only [Real.rpow_zero, mul_one] using data.choose_spec.2 m

private theorem transportAngular_fst_strip_interpolation
    {I E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    {T : MaterialData} {γ : ℝ} {H : CircleModelData}
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {g : I → E → H.Space}
    (hg : UniformSmoothFamilyOn p H.grading U g)
    (hp : Monotone p) (hq : Monotone q) (hU : IsOpen U)
    (hIp : HasInterpolation (pairGrading p q)) (hH : IsCircleModel T γ H)
    (hpos : ∀ m, 0 < T.H (T.sample m))
    (KH : ℝ) (hKH : 0 ≤ KH) (hheight : ∀ m, T.H (T.sample m) ^ γ ≤ KH)
    (l h : ℕ → ℝ) (rsel : I → ℕ → ℝ)
    (hcover : ∀ m r, r ∈ Ioo (l m) (h m) → ∃ i, rsel i m = r)
    {f : ℕ → (E × F) × PolarPoint → ℝ}
    (J : ∀ m, SmoothDirections ((U ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ)) (f m))
    (c : ℝ)
    (heq : ∀ i m, rsel i m ∈ Ioo (l m) (h m) → ∀ x ∈ U ×ˢ univ, ∀ θ,
      f m (x, (rsel i m, θ)) = c + H.decode (g i x.1) m θ)
    (nmax : ℕ) :
    ∃ B : ℕ, ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ m x, x ∈ U ×ˢ univ → ∀ w : E × F,
        pairGrading p q B x ≤ A → pairGrading p q B w ≤ 1 →
        ∀ y : PolarPoint, y.1 ∈ Ioo (l m) (h m) →
        |jointMixedDiagonal (J m) n 0 b x w y| ≤
          K * (1 + pairGrading p q (N + B + 1) x +
            pairGrading p q (N + B + 1) w) ^ ((b : ℝ) / ((N : ℝ) + 1)) := by
  have hg' : UniformSmoothFamilyOn (pairGrading p q) H.grading (U ×ˢ univ)
      (fun i (x : E × F) => g i x.1) :=
    UniformSmoothFamilyOn.fst (E := E) (F := H.Space) (G := F)
      (p := p) (q := H.grading) (r := q) (U := U) (f := g) hg hp hq hU
  exact UniformSmoothFamilyOn.realized_strip_angular_interpolation_add_const
    (I := I) (E := E × F) (T := T) (γ := γ) (H := H)
    (p := pairGrading p q) (U := U ×ˢ univ)
    (g := fun i (x : E × F) => g i x.1) (f := f)
    hg' (tamePairGrading_monotone hp hq) hIp hH hpos KH hKH hheight
    l h rsel hcover J c heq nmax

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)

include hN in
/-- A point of a negative component extends to an actual closed-radius
selector. The extension leaves all other components at their left end. -/
theorem N01Properties.closedRadiusSelector_cover
    (m : ℕ) (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m)) :
    ∃ s : {s : ℕ → ℝ // ∀ i, s i ∈ Icc (C.left i) (C.right i)}, s.val m = r := by
  classical
  let s : ℕ → ℝ := Function.update C.left m r
  have hs (i : ℕ) : s i ∈ Icc (C.left i) (C.right i) := by
    by_cases hi : i = m
    · subst i
      simpa only [s, Function.update_self] using hr
    · have hleft : C.left i ∈ Icc (C.left i) (C.right i) :=
        ⟨le_rfl, (hN.2.2.2.1.1 i).2.1.le⟩
      simpa only [s, Function.update_of_ne hi] using hleft
  exact ⟨⟨s, hs⟩, Function.update_self _ _ _⟩

variable
  (hflow : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
    r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
      deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2)
  (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
  (χ : ℕ → ℝ → ℝ)
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)

include hN hS hT hflow hl hh hχrange in
theorem N01Properties.returnCorrectionPulledDisplacement_angular_diagonal_interpolation
    (J : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionPulledDisplacementLinear S C χ (liftSectorParameter S C x.1.1)
          m x.2 x.1.2))
    (nmax : ℕ) :
    let p := pairGrading (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading
    ∃ B : ℕ, ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ m x, x ∈ sectorNeighborhood S base ε ε ×ˢ univ →
        ∀ w, p B x ≤ A → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l m) (h m) →
        |jointMixedDiagonal (J m) n 0 b x w y| ≤
          K * T.H (T.sample m) ^ (3 / 4 : ℝ) *
            (1 + p (N + B + 1) x + p (N + B + 1) w) ^
              ((b : ℝ) / ((N : ℝ) + 1)) := by
  let I := {s : ℕ → ℝ // ∀ m, s m ∈ Icc (C.left m) (C.right m)}
  let rsel : I → ℕ → ℝ := Subtype.val
  have hrsel (i : I) (m : ℕ) := i.property m
  have hcover (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (l m) (h m)) : ∃ i : I, rsel i m = r :=
    hN.closedRadiusSelector_cover m r ⟨((hl m).trans hr.1).le, (hr.2.trans (hh m)).le⟩
  have hg := hN.uniformSmoothFamilyOn_returnCorrectionPulledDisplacementCircleLinear
    hS hT hflow χ hχrange rsel hrsel
  apply hg.realized_strip_angular_interpolation (correctionParameterGrading_monotone S)
    (correctionParameterGrading_hasInterpolation hS) (hS.2.1 (3 / 4 : ℝ))
    ((material_circle_sample_weights_pos hT hN.1.1).2) l h rsel hcover J _ nmax
  intro i m hr x hx θ
  exact (hN.returnCorrectionPulledDisplacementCircleLinear_decode hS hT χ hχrange
    (rsel i) (hrsel i) x.1 hx.1 x.2 m θ).symm

include hN hS hT hflow hl hh in
theorem N01Properties.returnFlowInverseSlope_angular_diagonal_interpolation
    (J : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnFlowInverseSlope S C (liftSectorParameter S C x.1.1) m x.2))
    (nmax : ℕ) :
    let p := pairGrading (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading
    ∃ B : ℕ, ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ m x, x ∈ sectorNeighborhood S base ε ε ×ˢ univ →
        ∀ w, p B x ≤ A → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l m) (h m) →
        |jointMixedDiagonal (J m) n 0 b x w y| ≤
          K * (1 + p (N + B + 1) x + p (N + B + 1) w) ^
            ((b : ℝ) / ((N : ℝ) + 1)) := by
  let H : CircleModelData := S.circle (3 / 4 : ℝ)
  let p : ℕ → Seminorm ℝ (StateDirections S × ℝ) :=
    pairGrading (sectorGrading S) realGrading
  let U : Set (StateDirections S × ℝ) := sectorNeighborhood S base ε ε
  let I := {s : ℕ → ℝ // ∀ m, s m ∈ Icc (C.left m) (C.right m)}
  let rsel : I → ℕ → ℝ := Subtype.val
  have hrsel (i : I) (m : ℕ) : rsel i m ∈ Icc (C.left m) (C.right m) := i.property m
  have hcover (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (l m) (h m)) : ∃ i : I, rsel i m = r :=
    hN.closedRadiusSelector_cover m r ⟨((hl m).trans hr.1).le, (hr.2.trans (hh m)).le⟩
  let g : I → (StateDirections S × ℝ) → H.Space :=
    fun i => hN.selectorInverseSlopeCircle hS hT (rsel i) (hrsel i)
  have hg : UniformSmoothFamilyOn p H.grading U g :=
    hN.uniformSmoothFamilyOn_selectorInverseSlopeCircle hS hT hflow rsel hrsel
  have data : ∃ KH : ℝ, 0 ≤ KH ∧ ∀ m, T.H (T.sample m) ^ (3 / 4 : ℝ) ≤ KH :=
    transportAngular_sample_height_bound hT hN.1.1
  let KH : ℝ := data.choose
  have hKH : 0 ≤ KH := data.choose_spec.1
  have hhgt (m : ℕ) : T.H (T.sample m) ^ (3 / 4 : ℝ) ≤ KH := data.choose_spec.2 m
  have heq (i : I) (m : ℕ) (_hr : rsel i m ∈ Ioo (l m) (h m))
      (x : (StateDirections S × ℝ) × CircleSpace S) (hx : x ∈ U ×ˢ univ) (θ : ℝ) :
      returnFlowInverseSlope S C (liftSectorParameter S C x.1) m (rsel i m, θ) =
        1 + H.decode (g i x.1) m θ := by
    have hd : H.decode (g i x.1) m θ =
        returnFlowInverseSlope S C (liftSectorParameter S C x.1) m (rsel i m, θ) - 1 :=
      hN.selectorInverseSlopeCircle_decode hS hT (rsel i) (hrsel i) x.1 hx.1 m θ
    exact ((congrArg (fun a : ℝ => 1 + a) hd).trans
      (transportAngular_one_add_sub_one
        (returnFlowInverseSlope S C (liftSectorParameter S C x.1) m (rsel i m, θ)))).symm
  exact transportAngular_fst_strip_interpolation
    (I := I) (E := StateDirections S × ℝ) (F := CircleSpace S)
    (T := T) (γ := (3 / 4 : ℝ)) (H := H)
    (p := p) (q := H.grading) (U := U) (g := g)
    (f := fun m (x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) =>
      returnFlowInverseSlope S C (liftSectorParameter S C x.1.1) m x.2)
    hg (sectorPairGrading_monotone S)
    (gradedSeminorm_monotone (fun n => H.level n) H.bond)
    (sectorNeighborhood_isOpen S base ε ε) (correctionParameterGrading_hasInterpolation hS)
    (hS.2.1 (3 / 4 : ℝ)) ((material_circle_sample_weights_pos hT hN.1.1).2)
    KH hKH hhgt l h rsel hcover J 1 heq nmax

include hN hS hT hflow hl hh hχrange in
theorem N01Properties.returnCorrectionPulledResidual_angular_diagonal_interpolation
    (hR : N02Properties D T S C R base ε)
    (J : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionPulledDisplacementLinear S C χ (liftSectorParameter S C x.1.1)
          m x.2 (R.residual (liftSectorParameter S C x.1.1))))
    (nmax : ℕ) :
    let p := pairGrading (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading
    ∃ B : ℕ, ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ m x, x ∈ sectorNeighborhood S base ε ε ×ˢ univ →
        ∀ w, p B x ≤ A → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l m) (h m) →
        |jointMixedDiagonal (J m) n 0 b x w y| ≤
          K * (1 + p (N + B + 1) x + p (N + B + 1) w) ^
            ((b : ℝ) / ((N : ℝ) + 1)) := by
  let H : CircleModelData := S.circle (3 / 4 : ℝ)
  let p : ℕ → Seminorm ℝ (StateDirections S × ℝ) :=
    pairGrading (sectorGrading S) realGrading
  let U : Set (StateDirections S × ℝ) := sectorNeighborhood S base ε ε
  let I := {s : ℕ → ℝ // ∀ m, s m ∈ Icc (C.left m) (C.right m)}
  let rsel : I → ℕ → ℝ := Subtype.val
  have hrsel (i : I) (m : ℕ) : rsel i m ∈ Icc (C.left m) (C.right m) := i.property m
  have hcover (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (l m) (h m)) : ∃ i : I, rsel i m = r :=
    hN.closedRadiusSelector_cover m r ⟨((hl m).trans hr.1).le, (hr.2.trans (hh m)).le⟩
  let g : I → (StateDirections S × ℝ) → H.Space := fun i z =>
    hN.returnCorrectionPulledDisplacementCircleLinear hS hT χ hχrange
      (rsel i) (hrsel i) z (R.residual (liftSectorParameter S C z))
  have hg : UniformSmoothFamilyOn p H.grading U g :=
    hN.uniformSmoothFamilyOn_returnCorrectionPulledResidual_of_N02
      hS hT hR hflow χ hχrange rsel hrsel
  have data : ∃ KH : ℝ, 0 ≤ KH ∧ ∀ m, T.H (T.sample m) ^ (3 / 4 : ℝ) ≤ KH :=
    transportAngular_sample_height_bound hT hN.1.1
  let KH : ℝ := data.choose
  have hKH : 0 ≤ KH := data.choose_spec.1
  have hhgt (m : ℕ) : T.H (T.sample m) ^ (3 / 4 : ℝ) ≤ KH := data.choose_spec.2 m
  have heq (i : I) (m : ℕ) (_hr : rsel i m ∈ Ioo (l m) (h m))
      (x : (StateDirections S × ℝ) × CircleSpace S) (hx : x ∈ U ×ˢ univ) (θ : ℝ) :
      returnCorrectionPulledDisplacementLinear S C χ (liftSectorParameter S C x.1)
          m (rsel i m, θ) (R.residual (liftSectorParameter S C x.1)) =
        0 + H.decode (g i x.1) m θ := by
    have hd : H.decode (g i x.1) m θ =
        returnCorrectionPulledDisplacementLinear S C χ (liftSectorParameter S C x.1)
          m (rsel i m, θ) (R.residual (liftSectorParameter S C x.1)) :=
      hN.returnCorrectionPulledDisplacementCircleLinear_decode hS hT χ hχrange
        (rsel i) (hrsel i) x.1 hx.1 (R.residual (liftSectorParameter S C x.1)) m θ
    exact hd.symm.trans (zero_add (H.decode (g i x.1) m θ)).symm
  exact transportAngular_fst_strip_interpolation
    (I := I) (E := StateDirections S × ℝ) (F := CircleSpace S)
    (T := T) (γ := (3 / 4 : ℝ)) (H := H)
    (p := p) (q := H.grading) (U := U) (g := g)
    (f := fun m (x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) =>
      returnCorrectionPulledDisplacementLinear S C χ (liftSectorParameter S C x.1.1)
        m x.2 (R.residual (liftSectorParameter S C x.1.1)))
    hg (sectorPairGrading_monotone S)
    (gradedSeminorm_monotone (fun n => H.level n) H.bond)
    (sectorNeighborhood_isOpen S base ε ε) (correctionParameterGrading_hasInterpolation hS)
    (hS.2.1 (3 / 4 : ℝ)) ((material_circle_sample_weights_pos hT hN.1.1).2)
    KH hKH hhgt l h rsel hcover J 0 heq nmax

end ContinuousFlexibility.Statements
