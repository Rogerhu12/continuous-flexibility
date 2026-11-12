import ContinuousFlexibility.Analysis.CoupledCircleAverageSmooth
import ContinuousFlexibility.Analysis.CoupledCircleProductSmooth
import ContinuousFlexibility.Analysis.CoupledPhysicalTameComposition
import ContinuousFlexibility.Analysis.CoupledNeighborhoodRestriction
import ContinuousFlexibility.Analysis.SolveReturnEquations
import ContinuousFlexibility.Analysis.SpacesCircleParity
import ContinuousFlexibility.Scalar.WeightedSmoothTameLinear

/-!
# Joint smooth tameness of the given return error

The actual averaged composition, angular derivative, product, and parity
projections give the independent bilinear error formula. On the original
sector neighborhood, the N02 decoder identifies this expression with the
supplied return error. Every residual argument remains unrestricted.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Function ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section CircleFormula

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
  (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading)

def coupledCircleErrorFormula (travel : ℕ → ℝ) (e r v : M.Space) : M.Space :=
  circleModelEvenProjection hM
    (coupledCircleProduct hD hT hγ hM hI r
      (coupledCircleAverageCompose hD hT hγ hM hI travel e
        (coupledCircleDerivative hM v))) -
    coupledCircleProduct hD hT hγ hM hI (coupledCircleDerivative hM r)
      (circleModelOddProjection hM
        (coupledCircleShiftedCompose hD hT hγ hM hI travel e v))

theorem coupledCircleErrorFormula_decode
    (travel : ℕ → ℝ) (e r v : M.Space) (m : ℕ) (θ : ℝ) :
    M.decode (coupledCircleErrorFormula hD hT hγ hM hI travel e r v) m θ =
      evenPart (fun t => M.decode r m t *
        ∫ a in (0 : ℝ)..1, deriv (M.decode v m)
          (t + travel m + a * M.decode e m t)) θ -
      deriv (M.decode r m) θ *
        oddPart (fun t => M.decode v m (t + travel m + M.decode e m t)) θ := by
  simp only [coupledCircleErrorFormula, map_sub, Pi.sub_apply,
    circleModelEvenProjection_decode, coupledCircleProduct_decode,
    coupledCircleAverageCompose_decode, coupledCircleDerivative_decode,
    circleModelOddProjection_decode, coupledCircleShiftedCompose_decode, evenPart, oddPart]

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  {p : ℕ → Seminorm ℝ X} {U : Set X} {e r v : X → M.Space}

theorem coupledCircleErrorFormula_smoothTameOn
    (travel : ℕ → ℝ) (hp : Monotone p) (ht : WithSeminorms p)
    (he : SmoothTameOn p M.grading U e)
    (hr : SmoothTameOn p M.grading U r)
    (hv : SmoothTameOn p M.grading U v) :
    SmoothTameOn p M.grading U
      (fun x => coupledCircleErrorFormula hD hT hγ hM hI travel (e x) (r x) (v x)) := by
  letI : IsTopologicalAddGroup X := ht.isTopologicalAddGroup
  letI : ContinuousSMul ℝ X := ht.continuousSMul
  letI : ∀ n, CompleteSpace (M.level n) :=
    fun n => (hM.2.1 n).isComplete.completeSpace_coe
  have htc : WithSeminorms M.grading := withSeminorms_graded _ _
  have htcc := withSeminorms_pairGrading htc htc
  letI : LocallyConvexSpace ℝ (M.Space × M.Space) := htcc.toLocallyConvexSpace
  have hdr := smoothTameOn_postcompose_generic hp ht htc hr
    (coupledCircleDerivative hM) (coupledCircleDerivativeLinear_isTame hM)
  have hdv := smoothTameOn_postcompose_generic hp ht htc hv
    (coupledCircleDerivative hM) (coupledCircleDerivativeLinear_isTame hM)
  have havg := smoothTameOn_comp_generic hp ht htcc
    (smoothTameOn_prodMk_generic hp ht he hdv)
    (coupled_circleAverageCompose_smoothTameOn hD hT hγ hM hI travel)
    (fun _ _ => mem_univ _)
  have hfirst := smoothTameOn_comp_generic hp ht htcc
    (smoothTameOn_prodMk_generic hp ht hr havg)
    (coupled_circleProduct_smoothTameOn hD hT hγ hM hI) (fun _ _ => mem_univ _)
  have heven := smoothTameOn_postcompose_generic hp ht htc hfirst
    (circleModelEvenProjection hM) (circleModelEvenProjection_isTame hM)
  have hshift := smoothTameOn_comp_generic hp ht htcc
    (smoothTameOn_prodMk_generic hp ht he hv)
    (coupled_circleShiftedCompose_smoothTameOn hD hT hγ hM hI travel)
    (fun _ _ => mem_univ _)
  have hodd := smoothTameOn_postcompose_generic hp ht htc hshift
    (circleModelOddProjection hM) (circleModelOddProjection_isTame hM)
  have hsecond := smoothTameOn_comp_generic hp ht htcc
    (smoothTameOn_prodMk_generic hp ht hdr hodd)
    (coupled_circleProduct_smoothTameOn hD hT hγ hM hI) (fun _ _ => mem_univ _)
  have hsub := coupled_smoothTameOn_sub hp heven hsecond
  change SmoothTameOn p M.grading U
    (fun x : X =>
      circleModelEvenProjection hM
        (coupledCircleProduct hD hT hγ hM hI (r x)
          (coupledCircleAverageCompose hD hT hγ hM hI travel (e x)
            (coupledCircleDerivative hM (v x)))) -
        coupledCircleProduct hD hT hγ hM hI (coupledCircleDerivative hM (r x))
          (circleModelOddProjection hM
            (coupledCircleShiftedCompose hD hT hγ hM hI travel (e x) (v x)))) at hsub
  simpa only [Function.comp_def, coupledCircleErrorFormula] using hsub

end CircleFormula

private theorem coupled_circleError_ignore_right
    {E F Z : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
    {p : ℕ → Seminorm ℝ E} (q : ℕ → Seminorm ℝ F) {r : ℕ → Seminorm ℝ Z}
    {U : Set E} {f : E → Z} (hf : SmoothTameOn p r U f) :
    SmoothTameOn (pairGrading p q) r (U ×ˢ univ) (fun z : E × F => f z.1) := by
  let L := ContinuousLinearMap.fst ℝ E F
  have hb : ∀ n z, p n (L z) ≤ 1 * pairGrading p q n z := by
    intro n z
    change p n z.1 ≤ 1 * (p n z.1 + q n z.2)
    simpa only [one_mul] using le_add_of_nonneg_right (apply_nonneg (q n) z.2)
  have h := solve_smoothTameOn_precomp hf L (A := 1) le_rfl hb
  have hd : L ⁻¹' U = U ×ˢ univ := by
    ext z
    simp only [mem_preimage, L, ContinuousLinearMap.coe_fst', mem_prod, mem_univ, and_true]
  rw [hd] at h
  exact h

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

/-- N02 determines a genuine joint tower for its original independent
return error, on the same sector neighborhood and with the same data. -/
theorem coupled_returnError_smoothTameOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε) :
    SmoothTameOn
      (pairGrading (pairGrading (pairGrading (sectorGrading S) realGrading)
        (S.circle (3 / 4 : ℝ)).grading) (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ univ)
      (fun z : ((StateDirections S × ℝ) × CircleSpace S) × CircleSpace S =>
        R.error (liftSectorParameter S C z.1.1) z.1.2 z.2) := by
  let p := pairGrading (sectorGrading S) realGrading
  let c := (S.circle (3 / 4 : ℝ)).grading
  let a := pairGrading p c
  let b := pairGrading a c
  let U := sectorNeighborhood S base ε ε
  let W : Set (((StateDirections S × ℝ) × CircleSpace S) × CircleSpace S) :=
    (U ×ˢ univ) ×ˢ univ
  have hres : SmoothTameOn p c U (fun z => R.residual (liftSectorParameter S C z)) :=
    h2.2.2.2.2.2.2.2.2.2.2
  have hW : IsOpen W := (hres.choose.open_domain.prod isOpen_univ).prod isOpen_univ
  have hp : Monotone p := tamePairGrading_monotone
    (solve_sectorGrading_monotone S) weighted_realGrading_monotone
  have htp : WithSeminorms p := withSeminorms_pairGrading
    (solve_sectorGrading_withSeminorms S) weighted_realGrading_withSeminorms
  have hc : Monotone c := gradedSeminorm_monotone _ _
  have htc : WithSeminorms c := withSeminorms_graded _ _
  have hb : Monotone b := tamePairGrading_monotone (tamePairGrading_monotone hp hc) hc
  have htb : WithSeminorms b :=
    withSeminorms_pairGrading (withSeminorms_pairGrading htp htc) htc
  have he := coupled_circleError_ignore_right c (coupled_circleError_ignore_right c hres)
  have hfst : SmoothTameOn b a W
      (fun z : ((StateDirections S × ℝ) × CircleSpace S) × CircleSpace S => z.1) :=
    smoothTameOn_continuousLinear_on hW
      (ContinuousLinearMap.fst ℝ ((StateDirections S × ℝ) × CircleSpace S) (CircleSpace S))
      (scalar_pair_fst_isTame a c)
  have hr := solve_smoothTameOn_postcomp hfst
    (ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) (CircleSpace S))
    (r := c) (B := 1) zero_le_one (fun n z => by
      change c n z.2 ≤ 1 * (p n z.1 + c n z.2)
      simpa only [one_mul] using le_add_of_nonneg_left (apply_nonneg (p n) z.1))
  have hv : SmoothTameOn b c W
      (fun z : ((StateDirections S × ℝ) × CircleSpace S) × CircleSpace S => z.2) :=
    smoothTameOn_continuousLinear_on hW
      (ContinuousLinearMap.snd ℝ ((StateDirections S × ℝ) × CircleSpace S) (CircleSpace S))
      (scalar_pair_snd_isTame a c)
  let hM := hS.2.1 (3 / 4 : ℝ)
  have hγ : (0 : ℝ) < 3 / 4 := by norm_num
  have hI : HasInterpolation (S.circle (3 / 4 : ℝ)).grading :=
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
  have hformula := coupledCircleErrorFormula_smoothTameOn hD hT hγ hM hI C.travel hb htb
    he hr hv
  apply smoothTameOn_congr hformula
  intro z hz
  have hz' := liftSectorParameter_mem_stateNeighborhood (C := C) hz.1.1 le_rfl
  have hRef : referenceStateConditions D S C := h1.2.2.1
  have hs := hRef.liftSectorParameter_sector z.1.1
  have hdecode : (S.circle (3 / 4 : ℝ)).decode
      (R.residual (liftSectorParameter S C z.1.1)) =
      returnResidualField S C (liftSectorParameter S C z.1.1) := by
    funext m θ
    exact h2.2.1 _ hz' hs m θ
  apply hM.2.2.2.2.2.1
  funext m θ
  have hd := coupledCircleErrorFormula_decode hD hT hγ hM hI C.travel
    (R.residual (liftSectorParameter S C z.1.1)) z.1.2 z.2 m θ
  have heq := h2.2.2.2.2.1 (liftSectorParameter S C z.1.1) hz' hs z.1.2 z.2 m θ
  have hd' : (S.circle (3 / 4 : ℝ)).decode
      (coupledCircleErrorFormula hD hT hγ hM hI C.travel
        (R.residual (liftSectorParameter S C z.1.1)) z.1.2 z.2) m θ =
      circleChartError S C (liftSectorParameter S C z.1.1) z.1.2 z.2 m θ := by
    simpa only [hdecode, circleChartError] using hd
  exact hd'.trans heq.symm

end ContinuousFlexibility.Statements
