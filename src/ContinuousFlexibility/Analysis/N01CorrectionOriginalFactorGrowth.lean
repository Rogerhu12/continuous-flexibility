import ContinuousFlexibility.Analysis.N01TransportCharacteristicInterpolation
import ContinuousFlexibility.Analysis.FlatMixedDiagonalRealization

/-!
# The actual original factors in the correction polynomial

The radial and mixed coefficients have the original unweighted N01
growth. On the same quantitative strip, the already constructed minus
characteristic speed gives the square-root factor by the exact identity
`sqrt(discriminant) = b - a * minusSpeed`. Thus all three actual factors
have fixed-loss mixed growth on the full correction parameter space.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01CorrectionOriginalFactorGrowthStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped ContDiff Topology

private theorem sqrt_discriminant_from_minus_speed {a b c : ℝ} (ha : a ≠ 0) :
    b - a * (b / a - Real.sqrt (b ^ 2 - a * c) / a) = Real.sqrt (b ^ 2 - a * c) := by
  field_simp [ha] <;> ring

set_option diagnostics true in
theorem N01Properties.originalCorrectionFactors_flat_mixed_growth
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
    {lam P : ℝ} (hlam : 0 < lam) (hP : 0 ≤ P)
    (hpositive : ∀ z ∈ stateNeighborhood S C base ε, ∀ (m : ℕ) (p : PolarPoint),
      p.1 ∈ Ioo (l m) (h m) →
      let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
      d ≤ (originalCoefficients D S C z).a p ∧
      d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
    (Ja : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2))
    (Jb : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2))
    (Jq : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        Real.sqrt ((originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2 ^ 2 -
          (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2 *
            (originalCoefficients D S C (liftSectorParameter S C x.1.1)).c x.2))) :
    let p := pairGrading (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading
    let W := fun m => radialE (D.cellIndex (j m))
    HasFlatMixedTameGrowth p W (fun _ => 1) Ja ∧
      HasFlatMixedTameGrowth p W (fun _ => 1) Jb ∧
        HasFlatMixedTameGrowth p W (fun _ => 1) Jq := by
  let E₀ : Type := StateDirections S × ℝ
  let E : Type := (StateDirections S × ℝ) × CircleSpace S
  let p₀ : ℕ → Seminorm ℝ E₀ := pairGrading (sectorGrading S) realGrading
  let pc : ℕ → Seminorm ℝ (CircleSpace S) := (S.circle (3 / 4 : ℝ)).grading
  let p : ℕ → Seminorm ℝ E := pairGrading p₀ pc
  let U₀ : Set E₀ := sectorNeighborhood S base ε ε
  let U : Set E := U₀ ×ˢ univ
  let V : ℕ → Set PolarPoint := fun m => Ioo (l m) (h m) ×ˢ univ
  let W : ℕ → ℝ := fun m => radialE (D.cellIndex (j m))
  let fa : ℕ → E × PolarPoint → ℝ := fun _ x =>
    (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2
  let fb : ℕ → E × PolarPoint → ℝ := fun _ x =>
    (originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2
  let fq : ℕ → E × PolarPoint → ℝ := fun _ x =>
    Real.sqrt ((originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2 ^ 2 -
      (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2 *
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).c x.2)
  have hp : Monotone p := correctionParameterGrading_monotone S
  have hIp : HasInterpolation p := correctionParameterGrading_hasInterpolation hS
  have hW (m : ℕ) : 1 ≤ W m := one_le_radialE_of_nat (D.cellIndex (j m))
  have hW₀ (m : ℕ) : 0 ≤ W m := zero_le_one.trans (hW m)
  have hU₀ : IsOpen U₀ := sectorNeighborhood_isOpen S base ε ε
  have hV (m : ℕ) : IsOpen (V m) := isOpen_Ioo.prod isOpen_univ
  have hc (m : ℕ) : Convex ℝ (U ×ˢ V m) :=
    ((sectorNeighborhood_convex S base ε ε).prod convex_univ).prod
      ((convex_Ioo (l m) (h m)).prod convex_univ)
  let entry : Fin 3 → ℕ → E₀ × PolarPoint → ℝ := fun i _ x =>
    originalCoefficientEntry D S C i (liftSectorParameter S C x.1) x.2
  let K₀ : ∀ (i : Fin 3) (m : ℕ), SmoothDirections (U₀ ×ˢ V m) (entry i m) :=
    fun i m => hN.originalCoefficient_stripTower
      (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
      hS hT j hcell l h hl hh i m
  let K : ∀ (i : Fin 3) (m : ℕ), SmoothDirections (U ×ˢ V m)
      (fun x : E × PolarPoint => entry i m (x.1.1, x.2)) :=
    fun i m => SmoothDirections.fstParameter
      (E := E₀) (F := CircleSpace S) (P := PolarPoint) (G := ℝ)
      (U := U₀) (V := V m) (f := entry i m) (K₀ i m) hU₀ (hV m)
  have hK₀ (i : Fin 3) : UniformWeightedJointGrowth p₀ (fun _ => 1) (K₀ i) base loss :=
    hN.originalCoefficient_strip_joint_growth
      (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
      hS hT j hcell l h hl hh i
  have hK (i : Fin 3) : UniformWeightedJointGrowth p (fun _ => 1) (K i) base loss :=
    UniformWeightedJointGrowth.fstParameter
      (I := ℕ) (E := E₀) (F := CircleSpace S) (P := PolarPoint) (G := ℝ)
      (p := p₀) (W := fun _ => 1) (U := U₀) (V := V) (f := entry i)
      (J := K₀ i) (base := base) (loss := loss) pc (fun _ => zero_le_one)
      (hK₀ i) hU₀ hV
  have ha₀ : UniformWeightedJointGrowth p (fun _ => 1) Ja base loss := by
    apply UniformWeightedJointGrowth.congr
      (I := ℕ) (E := E) (P := PolarPoint) (F := ℝ)
      (p := p) (W := fun _ => 1) (U := U) (V := V)
      (f := fun m x => entry 0 m (x.1.1, x.2)) (g := fa)
      (J := K 0) (base := base) (loss := loss) (hK 0) Ja
    intro m x hx
    simp only [entry, fa, originalCoefficientEntry, eq_self_iff_true, ite_true]
  have hb₀ : UniformWeightedJointGrowth p (fun _ => 1) Jb base loss := by
    apply UniformWeightedJointGrowth.congr
      (I := ℕ) (E := E) (P := PolarPoint) (F := ℝ)
      (p := p) (W := fun _ => 1) (U := U) (V := V)
      (f := fun m x => entry 1 m (x.1.1, x.2)) (g := fb)
      (J := K 1) (base := base) (loss := loss) (hK 1) Jb
    intro m x hx
    have h10 : (1 : Fin 3) ≠ 0 := by decide
    simp only [entry, fb, originalCoefficientEntry, h10, eq_self_iff_true,
      ite_false, ite_true]
  have ha : UniformWeightedJointGrowth p W Ja base loss :=
    UniformWeightedJointGrowth.withWeight
      (I := ℕ) (E := E) (P := PolarPoint) (F := ℝ) (p := p)
      (U := U) (V := V) (f := fa) (J := Ja) (base := base) (loss := loss) ha₀ W
  have hb : UniformWeightedJointGrowth p W Jb base loss :=
    UniformWeightedJointGrowth.withWeight
      (I := ℕ) (E := E) (P := PolarPoint) (F := ℝ) (p := p)
      (U := U) (V := V) (f := fb) (J := Jb) (base := base) (loss := loss) hb₀ W
  let fv₀ : ℕ → E₀ × PolarPoint → ℝ := fun _ x =>
    minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C x.1)) x.2
  let fv : ℕ → E × PolarPoint → ℝ := fun m x => fv₀ m (x.1.1, x.2)
  let data : ∃ J : ∀ m, SmoothDirections (U₀ ×ˢ V m) (fv₀ m),
      ∃ B L : ℕ, base ≤ B ∧ loss ≤ B ∧ UniformWeightedJointGrowth p₀ W J B L :=
    hN.exists_minusCharacteristicSpeed_strip_joint_growth
      (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
      (lam := lam) (P := P) hS hT j hcell l h hl hh hlam hP hpositive
  let Jv₀ : ∀ m, SmoothDirections (U₀ ×ˢ V m) (fv₀ m) := data.choose
  let Jv : ∀ m, SmoothDirections (U ×ˢ V m) (fv m) :=
    fun m => SmoothDirections.fstParameter
      (E := E₀) (F := CircleSpace S) (P := PolarPoint) (G := ℝ)
      (U := U₀) (V := V m) (f := fv₀ m) (Jv₀ m) hU₀ (hV m)
  let B : ℕ := data.choose_spec.choose
  let L : ℕ := data.choose_spec.choose_spec.choose
  have hB : base ≤ B := data.choose_spec.choose_spec.choose_spec.1
  have hv₀ : UniformWeightedJointGrowth p₀ W Jv₀ B L :=
    data.choose_spec.choose_spec.choose_spec.2.2
  have hv : UniformWeightedJointGrowth p W Jv B L :=
    UniformWeightedJointGrowth.fstParameter
      (I := ℕ) (E := E₀) (F := CircleSpace S) (P := PolarPoint) (G := ℝ)
      (p := p₀) (W := W) (U := U₀) (V := V) (f := fv₀)
      (J := Jv₀) (base := B) (loss := L) pc hW₀ hv₀ hU₀ hV
  let M : ℕ := max loss L
  let fprod : ℕ → E × PolarPoint → ℝ := fun m x => fa m x * fv m x
  let Jprod : ∀ m, SmoothDirections (U ×ˢ V m) (fprod m) :=
    fun m => (Ja m).mul (Jv m)
  have haM : UniformWeightedJointGrowth p W Ja B M :=
    UniformWeightedJointGrowth.mono
      (I := ℕ) (E := E) (P := PolarPoint) (F := ℝ)
      (p := p) (W := W) (U := U) (V := V) (f := fa) (J := Ja)
      (base := base) (loss := loss) (B := B) (L := M)
      hp hW₀ ha hB (le_max_left loss L)
  have hvM : UniformWeightedJointGrowth p W Jv B M :=
    UniformWeightedJointGrowth.mono
      (I := ℕ) (E := E) (P := PolarPoint) (F := ℝ)
      (p := p) (W := W) (U := U) (V := V) (f := fv) (J := Jv)
      (base := B) (loss := L) (B := B) (L := M)
      hp hW₀ hv le_rfl (le_max_right loss L)
  let productData : ∃ B' L' : ℕ, B ≤ B' ∧ M ≤ B' ∧
      UniformWeightedJointGrowth p W Jprod B' L' :=
    UniformWeightedJointGrowth.mul
      (I := ℕ) (E := E) (P := PolarPoint)
      (p := p) (W := W) (U := U) (V := V) (f := fa) (g := fv)
      (J := Ja) (K := Jv) (base := B) (loss := M) hp hIp hW haM hvM Jprod
  let B' : ℕ := productData.choose
  let L' : ℕ := productData.choose_spec.choose
  have hB' : B ≤ B' := productData.choose_spec.choose_spec.1
  have hprod : UniformWeightedJointGrowth p W Jprod B' L' :=
    productData.choose_spec.choose_spec.2.2
  let M' : ℕ := max loss L'
  let subL : (ℝ × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ
  let ftemp : ℕ → E × PolarPoint → ℝ := fun m x => fb m x - fprod m x
  let Jtemp : ∀ m, SmoothDirections (U ×ˢ V m) (ftemp m) := fun m =>
    (smoothDirectionsPostContinuousLinear
      (smoothDirectionsProd (Jb m) (Jprod m)) subL).congrOn (by
        intro x hx
        simp only [subL, ftemp, _root_.sub_apply,
          ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'])
  have hbM' : UniformWeightedJointGrowth p W Jb B' M' :=
    UniformWeightedJointGrowth.mono
      (I := ℕ) (E := E) (P := PolarPoint) (F := ℝ)
      (p := p) (W := W) (U := U) (V := V) (f := fb) (J := Jb)
      (base := base) (loss := loss) (B := B') (L := M')
      hp hW₀ hb (hB.trans hB') (le_max_left loss L')
  have hprodM' : UniformWeightedJointGrowth p W Jprod B' M' :=
    UniformWeightedJointGrowth.mono
      (I := ℕ) (E := E) (P := PolarPoint) (F := ℝ)
      (p := p) (W := W) (U := U) (V := V) (f := fprod) (J := Jprod)
      (base := B') (loss := L') (B := B') (L := M')
      hp hW₀ hprod le_rfl (le_max_right loss L')
  have htemp : UniformWeightedJointGrowth p W Jtemp B' M' :=
    UniformWeightedJointGrowth.sub
      (I := ℕ) (E := E) (P := PolarPoint) (F := ℝ)
      (p := p) (W := W) (U := U) (V := V) (f := fb) (g := fprod)
      (J := Jb) (K := Jprod) (base := B') (loss := M')
      hp hW hbM' hprodM' Jtemp
  have hq : UniformWeightedJointGrowth p W Jq B' M' := by
    apply UniformWeightedJointGrowth.congr
      (I := ℕ) (E := E) (P := PolarPoint) (F := ℝ)
      (p := p) (W := W) (U := U) (V := V) (f := ftemp) (g := fq)
      (J := Jtemp) (base := B') (loss := M') htemp Jq
    intro m x hx
    have hpoint : x.2 ∈ annularOpen D := hN.negativeComponent_subset_annularOpen m
      ⟨⟨(hl m).trans hx.2.1.1, hx.2.1.2.trans (hh m)⟩, hx.2.2⟩
    have hapos : 0 < (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2 :=
      hN.originalRadialCoefficient_pos
        (liftSectorParameter_mem_stateNeighborhood hx.1.1 le_rfl)
        (hN.2.2.1.liftSectorParameter_sector x.1.1) hpoint
    simpa only [ftemp, fprod, fa, fb, fq, fv, fv₀, minusCharacteristicSpeed] using
      (sqrt_discriminant_from_minus_speed
        (a := (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2)
        (b := (originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2)
        (c := (originalCoefficients D S C (liftSectorParameter S C x.1.1)).c x.2)
        hapos.ne')
  exact ⟨UniformWeightedJointGrowth.hasFlatMixedTameGrowth
      (I := ℕ) (E := E) (p := p) (W := W) (U := U) (V := V) (f := fa)
      (J := Ja) (B := base) (L := loss) hp hW ha hV hc,
    UniformWeightedJointGrowth.hasFlatMixedTameGrowth
      (I := ℕ) (E := E) (p := p) (W := W) (U := U) (V := V) (f := fb)
      (J := Jb) (B := base) (L := loss) hp hW hb hV hc,
    UniformWeightedJointGrowth.hasFlatMixedTameGrowth
      (I := ℕ) (E := E) (p := p) (W := W) (U := U) (V := V) (f := fq)
      (J := Jq) (B := B') (L := M') hp hW hq hV hc⟩

end ContinuousFlexibility.Statements
