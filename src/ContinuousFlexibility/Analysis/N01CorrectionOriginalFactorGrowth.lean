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

theorem sqrt_discriminant_from_minus_speed {a b c : ℝ} (ha : a ≠ 0) :
    b - a * (b / a - Real.sqrt (b ^ 2 - a * c) / a) = Real.sqrt (b ^ 2 - a * c) := by
  field_simp [ha] <;> ring

private theorem fstParameter_jointGrowth_congr
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    {p : ℕ → Seminorm ℝ E} (q : ℕ → Seminorm ℝ F)
    {W : ℕ → ℝ}
    {U : Set E} {V : ℕ → Set PolarPoint}
    {f g : ℕ → E × PolarPoint → ℝ}
    {J : ∀ m, SmoothDirections (U ×ˢ V m) (f m)} {base loss : ℕ}
    (hJ : UniformWeightedJointGrowth p (fun _ => 1) J base loss)
    (hU : IsOpen U) (hV : ∀ m, IsOpen (V m))
    (K : ∀ m, SmoothDirections ((U ×ˢ (univ : Set F)) ×ˢ V m)
      (fun x : (E × F) × PolarPoint => g m (x.1.1, x.2)))
    (heq : ∀ m x, x ∈ U ×ˢ V m → f m x = g m x) :
    UniformWeightedJointGrowth (pairGrading p q) W K base loss := by
  let Jlift : ∀ m, SmoothDirections ((U ×ˢ (univ : Set F)) ×ˢ V m)
      (fun x : (E × F) × PolarPoint => f m (x.1.1, x.2)) :=
    fun m => SmoothDirections.fstParameter
      (E := E) (F := F) (P := PolarPoint) (G := ℝ)
      (U := U) (V := V m) (f := f m) (J m) hU (hV m)
  have hlift : UniformWeightedJointGrowth (pairGrading p q) (fun _ => 1) Jlift base loss :=
    UniformWeightedJointGrowth.fstParameter
      (I := ℕ) (E := E) (F := F) (P := PolarPoint) (G := ℝ)
      (p := p) (W := fun _ => 1) (U := U) (V := V) (f := f) (J := J)
      (base := base) (loss := loss) q (fun _ => zero_le_one) hJ hU hV
  have hcongr : UniformWeightedJointGrowth (pairGrading p q) (fun _ => 1) K base loss :=
    UniformWeightedJointGrowth.congr
      (I := ℕ) (E := E × F) (P := PolarPoint) (F := ℝ)
      (p := pairGrading p q) (W := fun _ => 1) (U := U ×ˢ (univ : Set F)) (V := V)
      (f := fun m x => f m (x.1.1, x.2))
      (g := fun m x => g m (x.1.1, x.2)) (J := Jlift)
      (base := base) (loss := loss) hlift K
      (fun m x hx => heq m (x.1.1, x.2) ⟨hx.1.1, hx.2⟩)
  exact UniformWeightedJointGrowth.withWeight
    (I := ℕ) (E := E × F) (P := PolarPoint) (F := ℝ)
    (p := pairGrading p q) (U := U ×ˢ (univ : Set F)) (V := V)
    (f := fun m x => g m (x.1.1, x.2)) (J := K)
    (base := base) (loss := loss) hcongr W

theorem scalar_sub_mul_jointGrowth
    {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hIp : HasInterpolation p)
    {W : ℕ → ℝ} (hW : ∀ m, 1 ≤ W m)
    {U : Set E} {V : ℕ → Set PolarPoint}
    {fa fb fv fq : ℕ → E × PolarPoint → ℝ}
    (Ja : ∀ m, SmoothDirections (U ×ˢ V m) (fa m))
    (Jb : ∀ m, SmoothDirections (U ×ˢ V m) (fb m))
    (Jv : ∀ m, SmoothDirections (U ×ˢ V m) (fv m))
    (Jq : ∀ m, SmoothDirections (U ×ˢ V m) (fq m))
    {base loss B L : ℕ} (hB : base ≤ B)
    (ha : UniformWeightedJointGrowth p W Ja base loss)
    (hb : UniformWeightedJointGrowth p W Jb base loss)
    (hv : UniformWeightedJointGrowth p W Jv B L)
    (heq : ∀ m x, x ∈ U ×ˢ V m → fb m x - fa m x * fv m x = fq m x) :
    ∃ B' L' : ℕ, B ≤ B' ∧ max loss L ≤ B' ∧
      UniformWeightedJointGrowth p W Jq B' (max loss L') := by
  have hW₀ (m : ℕ) : 0 ≤ W m := zero_le_one.trans (hW m)
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
  have hq : UniformWeightedJointGrowth p W Jq B' M' :=
    UniformWeightedJointGrowth.congr
      (I := ℕ) (E := E) (P := PolarPoint) (F := ℝ)
      (p := p) (W := W) (U := U) (V := V) (f := ftemp) (g := fq)
      (J := Jtemp) (base := B') (loss := M') htemp Jq (fun m x hx => heq m x hx)
  exact ⟨B', L', hB', productData.choose_spec.choose_spec.2.1, hq⟩

private theorem originalFactors_flat_mixed_growth_of_source_data
    {E₀ F : Type*}
    [TopologicalSpace E₀] [AddCommGroup E₀] [Module ℝ E₀]
    [IsTopologicalAddGroup E₀] [ContinuousSMul ℝ E₀]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    {p₀ : ℕ → Seminorm ℝ E₀} (pc : ℕ → Seminorm ℝ F)
    (hp : Monotone (pairGrading p₀ pc)) (hIp : HasInterpolation (pairGrading p₀ pc))
    {W : ℕ → ℝ} (hW : ∀ m, 1 ≤ W m)
    {U₀ : Set E₀} {V : ℕ → Set PolarPoint}
    (hU₀ : IsOpen U₀) (hV : ∀ m, IsOpen (V m))
    (hc : ∀ m, Convex ℝ ((U₀ ×ˢ (univ : Set F)) ×ˢ V m))
    {entry : Fin 3 → ℕ → E₀ × PolarPoint → ℝ}
    (K₀ : ∀ (i : Fin 3) (m : ℕ), SmoothDirections (U₀ ×ˢ V m) (entry i m))
    {base loss : ℕ}
    (hK₀ : ∀ i, UniformWeightedJointGrowth p₀ (fun _ => 1) (K₀ i) base loss)
    {fa₀ fb₀ fv₀ fq₀ : ℕ → E₀ × PolarPoint → ℝ}
    (Ja : ∀ m, SmoothDirections ((U₀ ×ˢ (univ : Set F)) ×ˢ V m)
      (fun x : (E₀ × F) × PolarPoint => fa₀ m (x.1.1, x.2)))
    (Jb : ∀ m, SmoothDirections ((U₀ ×ˢ (univ : Set F)) ×ˢ V m)
      (fun x : (E₀ × F) × PolarPoint => fb₀ m (x.1.1, x.2)))
    (Jq : ∀ m, SmoothDirections ((U₀ ×ˢ (univ : Set F)) ×ˢ V m)
      (fun x : (E₀ × F) × PolarPoint => fq₀ m (x.1.1, x.2)))
    (heqa : ∀ m x, x ∈ U₀ ×ˢ V m → entry 0 m x = fa₀ m x)
    (heqb : ∀ m x, x ∈ U₀ ×ˢ V m → entry 1 m x = fb₀ m x)
    (data : ∃ J : ∀ m, SmoothDirections (U₀ ×ˢ V m) (fv₀ m),
      ∃ B L : ℕ, base ≤ B ∧ loss ≤ B ∧ UniformWeightedJointGrowth p₀ W J B L)
    (heq₀ : ∀ m x, x ∈ U₀ ×ˢ V m →
      fb₀ m x - fa₀ m x * fv₀ m x = fq₀ m x) :
    HasFlatMixedTameGrowth (pairGrading p₀ pc) W (fun _ => 1) Ja ∧
      HasFlatMixedTameGrowth (pairGrading p₀ pc) W (fun _ => 1) Jb ∧
        HasFlatMixedTameGrowth (pairGrading p₀ pc) W (fun _ => 1) Jq := by
  let E : Type _ := E₀ × F
  let p : ℕ → Seminorm ℝ E := pairGrading p₀ pc
  let U : Set E := U₀ ×ˢ univ
  let fa : ℕ → E × PolarPoint → ℝ := fun m x => fa₀ m (x.1.1, x.2)
  let fb : ℕ → E × PolarPoint → ℝ := fun m x => fb₀ m (x.1.1, x.2)
  let fq : ℕ → E × PolarPoint → ℝ := fun m x => fq₀ m (x.1.1, x.2)
  have hW₀ (m : ℕ) : 0 ≤ W m := zero_le_one.trans (hW m)
  have ha : UniformWeightedJointGrowth
      (I := ℕ) (E := E) (P := PolarPoint) (F := ℝ)
      (U := U) (V := V) (f := fa) p W Ja base loss :=
    fstParameter_jointGrowth_congr
      (E := E₀) (F := F) (p := p₀) (W := W)
      (U := U₀) (V := V) (f := entry 0) (g := fa₀) (J := K₀ 0)
      (base := base) (loss := loss) pc (hK₀ 0) hU₀ hV Ja heqa
  have hb : UniformWeightedJointGrowth
      (I := ℕ) (E := E) (P := PolarPoint) (F := ℝ)
      (U := U) (V := V) (f := fb) p W Jb base loss :=
    fstParameter_jointGrowth_congr
      (E := E₀) (F := F) (p := p₀) (W := W)
      (U := U₀) (V := V) (f := entry 1) (g := fb₀) (J := K₀ 1)
      (base := base) (loss := loss) pc (hK₀ 1) hU₀ hV Jb heqb
  let fv : ℕ → E × PolarPoint → ℝ := fun m x => fv₀ m (x.1.1, x.2)
  let Jv₀ : ∀ m, SmoothDirections (U₀ ×ˢ V m) (fv₀ m) := data.choose
  let Jv : ∀ m, SmoothDirections (U ×ˢ V m) (fv m) :=
    fun m => SmoothDirections.fstParameter
      (E := E₀) (F := F) (P := PolarPoint) (G := ℝ)
      (U := U₀) (V := V m) (f := fv₀ m) (Jv₀ m) hU₀ (hV m)
  let B : ℕ := data.choose_spec.choose
  let L : ℕ := data.choose_spec.choose_spec.choose
  have hB : base ≤ B := data.choose_spec.choose_spec.choose_spec.1
  have hv₀ : UniformWeightedJointGrowth p₀ W Jv₀ B L :=
    data.choose_spec.choose_spec.choose_spec.2.2
  have hv : UniformWeightedJointGrowth p W Jv B L :=
    UniformWeightedJointGrowth.fstParameter
      (I := ℕ) (E := E₀) (F := F) (P := PolarPoint) (G := ℝ)
      (p := p₀) (W := W) (U := U₀) (V := V) (f := fv₀)
      (J := Jv₀) (base := B) (loss := L) pc hW₀ hv₀ hU₀ hV
  have heq : ∀ m (x : E × PolarPoint), x ∈ U ×ˢ V m →
      fb m x - fa m x * fv m x = fq m x :=
    fun m x hx => heq₀ m (x.1.1, x.2) ⟨hx.1.1, hx.2⟩
  let scalarData : ∃ B' L' : ℕ, B ≤ B' ∧ max loss L ≤ B' ∧
      UniformWeightedJointGrowth p W Jq B' (max loss L') :=
    scalar_sub_mul_jointGrowth
      (E := E) (p := p) (W := W) (U := U) (V := V)
      (fa := fa) (fb := fb) (fv := fv) (fq := fq)
      (base := base) (loss := loss) (B := B) (L := L)
      hp hIp hW Ja Jb Jv Jq hB ha hb hv heq
  obtain ⟨B', L', _, _, hq⟩ := scalarData
  let M' : ℕ := max loss L'
  exact ⟨UniformWeightedJointGrowth.hasFlatMixedTameGrowth
      (I := ℕ) (E := E) (p := p) (W := W) (U := U) (V := V) (f := fa)
      (J := Ja) (B := base) (L := loss) hp hW ha hV hc,
    UniformWeightedJointGrowth.hasFlatMixedTameGrowth
      (I := ℕ) (E := E) (p := p) (W := W) (U := U) (V := V) (f := fb)
      (J := Jb) (B := base) (L := loss) hp hW hb hV hc,
    UniformWeightedJointGrowth.hasFlatMixedTameGrowth
      (I := ℕ) (E := E) (p := p) (W := W) (U := U) (V := V) (f := fq)
      (J := Jq) (B := B') (L := M') hp hW hq hV hc⟩

private def n01CorrectionOriginalFactorGrowthCircleSMul (S : PhysicalSpacesData) :
    SMul ℝ (CircleSpace S) :=
  Submodule.smul (R := ℝ) (S := ℝ)
    (Analysis.compatibleSubmodule
      (fun n => (S.circle (3 / 4 : ℝ)).level n) (S.circle (3 / 4 : ℝ)).bond)

private theorem n01CorrectionOriginalFactorGrowthCircleSMul_eq_inferInstance
    (S : PhysicalSpacesData) :
    n01CorrectionOriginalFactorGrowthCircleSMul S =
      (inferInstance : SMul ℝ (CircleSpace S)) := rfl

attribute [local instance] n01CorrectionOriginalFactorGrowthCircleSMul

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

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
  have hp : Monotone p := correctionParameterGrading_monotone S
  have hIp : HasInterpolation p := correctionParameterGrading_hasInterpolation hS
  have hW (m : ℕ) : 1 ≤ W m := one_le_radialE_of_nat (D.cellIndex (j m))
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
  have hK₀ (i : Fin 3) : UniformWeightedJointGrowth
      (I := ℕ) (E := E₀) (P := PolarPoint) (F := ℝ)
      (U := U₀) (V := V) (f := entry i)
      p₀ (fun _ : ℕ => (1 : ℝ)) (K₀ i) base loss :=
    hN.originalCoefficient_strip_joint_growth
      (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
      hS hT j hcell l h hl hh i
  let fa₀ : ℕ → E₀ × PolarPoint → ℝ := fun _ x =>
    (originalCoefficients D S C (liftSectorParameter S C x.1)).a x.2
  let fb₀ : ℕ → E₀ × PolarPoint → ℝ := fun _ x =>
    (originalCoefficients D S C (liftSectorParameter S C x.1)).b x.2
  have heqa : ∀ m (x : E₀ × PolarPoint), x ∈ U₀ ×ˢ V m →
      entry 0 m x = fa₀ m x := by
    intro m x hx
    simp only [entry, fa₀, originalCoefficientEntry, eq_self_iff_true, ite_true]
  have heqb : ∀ m (x : E₀ × PolarPoint), x ∈ U₀ ×ˢ V m →
      entry 1 m x = fb₀ m x := by
    intro m x hx
    have h10 : (1 : Fin 3) ≠ 0 := by decide
    simp only [entry, fb₀, originalCoefficientEntry, h10, eq_self_iff_true,
      ite_false, ite_true]
  let fv₀ : ℕ → E₀ × PolarPoint → ℝ := fun _ x =>
    minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C x.1)) x.2
  let fq₀ : ℕ → E₀ × PolarPoint → ℝ := fun _ x =>
    Real.sqrt ((originalCoefficients D S C (liftSectorParameter S C x.1)).b x.2 ^ 2 -
      (originalCoefficients D S C (liftSectorParameter S C x.1)).a x.2 *
        (originalCoefficients D S C (liftSectorParameter S C x.1)).c x.2)
  let data : ∃ J : ∀ m, SmoothDirections (U₀ ×ˢ V m) (fv₀ m),
      ∃ B L : ℕ, base ≤ B ∧ loss ≤ B ∧ UniformWeightedJointGrowth p₀ W J B L :=
    hN.exists_minusCharacteristicSpeed_strip_joint_growth
      (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
      (lam := lam) (P := P) hS hT j hcell l h hl hh hlam hP hpositive
  have heq₀ : ∀ m (x : E₀ × PolarPoint), x ∈ U₀ ×ˢ V m →
      fb₀ m x - fa₀ m x * fv₀ m x = fq₀ m x := by
    intro m x hx
    have hpoint : x.2 ∈ annularOpen D := hN.negativeComponent_subset_annularOpen m
      ⟨⟨(hl m).trans hx.2.1.1, hx.2.1.2.trans (hh m)⟩, hx.2.2⟩
    have hapos : 0 < (originalCoefficients D S C (liftSectorParameter S C x.1)).a x.2 :=
      hN.originalRadialCoefficient_pos
        (liftSectorParameter_mem_stateNeighborhood hx.1 le_rfl)
        (hN.2.2.1.liftSectorParameter_sector x.1) hpoint
    simpa only [fa₀, fb₀, fq₀, fv₀, minusCharacteristicSpeed] using
      (sqrt_discriminant_from_minus_speed
        (a := (originalCoefficients D S C (liftSectorParameter S C x.1)).a x.2)
        (b := (originalCoefficients D S C (liftSectorParameter S C x.1)).b x.2)
        (c := (originalCoefficients D S C (liftSectorParameter S C x.1)).c x.2)
        hapos.ne')
  exact originalFactors_flat_mixed_growth_of_source_data
    (E₀ := E₀) (F := CircleSpace S) (p₀ := p₀) (W := W)
    (U₀ := U₀) (V := V) (entry := entry) (base := base) (loss := loss)
    (fa₀ := fa₀) (fb₀ := fb₀) (fv₀ := fv₀) (fq₀ := fq₀)
    pc hp hIp hW hU₀ hV hc K₀ hK₀ Ja Jb Jq heqa heqb data heq₀

end ContinuousFlexibility.Statements
