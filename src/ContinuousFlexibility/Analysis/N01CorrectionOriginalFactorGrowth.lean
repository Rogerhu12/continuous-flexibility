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

private theorem originalFactor_entry_zero_apply
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (p : PolarPoint) :
    originalCoefficientEntry D S C 0 z p = (originalCoefficients D S C z).a p := by
  simp only [originalCoefficientEntry, eq_self_iff_true, ite_true]

private theorem originalFactor_entry_one_apply
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (p : PolarPoint) :
    originalCoefficientEntry D S C 1 z p = (originalCoefficients D S C z).b p := by
  norm_num [originalCoefficientEntry]

section GenericFactors

variable {I E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

private theorem originalFactor_growth_of_projected
    {p : ℕ → Seminorm ℝ E} (q : ℕ → Seminorm ℝ F)
    {U : Set E} {V : I → Set PolarPoint}
    {f : I → E × PolarPoint → ℝ} {g : I → (E × F) × PolarPoint → ℝ}
    (K : ∀ i, SmoothDirections (U ×ˢ V i) (f i))
    (J : ∀ i, SmoothDirections ((U ×ˢ (univ : Set F)) ×ˢ V i) (g i))
    {base loss : ℕ}
    (hK : UniformWeightedJointGrowth p (fun _ => 1) K base loss)
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (heq : ∀ i z, z ∈ (U ×ˢ (univ : Set F)) ×ˢ V i →
      f i (z.1.1, z.2) = g i z) :
    UniformWeightedJointGrowth (pairGrading p q) (fun _ => 1) J base loss := by
  have hproject : UniformWeightedJointGrowth (pairGrading p q) (fun _ => 1)
      (fun i => (K i).fstParameter (F := F) hU (hV i)) base loss :=
    UniformWeightedJointGrowth.fstParameter
      (I := I) (E := E) (F := F) (P := PolarPoint) (G := ℝ)
      (p := p) (W := fun _ => 1) (U := U) (V := V) (f := f) (J := K)
      (base := base) (loss := loss) q (fun _ => zero_le_one) hK hU hV
  exact UniformWeightedJointGrowth.congr
    (I := I) (E := E × F) (P := PolarPoint) (F := ℝ)
    (p := pairGrading p q) (W := fun _ => 1)
    (U := U ×ˢ (univ : Set F)) (V := V)
    (f := fun i z => f i (z.1.1, z.2)) (g := g)
    (J := fun i => (K i).fstParameter (F := F) hU (hV i))
    (base := base) (loss := loss) hproject J heq

private theorem originalFactors_flat_growth_of_speed
    {p : ℕ → Seminorm ℝ E} (q : ℕ → Seminorm ℝ F)
    (hp : Monotone (pairGrading p q)) (hIp : HasInterpolation (pairGrading p q))
    {W : I → ℝ} (hW : ∀ i, 1 ≤ W i)
    {U : Set E} {V : I → Set PolarPoint}
    {a b qf : I → (E × F) × PolarPoint → ℝ} {v : I → E × PolarPoint → ℝ}
    (Ja : ∀ i, SmoothDirections ((U ×ˢ (univ : Set F)) ×ˢ V i) (a i))
    (Jb : ∀ i, SmoothDirections ((U ×ˢ (univ : Set F)) ×ˢ V i) (b i))
    (Jq : ∀ i, SmoothDirections ((U ×ˢ (univ : Set F)) ×ˢ V i) (qf i))
    {base loss : ℕ}
    (ha₀ : UniformWeightedJointGrowth (pairGrading p q) (fun _ => 1) Ja base loss)
    (hb₀ : UniformWeightedJointGrowth (pairGrading p q) (fun _ => 1) Jb base loss)
    (hdata : ∃ K : ∀ i, SmoothDirections (U ×ˢ V i) (v i),
      ∃ B L : ℕ, base ≤ B ∧ loss ≤ B ∧ UniformWeightedJointGrowth p W K B L)
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hc : ∀ i, Convex ℝ ((U ×ˢ (univ : Set F)) ×ˢ V i))
    (hrelation : ∀ i z, z ∈ (U ×ˢ (univ : Set F)) ×ˢ V i →
      b i z - a i z * v i (z.1.1, z.2) = qf i z) :
    HasFlatMixedTameGrowth (pairGrading p q) W (fun _ => 1) Ja ∧
      HasFlatMixedTameGrowth (pairGrading p q) W (fun _ => 1) Jb ∧
        HasFlatMixedTameGrowth (pairGrading p q) W (fun _ => 1) Jq := by
  have hW₀ (i : I) : 0 ≤ W i := zero_le_one.trans (hW i)
  have ha : UniformWeightedJointGrowth (pairGrading p q) W Ja base loss := ha₀.withWeight W
  have hb : UniformWeightedJointGrowth (pairGrading p q) W Jb base loss := hb₀.withWeight W
  obtain ⟨K, B, L, hB, _, hg⟩ := hdata
  let Jv : ∀ i, SmoothDirections ((U ×ˢ (univ : Set F)) ×ˢ V i)
      (fun z => v i (z.1.1, z.2)) :=
    fun i => (K i).fstParameter (F := F) hU (hV i)
  have hv : UniformWeightedJointGrowth (pairGrading p q) W Jv B L :=
    UniformWeightedJointGrowth.fstParameter
      (I := I) (E := E) (F := F) (P := PolarPoint) (G := ℝ)
      (p := p) (W := W) (U := U) (V := V) (f := v) (J := K)
      (base := B) (loss := L) q hW₀ hg hU hV
  let M : ℕ := max loss L
  have ha' : UniformWeightedJointGrowth (pairGrading p q) W Ja B M :=
    ha.mono hp hW₀ hB (le_max_left loss L)
  have hv' : UniformWeightedJointGrowth (pairGrading p q) W Jv B M :=
    hv.mono hp hW₀ le_rfl (le_max_right loss L)
  let Jprod : ∀ i, SmoothDirections ((U ×ˢ (univ : Set F)) ×ˢ V i)
      (fun z => a i z * v i (z.1.1, z.2)) :=
    fun i => (Ja i).mul (Jv i)
  obtain ⟨B', L', hB', _, hprod⟩ := ha'.mul hp hIp hW hv' Jprod
  let M' : ℕ := max loss L'
  let Jtemp : ∀ i, SmoothDirections ((U ×ˢ (univ : Set F)) ×ˢ V i)
      (fun z => b i z - a i z * v i (z.1.1, z.2)) :=
    fun i => (Jq i).congrOn (fun z hz => (hrelation i z hz).symm)
  have hb' : UniformWeightedJointGrowth (pairGrading p q) W Jb B' M' :=
    hb.mono hp hW₀ (hB.trans hB') (le_max_left loss L')
  have hp' : UniformWeightedJointGrowth (pairGrading p q) W Jprod B' M' :=
    hprod.mono hp hW₀ le_rfl (le_max_right loss L')
  have htemp : UniformWeightedJointGrowth (pairGrading p q) W Jtemp B' M' :=
    hb'.sub hp hW hp' Jtemp
  have hq : UniformWeightedJointGrowth (pairGrading p q) W Jq B' M' :=
    UniformWeightedJointGrowth.congr
      (I := I) (E := E × F) (P := PolarPoint) (F := ℝ)
      (p := pairGrading p q) (W := W) (U := U ×ˢ (univ : Set F)) (V := V)
      (f := fun i z => b i z - a i z * v i (z.1.1, z.2)) (g := qf)
      (J := Jtemp) (base := B') (loss := M') htemp Jq hrelation
  exact ⟨ha.hasFlatMixedTameGrowth hp hW hV hc,
    hb.hasFlatMixedTameGrowth hp hW hV hc,
    hq.hasFlatMixedTameGrowth hp hW hV hc⟩

end GenericFactors

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
  let U : Set (StateDirections S × ℝ) := sectorNeighborhood S base ε ε
  let V : ℕ → Set PolarPoint := fun m => Ioo (l m) (h m) ×ˢ univ
  let p₀ := pairGrading (sectorGrading S) realGrading
  let q := (S.circle (3 / 4 : ℝ)).grading
  let p := pairGrading p₀ q
  let W : ℕ → ℝ := fun m => radialE (D.cellIndex (j m))
  have hp : Monotone p := correctionParameterGrading_monotone S
  have hIp : HasInterpolation p := correctionParameterGrading_hasInterpolation hS
  have hW (m : ℕ) : 1 ≤ W m := one_le_radialE_of_nat _
  have hU : IsOpen U := sectorNeighborhood_isOpen S base ε ε
  have hV (m : ℕ) : IsOpen (V m) :=
    (isOpen_Ioo : IsOpen (Ioo (l m) (h m))).prod
      (isOpen_univ : IsOpen (univ : Set ℝ))
  have hc (m : ℕ) : Convex ℝ ((U ×ˢ (univ : Set (CircleSpace S))) ×ˢ V m) :=
    ((sectorNeighborhood_convex S base ε ε).prod convex_univ).prod
      ((convex_Ioo (l m) (h m)).prod convex_univ)
  let K : ∀ (i : Fin 3) (m : ℕ), SmoothDirections (U ×ˢ V m)
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        originalCoefficientEntry D S C i (liftSectorParameter S C x.1) x.2) :=
    fun i m => N01Properties.originalCoefficient_stripTower
      (D := D) (T := T) (S := S) (C := C)
      (base := base) (loss := loss) (ε := ε) hN hS hT j hcell l h hl hh i m
  have hK (i : Fin 3) : UniformWeightedJointGrowth p₀ (fun _ => 1) (K i) base loss :=
    N01Properties.originalCoefficient_strip_joint_growth
      (D := D) (T := T) (S := S) (C := C)
      (base := base) (loss := loss) (ε := ε) hN hS hT j hcell l h hl hh i
  have ha₀ : UniformWeightedJointGrowth p (fun _ => 1) Ja base loss :=
    originalFactor_growth_of_projected
      (I := ℕ) (E := StateDirections S × ℝ) (F := CircleSpace S)
      (p := p₀) (U := U) (V := V)
      (f := fun (_m : ℕ) (x : (StateDirections S × ℝ) × PolarPoint) =>
        originalCoefficientEntry D S C 0 (liftSectorParameter S C x.1) x.2)
      (g := fun (_m : ℕ) (x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) =>
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2)
      (base := base) (loss := loss) q (K 0) Ja (hK 0) hU hV
      (fun _ x _ => originalFactor_entry_zero_apply D S C
        (liftSectorParameter S C x.1.1) x.2)
  have hb₀ : UniformWeightedJointGrowth p (fun _ => 1) Jb base loss :=
    originalFactor_growth_of_projected
      (I := ℕ) (E := StateDirections S × ℝ) (F := CircleSpace S)
      (p := p₀) (U := U) (V := V)
      (f := fun (_m : ℕ) (x : (StateDirections S × ℝ) × PolarPoint) =>
        originalCoefficientEntry D S C 1 (liftSectorParameter S C x.1) x.2)
      (g := fun (_m : ℕ) (x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) =>
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2)
      (base := base) (loss := loss) q (K 1) Jb (hK 1) hU hV
      (fun _ x _ => originalFactor_entry_one_apply D S C
        (liftSectorParameter S C x.1.1) x.2)
  have hrelation (m : ℕ) (x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint)
      (hx : x ∈ (U ×ˢ (univ : Set (CircleSpace S))) ×ˢ V m) :
      (originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2 -
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2 *
          minusCharacteristicSpeed
            (originalCoefficients D S C (liftSectorParameter S C x.1.1)) x.2 =
      Real.sqrt ((originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2 ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2 *
          (originalCoefficients D S C (liftSectorParameter S C x.1.1)).c x.2) := by
    have hpoint : x.2 ∈ annularOpen D := hN.negativeComponent_subset_annularOpen m
      ⟨⟨(hl m).trans hx.2.1.1, hx.2.1.2.trans (hh m)⟩, hx.2.2⟩
    have hapos : 0 < (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2 :=
      N01Properties.originalRadialCoefficient_pos
        (D := D) (T := T) (S := S) (C := C)
        (base := base) (loss := loss) (ε := ε) hN
        (liftSectorParameter_mem_stateNeighborhood (C := C) hx.1.1 le_rfl)
        (hN.2.2.1.liftSectorParameter_sector x.1.1) hpoint
    simpa only [minusCharacteristicSpeed] using
      sqrt_discriminant_from_minus_speed
        (a := (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2)
        (b := (originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2)
        (c := (originalCoefficients D S C (liftSectorParameter S C x.1.1)).c x.2) hapos.ne'
  exact originalFactors_flat_growth_of_speed
    (I := ℕ) (E := StateDirections S × ℝ) (F := CircleSpace S)
    (p := p₀) (W := W) (U := U) (V := V)
    (a := fun (_m : ℕ) (x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) =>
      (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2)
    (b := fun (_m : ℕ) (x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) =>
      (originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2)
    (qf := fun (_m : ℕ) (x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) =>
      Real.sqrt ((originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2 ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2 *
          (originalCoefficients D S C (liftSectorParameter S C x.1.1)).c x.2))
    (v := fun (_m : ℕ) (x : (StateDirections S × ℝ) × PolarPoint) =>
      minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C x.1)) x.2)
    (base := base) (loss := loss) q hp hIp hW Ja Jb Jq ha₀ hb₀
    (N01Properties.exists_minusCharacteristicSpeed_strip_joint_growth
      (D := D) (T := T) (S := S) (C := C)
      (base := base) (loss := loss) (ε := ε) (lam := lam) (P := P)
      hN hS hT j hcell l h hl hh hlam hP hpositive)
    hU hV hc hrelation

end ContinuousFlexibility.Statements
