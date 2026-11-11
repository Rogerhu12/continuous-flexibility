import ContinuousFlexibility.Analysis.N07bSourceBoundSummation
import ContinuousFlexibility.Analysis.SolveStateSpaces
import ContinuousFlexibility.Scalar.WeightedPointwise

/-!
# A uniform actual source lift from a geometric coefficient estimate

The geometric estimate below is a separately named, source-independent
condition. This module does not claim that frozen `N04PartA` or `N04Properties`
provides it. Under that condition, the actual finite source expansion,
material energy, atlas summation, and prescribed weak-jet model prove the
uniform source-lift bound needed in the Banach bridge.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

/-- The exact geometric condition used by the analytic source estimate.
The constants are chosen before the state, piece, path, and source. This
condition is not a field of the frozen canonical geometry statement. -/
def N07bSourceCoefficientBound (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base : ℕ) (ε : ℝ) (b loss : ℕ) : Prop :=
  ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m x, x ∈ physicalPieceOpen S K m →
        ∀ j : Fin (b + 1), ∀ i : n07bAngularChainIndex j.val,
          n07bSourceGeometricWeight T K z m x *
            n07bAngularChainCoefficient T K z m (3 / 4 : ℝ) j.val i x ^ 2 ≤
              B * T.E0 x.1 ^ A *
                (1 + stateGrading S (b + loss) (z.1 - C.referenceState) + |z.2|) ^ 2

/-- For positive actual heights, the coefficient multiplier is precisely
the physical Jacobian weight with height ratio exponent `3/2`. -/
theorem n07bSourceGeometricWeight_eq
    {S : PhysicalSpacesData} (T : MaterialData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (x : PolarPoint)
    (hx : 0 < T.H x.1) (hm : 0 < T.H (T.sample (K.cell m))) :
    n07bSourceGeometricWeight T K z m x =
      T.ell x.1 * |planeJacobian (K.chart z m) x| *
        (T.H x.1 / T.H (T.sample (K.cell m))) ^ (3 / 2 : ℝ) := by
  have hfactor : n07bCanonicalSourceFactor T K (3 / 4 : ℝ) 0 m =
      T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) := by
    simp only [n07bCanonicalSourceFactor, neg_zero, Real.rpow_zero, one_mul]
  have hp : (T.H x.1 ^ (3 / 4 : ℝ) / T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ)) ^ 2 =
      (T.H x.1 / T.H (T.sample (K.cell m))) ^ (3 / 2 : ℝ) := by
    rw [← Real.div_rpow hx.le hm.le, ← Real.rpow_natCast,
      ← Real.rpow_mul (div_nonneg hx.le hm.le)]
    norm_num
  calc
    _ = T.ell x.1 * |planeJacobian (K.chart z m) x| *
        (T.H x.1 ^ (3 / 4 : ℝ) / T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ)) ^ 2 := by
      change T.ell x.1 * ((n07bCanonicalSourceFactor T K (3 / 4 : ℝ) 0 m)⁻¹ ^ 2 *
        |planeJacobian (K.chart z m) x| * (T.H x.1 ^ (3 / 4 : ℝ)) ^ 2) = _
      rw [hfactor]
      simp only [div_eq_mul_inv, mul_pow]
      ring
    _ = _ := by rw [hp]

/-- Scalar square-root arithmetic is checked before a concrete weak-jet
space is supplied, so the norm comparison does not unfold that space. -/
private theorem norm_le_sqrt_mul_of_square_bound
    {E : Type*} [SeminormedAddCommGroup E] {u : E} {A Q p q : ℝ}
    (hA : 0 ≤ A) (hQ : 0 ≤ Q) (hp : 0 ≤ p) (hpq : p ≤ q)
    (h : ‖u‖ ^ 2 ≤ A * Q ^ 2 * p ^ 2) :
    ‖u‖ ≤ Real.sqrt A * Q * q := by
  have hq : 0 ≤ q := hp.trans hpq
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hQ) hq)).mp
  calc
    ‖u‖ ^ 2 ≤ A * Q ^ 2 * p ^ 2 := h
    _ ≤ A * Q ^ 2 * q ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp hpq 2) (mul_nonneg hA (sq_nonneg _))
    _ = (Real.sqrt A * Q * q) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hA]

private theorem sourceCoefficient_uniform_M_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    {base : ℕ} {ε : ℝ} (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (b loss : ℕ)
    (hgeom : N07bSourceCoefficientBound T S C K base ε b loss) :
    ∃ A₀ : ℝ, 0 ≤ A₀ ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        ∀ m x, x ∈ physicalPieceOpen S K m →
          ∀ j : Fin (b + 1), ∀ i : n07bAngularChainIndex j.val,
            n07bSourceGeometricWeight T K z m x *
                n07bAngularChainCoefficient T K z m (3 / 4 : ℝ) j.val i x ^ 2 ≤
              (A₀ * (1 + stateGrading S (b + loss) (z.1 - C.referenceState) + |z.2|) ^ 2) *
                T.M x.1 ^ 2 := by
  obtain ⟨B, A, hB, _, hcoeff⟩ := hgeom
  obtain ⟨CA, hCA, hEA⟩ := hT.2.2.2.2.2.2.2.2.2.2.2.1 A
  refine ⟨B * CA, mul_nonneg hB hCA.le, ?_⟩
  intro z hz hs m x hx j i
  have hxcore : x.1 ∈ Ioo D.a D.b := (hK.2.2.2.1 m).2.2 hx.1
  have hM : 1 ≤ T.M x.1 := (hT.2.1 x.1 hxcore).2.2.2
  have hMM : T.M x.1 ≤ T.M x.1 ^ 2 := by nlinarith
  have hEM : T.E0 x.1 ^ A ≤ CA * T.M x.1 ^ 2 :=
    (hEA x.1 hxcore).trans (mul_le_mul_of_nonneg_left hMM hCA.le)
  calc
    _ ≤ B * T.E0 x.1 ^ A *
        (1 + stateGrading S (b + loss) (z.1 - C.referenceState) + |z.2|) ^ 2 :=
      hcoeff z hz hs m x hx j i
    _ ≤ B * (CA * T.M x.1 ^ 2) *
        (1 + stateGrading S (b + loss) (z.1 - C.referenceState) + |z.2|) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEM hB) (sq_nonneg _)
    _ = _ := by ring

set_option diagnostics true in
set_option backward.isDefEq.respectTransparency true in
private theorem sourceLift_uniform_square_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hV : IsVolumeModel T S K V)
    (hK : N04PartA D S C K base ε) (b loss : ℕ)
    (hgeom : N07bSourceCoefficientBound T S C K base ε b loss) :
    ∃ A₀ : ℝ, 0 ≤ A₀ ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ f : S.Source,
        ∃ F : V.level (3 / 4 : ℝ) 0 b,
          ‖F‖ ^ 2 ≤ A₀ * (1 + stateGrading S (b + loss) (z.1 - C.referenceState) + |z.2|) ^ 2 *
            physicalNorm T (3 / 4 : ℝ) (b + 1) ((S.height (3 / 4 : ℝ)).decode f.val) ^ 2 ∧
          ∀ m, (V.forget (3 / 4 : ℝ) 0 b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
            canonicalSource S K z m ((S.height (3 / 4 : ℝ)).decode f.val) := by
  obtain ⟨A, hA, hcoeff⟩ := sourceCoefficient_uniform_M_bound
    (D := D) (T := T) (S := S) (C := C) (K := K) (base := base) (ε := ε)
    hT hK b loss hgeom
  refine ⟨A * n07bSourcePathConstant b,
    mul_nonneg hA (n07bSourcePathConstant_nonneg b), ?_⟩
  intro z hz hs f
  let Q : ℝ := 1 + stateGrading S (b + loss) (z.1 - C.referenceState) + |z.2|
  have hAQ : 0 ≤ A * Q ^ 2 := mul_nonneg hA (sq_nonneg Q)
  obtain ⟨F, hF, hforget⟩ := n07b_exists_sourceLift_of_M_bound
    (D := D) (T := T) (S := S) (C := C) (K := K) (V := V)
    (base := base) (ε := ε) (z := z) (A := A * Q ^ 2)
    hD hT hS hV hK hz hs f b hAQ (hcoeff z hz hs)
  refine ⟨F, hF.trans_eq ?_, hforget⟩
  change (A * Q ^ 2) * n07bSourcePathConstant b *
      physicalNorm T (3 / 4 : ℝ) (b + 1) ((S.height (3 / 4 : ℝ)).decode f.val) ^ 2 =
    (A * n07bSourcePathConstant b) * Q ^ 2 *
      physicalNorm T (3 / 4 : ℝ) (b + 1) ((S.height (3 / 4 : ℝ)).decode f.val) ^ 2
  ring

private theorem source_physicalNorm_le_grading
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) {r s : ℕ} (hrs : r ≤ s) (f : S.Source) :
    physicalNorm T (3 / 4 : ℝ) r ((S.height (3 / 4 : ℝ)).decode f.val) ≤ S.sourceGrading s f := by
  rw [PhysicalSpacesData.sourceGrading, Seminorm.comp_apply, Submodule.subtype_apply]
  apply (physicalNorm_decode_le_grading (hS.1 (3 / 4 : ℝ)) f.val r).trans
  exact gradedSeminorm_monotone (fun n => (S.height (3 / 4 : ℝ)).level n)
    (S.height (3 / 4 : ℝ)).bond hrs f.val

/-- Existence and scalar norm arithmetic are packaged on abstract types.
The relation carrying the actual decoded source is preserved verbatim. -/
private theorem uniformLift_of_square_bound
    {Z X E : Type*} [SeminormedAddCommGroup E]
    (U : Set Z) (sector : Z → Prop) (Q Q' : Z → ℝ) (p q : X → ℝ)
    (spec : Z → X → E → Prop) {A : ℝ} (hA : 0 ≤ A)
    (hQ : ∀ z, 0 ≤ Q z) (hQQ : ∀ z, Q z ≤ Q' z)
    (hp : ∀ x, 0 ≤ p x) (hpq : ∀ x, p x ≤ q x)
    (hlift : ∀ z ∈ U, sector z → ∀ x, ∃ u : E,
      ‖u‖ ^ 2 ≤ A * Q z ^ 2 * p x ^ 2 ∧ spec z x u) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ z ∈ U, sector z → ∀ x, ∃ u : E,
      ‖u‖ ≤ C₀ * Q' z * q x ∧ spec z x u := by
  have hC₀ : 0 < Real.sqrt A + 1 := by linarith [Real.sqrt_nonneg A]
  refine ⟨Real.sqrt A + 1, hC₀, ?_⟩
  intro z hz hs x
  obtain ⟨u, hu, hspec⟩ := hlift z hz hs x
  have hn := norm_le_sqrt_mul_of_square_bound hA (hQ z) (hp x) (hpq x) hu
  have hq : 0 ≤ q x := (hp x).trans (hpq x)
  refine ⟨u, hn.trans ?_, hspec⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (by linarith : Real.sqrt A ≤ Real.sqrt A + 1) (hQQ z) (hQ z) hC₀.le) hq

set_option diagnostics true in
set_option backward.isDefEq.respectTransparency true in
/-- The geometric coefficient estimate implies the actual uniform source
bound with source order `b+1` and final common index `b+loss+1`.
Only the explicitly displayed geometric hypothesis remains conditional. -/
theorem n07b_sourceLift_uniform_bound_of_coefficients
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hV : IsVolumeModel T S K V)
    (hK : N04PartA D S C K base ε) (b loss : ℕ)
    (hgeom : N07bSourceCoefficientBound T S C K base ε b loss) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ f : S.Source,
        ∃ F : V.level (3 / 4 : ℝ) 0 b,
          ‖F‖ ≤ C₀ * (1 + stateGrading S (b + loss + 1) (z.1 - C.referenceState) + |z.2|) *
            S.sourceGrading (b + loss + 1) f ∧
          ∀ m, (V.forget (3 / 4 : ℝ) 0 b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
            canonicalSource S K z m ((S.height (3 / 4 : ℝ)).decode f.val) := by
  obtain ⟨A, hA, hlift⟩ := sourceLift_uniform_square_bound
    (D := D) (T := T) (S := S) (C := C) (K := K) (V := V) (base := base) (ε := ε)
    hD hT hS hV hK b loss hgeom
  refine uniformLift_of_square_bound (Z := AnnularState S × ℝ) (X := S.Source)
    (E := V.level (3 / 4 : ℝ) 0 b) (stateNeighborhood S C base ε) (fun z => stateSector S z.1)
    (fun z => 1 + stateGrading S (b + loss) (z.1 - C.referenceState) + |z.2|)
    (fun z => 1 + stateGrading S (b + loss + 1) (z.1 - C.referenceState) + |z.2|)
    (fun f => physicalNorm T (3 / 4 : ℝ) (b + 1) ((S.height (3 / 4 : ℝ)).decode f.val))
    (fun f => S.sourceGrading (b + loss + 1) f)
    (fun z f F => ∀ m, (V.forget (3 / 4 : ℝ) 0 b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K z m ((S.height (3 / 4 : ℝ)).decode f.val)) hA ?_ ?_ ?_ ?_ hlift
  · intro z
    exact add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (abs_nonneg _)
  · intro z
    exact add_le_add (add_le_add le_rfl
      (solve_stateGrading_monotone S (by omega) (z.1 - C.referenceState))) le_rfl
  · intro f
    exact Real.sqrt_nonneg _
  · intro f
    exact source_physicalNorm_le_grading hS (by omega) f

end ContinuousFlexibility.Analysis
