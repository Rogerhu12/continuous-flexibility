module

public import ContinuousFlexibility.Analysis.N01cProfileMajorantWeights
public import ContinuousFlexibility.Analysis.N01cControlJetWeights
public import ContinuousFlexibility.Analysis.N01cReferenceJetBounds
public import ContinuousFlexibility.Analysis.N01cProfileDifferenceBounds

/-!
# Actual profile parameter jets with one exact material height weight

The primitive exponent-jet estimate follows from the original control
bounds and explicit physical placement.  The material axioms uniformly
bound each extra height factor.  Applying the finite-product calculation
therefore leaves one full H^(3/4) in every positive parameter derivative,
at every radial order, on the original N01b neighbourhood.

The zero-parameter difference uses the actual first-jet segment theorem.
No tame estimate for the profile itself is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

set_option backward.isDefEq.respectTransparency false

/-- Transport a scalar material majorant through its original nonnegative
direction factor.  All existence and domain binders stay generic. -/
theorem exists_material_bound_of_majorant
    {X V : Type*} (core : Set ℝ) (cells : ℕ → Set ℝ)
    (H E : ℝ → ℝ) (U : Set X)
    (M : ∀ r, r ∈ core → ℝ) (f : ∀ r, r ∈ core → X → V → ℝ)
    (P : X → V → ℝ) (hP : ∀ x v, 0 ≤ P x v)
    (hM : ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r (hr : r ∈ core), r ∈ cells m → M r hr ≤ B * H r * E r ^ A)
    (hf : ∀ r (hr : r ∈ core), ∀ x ∈ U, ∀ v,
      |f r hr x v| ≤ 2 * M r hr * P x v) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r (hr : r ∈ core), r ∈ cells m → ∀ x ∈ U, ∀ v,
        |f r hr x v| ≤ (B * H r * E r ^ A) * P x v := by
  obtain ⟨B, A, hB, hA, hbound⟩ := hM
  refine ⟨2 * B, A, mul_pos (by norm_num) hB, hA, fun m r hr hm x hx v => ?_⟩
  calc
    _ ≤ 2 * M r hr * P x v := hf r hr x hx v
    _ ≤ 2 * (B * H r * E r ^ A) * P x v :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hbound m r hr hm) (by norm_num)) (hP x v)
    _ = _ := by ring

/-- The same transport for an actual scalar family with a base-point
weight, including a seminorm of the reference displacement. -/
theorem exists_scalar_material_bound_of_majorant
    {X : Type*} (core : Set ℝ) (cells : ℕ → Set ℝ)
    (H E : ℝ → ℝ) (U : Set X)
    (M : ∀ r, r ∈ core → ℝ) (f : ∀ r, r ∈ core → X → ℝ)
    (P : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hM : ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r (hr : r ∈ core), r ∈ cells m → M r hr ≤ B * H r * E r ^ A)
    (hf : ∀ r (hr : r ∈ core), ∀ x ∈ U,
      |f r hr x| ≤ 2 * M r hr * P x) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r (hr : r ∈ core), r ∈ cells m → ∀ x ∈ U,
        |f r hr x| ≤ (B * H r * E r ^ A) * P x := by
  obtain ⟨B, A, hB, hA, h⟩ := exists_material_bound_of_majorant
    (X := X) (V := Unit) core cells H E U M (fun r hr x _ => f r hr x)
    (fun x _ => P x) (fun x _ => hP x) hM (fun r hr x hx _ => hf r hr x hx)
  exact ⟨B, A, hB, hA, fun m r hr hm x hx => h m r hr hm x hx ()⟩

/-- A parameter family bounded by twice an envelope majorant retains one
uniform envelope exponent on the same set. -/
theorem exists_scalar_envelope_bound_of_majorant
    {X : Type*} (core : Set ℝ) (cells : ℕ → Set ℝ)
    (E : ℝ → ℝ) (U : Set X)
    (M : ∀ r, r ∈ core → ℝ) (f : ∀ r, r ∈ core → X → ℝ)
    (hM : ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r (hr : r ∈ core), r ∈ cells m → M r hr ≤ B * E r ^ A)
    (hf : ∀ r (hr : r ∈ core), ∀ x ∈ U, |f r hr x| ≤ 2 * M r hr) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r (hr : r ∈ core), r ∈ cells m → ∀ x ∈ U,
        |f r hr x| ≤ B * E r ^ A := by
  have hM' : ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r (hr : r ∈ core), r ∈ cells m → M r hr ≤ B * 1 * E r ^ A := by
    simpa only [mul_one] using hM
  have hf' : ∀ r (hr : r ∈ core), ∀ x ∈ U,
      |f r hr x| ≤ 2 * M r hr * 1 := by
    simpa only [mul_one] using hf
  simpa only [mul_one] using exists_scalar_material_bound_of_majorant
    core cells (fun _ => 1) E U M f (fun _ => 1) (fun _ => zero_le_one) hM' hf'

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

/-- The genuine finite profile majorant has one full height weight for
every positive number of parameter directions. -/
theorem profileParameterProductMajorant_material_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b)
    {q : ℝ} (hq : 0 ≤ q) (n k : ℕ) (hk : 0 < k) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r (hr : r ∈ Ioo D.a D.b), r ∈ D.cells m →
        profileParameterProductMajorant (fun j => |iteratedDeriv j D.w r|)
          (fun j => stateProfileExponentJetMajorant D T C hA.2.2.1 j r hr) q n k ≤
            B * T.H r ^ (3 / 4 : ℝ) * T.E0 r ^ A := by
  classical
  have hpart : RadialPartition D := hA.1.1.choose_spec.2.1
  let X : Type := {p : ℕ × ℝ // p.2 ∈ D.cells p.1}
  have hcore (x : X) : x.1.2 ∈ Ioo D.a D.b :=
    hpart.2.2.2.1 x.1.1 x.2
  let E : X → ℝ := fun x => T.E0 x.1.2
  let H : X → ℝ := fun x => T.H x.1.2 ^ (3 / 4 : ℝ)
  let W : ℕ → X → ℝ := fun j x => |iteratedDeriv j D.w x.1.2|
  let P : ℕ → X → ℝ := fun j x =>
    stateProfileExponentJetMajorant D T C hA.2.2.1 j x.1.2 (hcore x)
  have hEone (x : X) : 1 ≤ E x := hE _ (hcore x)
  have hHnonneg (x : X) : 0 ≤ H x :=
    Real.rpow_nonneg (hT.2.1 _ (hcore x)).2.1.le _
  have hWprimitive (j : ℕ) :
      ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ x : X, W j x ≤ B * 1 * E x ^ A := by
    obtain ⟨B, A, hB, hA', hbound⟩ := referenceProfile_iteratedDeriv_le_E0 hA.1.1 hE j
    refine ⟨B, A, hB, hA', fun x => ?_⟩
    simpa only [W, E, mul_one] using hbound x.1.1 x.1.2 x.2
  have hPprimitive (j : ℕ) :
      ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ x : X, P j x ≤ B * H x * E x ^ A := by
    obtain ⟨B, A, hB, hA', hbound⟩ :=
      stateProfileExponentJetMajorant_material_bound hT hA hloc hχloc j
    exact ⟨B, A, hB, hA', fun x => hbound x.1.2 (hcore x)⟩
  obtain ⟨CW, AW, hCW, hAW, hWbound⟩ := finiteOrder_envelope_bound
    (fun _ : X => 1) E (fun _ => zero_le_one) hEone W hWprimitive n
  obtain ⟨CP, AP, hCP, hAP, hPbound⟩ := finiteOrder_envelope_bound
    H E hHnonneg hEone P hPprimitive n
  obtain ⟨M, hM, hMbound⟩ :=
    materialHeight_E0_weight_bounded hT (γ := (3 / 4 : ℝ)) (by norm_num) AP
  let R : ℝ := CP * M
  have hR : 0 < R := mul_pos hCP hM
  let Q : ℝ := radialProfileNumericMajorant R q n k
  have hQ : 0 ≤ Q := radialProfileNumericMajorant_nonneg hR.le hq n k
  let B₀ : ℝ := Q * CW * CP * R ^ (k - 1)
  have hB₀ : 0 ≤ B₀ := by dsimp only [B₀]; positivity
  refine ⟨1 + B₀, AW + AP, by linarith, add_pos hAW hAP, fun m r hr hrm => ?_⟩
  let x : X := ⟨(m, r), hrm⟩
  have hWnonneg (j : ℕ) : 0 ≤ W j x := abs_nonneg _
  have hPnonneg (j : ℕ) : 0 ≤ P j x :=
    stateProfileExponentJetMajorant_nonneg hT hA.1.1 hA.2.2.1 j r hr
  have hWbound' (j : ℕ) (hj : j ≤ n) : W j x ≤ CW * E x ^ AW := by
    simpa only [mul_one] using hWbound j hj x
  have hPbound' (j : ℕ) (hj : j ≤ n) : P j x ≤ R := by
    calc
      P j x ≤ CP * H x * E x ^ AP := hPbound j hj x
      _ = CP * (T.H r ^ (3 / 4 : ℝ) * T.E0 r ^ AP) := by
        dsimp only [H, E, x]
        ring
      _ ≤ CP * M := mul_le_mul_of_nonneg_left (hMbound r hr) hCP.le
      _ = R := rfl
  have hWsize : 0 ≤ CW * E x ^ AW :=
    mul_nonneg hCW.le (Real.rpow_nonneg (zero_le_one.trans (hEone x)) _)
  have hPsize : 0 ≤ CP * H x * E x ^ AP :=
    mul_nonneg (mul_nonneg hCP.le (hHnonneg x))
      (Real.rpow_nonneg (zero_le_one.trans (hEone x)) _)
  have hraw := profileParameterProductMajorant_le_one_weight
    (fun j => W j x) (fun j => P j x) hWnonneg hPnonneg
    hWsize hR.le hPsize hq n k hk hWbound' hPbound'
    (fun j hj => hPbound j hj x)
  have hEpos : 0 < T.E0 r := (hT.2.1 r hr).2.2.1
  calc
    profileParameterProductMajorant (fun j => |iteratedDeriv j D.w r|)
        (fun j => stateProfileExponentJetMajorant D T C hA.2.2.1 j r hr) q n k ≤
      Q * (CW * T.E0 r ^ AW) *
        (CP * T.H r ^ (3 / 4 : ℝ) * T.E0 r ^ AP) * R ^ (k - 1) := hraw
    _ = B₀ * T.H r ^ (3 / 4 : ℝ) * T.E0 r ^ (AW + AP) := by
      rw [Real.rpow_add hEpos]
      dsimp only [B₀]
      ring
    _ ≤ (1 + B₀) * T.H r ^ (3 / 4 : ℝ) * T.E0 r ^ (AW + AP) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) (hHnonneg x))
        (Real.rpow_nonneg hEpos.le _)

private abbrev profileMaterialStateTopology (S : PhysicalSpacesData) :
    TopologicalSpace (AnnularState S) := inferInstance
attribute [local instance] profileMaterialStateTopology

private abbrev profileMaterialStateGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := inferInstance
attribute [local instance] profileMaterialStateGroup

private abbrev profileMaterialStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := inferInstance
attribute [local instance] profileMaterialStateModule

private abbrev profileMaterialStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) :=
  (profileMaterialStateModule S).toDistribMulAction.toDistribSMul.toSMul
attribute [local instance] profileMaterialStateSMul

/-- Positive parameter derivatives of every actual radial profile jet
have the exact material height exponent and only level-zero direction
factors, on the same original neighbourhood for all orders. -/
theorem stateProfileRadialJetSmoothDirections_material_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hD : RadialProfileGeometry D)
    (hχ : ContDiff ℝ ∞ D.chi) (hε : 0 < ε)
    (hB : N01PartB D S C base ε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b) (n k : ℕ) (hk : 0 < k) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r (hr : r ∈ Ioo D.a D.b), r ∈ D.cells m →
      ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin k → AnnularState S,
        |(stateProfileRadialJetSmoothDirections
          hS hT hA.1.1 hD hA.2.2.1 hχ n r hr).D k z.1 v| ≤
          (B * T.H r ^ (3 / 4 : ℝ) * T.E0 r ^ A) *
            ∏ i, stateGrading S 0 (v i) :=
  exists_material_bound_of_majorant
    (X := AnnularState S × ℝ) (V := Fin k → AnnularState S)
    (Ioo D.a D.b) D.cells (fun r => T.H r ^ (3 / 4 : ℝ)) T.E0
    (stateNeighborhood S C base ε)
    (fun r hr => profileParameterProductMajorant (fun j => |iteratedDeriv j D.w r|)
      (fun j => stateProfileExponentJetMajorant D T C hA.2.2.1 j r hr)
      (stateGrading S 0 C.referenceState + ε) n k)
    (fun r hr z v =>
      (stateProfileRadialJetSmoothDirections hS hT hA.1.1 hD hA.2.2.1 hχ n r hr).D k z.1 v)
    (fun _ v => ∏ i, stateGrading S 0 (v i))
    (fun _ v => Finset.prod_nonneg (fun i _ => apply_nonneg (stateGrading S 0) (v i)))
    (profileParameterProductMajorant_material_bound hT hA hE hloc hχloc
      (add_nonneg (apply_nonneg (stateGrading S 0) C.referenceState) hε.le) n k hk)
    (fun r hr z hz v => stateProfileRadialJetSmoothDirections_rawProductBound_on_neighborhood
      hS hT hA.1.1 hD hA.2.2.1 hχ hA.2.1 hB n k r hr hz v)

/-- The actual zeroth-parameter profile difference has the same full
material weight and retains one level-zero state-displacement factor. -/
theorem iteratedDeriv_stateProfile_difference_material_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hD : RadialProfileGeometry D)
    (hχ : ContDiff ℝ ∞ D.chi) (hε : 0 < ε)
    (hB : N01PartB D S C base ε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b) (n : ℕ) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r (hr : r ∈ Ioo D.a D.b), r ∈ D.cells m →
      ∀ z ∈ stateNeighborhood S C base ε,
        |iteratedDeriv n (fun s => stateProfile D S C z.1 s -
            stateProfile D S C C.referenceState s) r| ≤
          (B * T.H r ^ (3 / 4 : ℝ) * T.E0 r ^ A) *
            stateGrading S 0 (z.1 - C.referenceState) :=
  exists_scalar_material_bound_of_majorant (X := AnnularState S × ℝ)
    (Ioo D.a D.b) D.cells (fun r => T.H r ^ (3 / 4 : ℝ)) T.E0
    (stateNeighborhood S C base ε)
    (fun r hr => profileParameterProductMajorant (fun j => |iteratedDeriv j D.w r|)
      (fun j => stateProfileExponentJetMajorant D T C hA.2.2.1 j r hr)
      (stateGrading S 0 C.referenceState + ε) n 1)
    (fun r _ z => iteratedDeriv n
      (fun s => stateProfile D S C z.1 s - stateProfile D S C C.referenceState s) r)
    (fun z => stateGrading S 0 (z.1 - C.referenceState))
    (fun z => apply_nonneg (stateGrading S 0) (z.1 - C.referenceState))
    (profileParameterProductMajorant_material_bound hT hA hE hloc hχloc
      (add_nonneg (apply_nonneg (stateGrading S 0) C.referenceState) hε.le) n 1 (by norm_num))
    (fun r hr z hz => iteratedDeriv_stateProfile_difference_bound
      hS hT hA.1.1 hD hA.2.2.1 hχ hA.2.1 hB n r hr hz)

end ContinuousFlexibility.Statements
