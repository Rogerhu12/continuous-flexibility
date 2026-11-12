import ContinuousFlexibility.Analysis.N01cInverseProfileParameters
import ContinuousFlexibility.Analysis.N01cProfileBaseBounds

/-!
# Material bounds for the actual reciprocal profile towers

The true radial Leibniz expansion uses reference inverse-square jets and
profile jets at the reflected state.  The lower profile-ratio estimate at
the original state bounds the reflected exponential; reflection is never
asserted to preserve the original reference-centred neighbourhood.

A finite-order envelope argument controls the reference multiplier.
Every positive parameter derivative retains the full H^(3/4) weight and
only level-zero state direction factors.  The ordinary base jets require
only an E0 envelope bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

/-- A finite ordinary Leibniz convolution preserves one prescribed weight.
Only the two primitive radial-jet envelopes are assumed. -/
theorem finiteLeibniz_envelope_bound {X : Type*}
    (W E : X → ℝ) (hW : ∀ x, 0 ≤ W x) (hE : ∀ x, 1 ≤ E x)
    (F G : ℕ → X → ℝ) (hG : ∀ j x, 0 ≤ G j x)
    (hFbound : ∀ j, ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ x, F j x ≤ C * 1 * E x ^ A)
    (hGbound : ∀ j, ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ x, G j x ≤ C * W x * E x ^ A) (n : ℕ) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ x,
      (∑ a : Fin (n + 1), (n.choose a.val : ℝ) * F a.val x * G (n - a.val) x) ≤
        C * W x * E x ^ A := by
  obtain ⟨CF, AF, hCF, hAF, hFB⟩ := finiteOrder_envelope_bound
    (fun _ : X => 1) E (fun _ => zero_le_one) hE F hFbound n
  obtain ⟨CG, AG, hCG, hAG, hGB⟩ := finiteOrder_envelope_bound
    W E hW hE G hGbound n
  let N : ℝ := ∑ a : Fin (n + 1), (n.choose a.val : ℝ)
  let C₀ : ℝ := N * CF * CG
  have hN : 0 ≤ N := Finset.sum_nonneg (fun a _ => Nat.cast_nonneg _)
  have hC₀ : 0 ≤ C₀ := mul_nonneg (mul_nonneg hN hCF.le) hCG.le
  refine ⟨1 + C₀, AF + AG, by linarith, add_pos hAF hAG, fun x => ?_⟩
  have hEpos : 0 < E x := zero_lt_one.trans_le (hE x)
  have hFB' (j : ℕ) (hj : j ≤ n) : F j x ≤ CF * E x ^ AF := by
    simpa only [mul_one] using hFB j hj x
  calc
    _ ≤ ∑ a : Fin (n + 1), (n.choose a.val : ℝ) *
        ((CF * CG) * W x * E x ^ (AF + AG)) := by
      apply Finset.sum_le_sum
      intro a _
      have ha : a.val ≤ n := Nat.le_of_lt_succ a.isLt
      calc
        _ ≤ (n.choose a.val : ℝ) * (CF * E x ^ AF) *
            (CG * W x * E x ^ AG) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (hFB' a.val ha) (Nat.cast_nonneg _))
            (hGB (n - a.val) (Nat.sub_le _ _) x) (hG _ x)
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hCF.le
              (Real.rpow_nonneg hEpos.le _)))
        _ = _ := by rw [Real.rpow_add hEpos]; ring
    _ = N * ((CF * CG) * W x * E x ^ (AF + AG)) := (Finset.sum_mul _ _ _).symm
    _ = C₀ * W x * E x ^ (AF + AG) := by dsimp only [C₀]; ring
    _ ≤ (1 + C₀) * W x * E x ^ (AF + AG) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) (hW x))
        (Real.rpow_nonneg hEpos.le _)

/-- Absolute values of the genuine two-factor radial Leibniz formula. -/
theorem abs_iteratedDeriv_mul_le_finSum {f g : ℝ → ℝ} {r : ℝ}
    (hf : ContDiffAt ℝ ∞ f r) (hg : ContDiffAt ℝ ∞ g r) (n : ℕ) :
    |iteratedDeriv n (fun s => f s * g s) r| ≤
      ∑ a : Fin (n + 1), (n.choose a.val : ℝ) *
        |iteratedDeriv a.val f r| * |iteratedDeriv (n - a.val) g r| := by
  let term (a : ℕ) : ℝ :=
    (n.choose a : ℝ) * iteratedDeriv a f r * iteratedDeriv (n - a) g r
  have he : iteratedDeriv n (fun s => f s * g s) r =
      ∑ a : Fin (n + 1), term a.val := by
    rw [Fin.sum_univ_eq_sum_range term]
    exact iteratedDeriv_fun_mul (hf.of_le (by simp)) (hg.of_le (by simp))
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro a _
  dsimp only [term]
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]

/-- A true reflected-profile bound passes through the finite reciprocal
Leibniz sum, retaining the same direction factor. -/
private theorem abs_leibniz_reflectedSum_le
    (n : ℕ) (F R : ℕ → ℝ) (u : Fin (n + 1) → ℝ) (p : ℝ)
    (hu : ∀ a, |u a| ≤ 2 * R (n - a.val) * p) :
    |∑ a : Fin (n + 1), (n.choose a.val : ℝ) * F a.val * u a| ≤
      2 * (∑ a : Fin (n + 1), (n.choose a.val : ℝ) *
        |F a.val| * R (n - a.val)) * p := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ a : Fin (n + 1), ((n.choose a.val : ℝ) * |F a.val|) *
        (2 * R (n - a.val) * p) := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hu a)
        (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
    _ = _ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      ring

private theorem exp_reflectedCLM_le_two
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (L : E →L[ℝ] ℝ) (x : E) (h : (1 / 2 : ℝ) ≤ Real.exp (L x)) :
    Real.exp (L (-x)) ≤ 2 := by
  simpa only [map_neg, Real.exp_neg, one_div, inv_inv] using
    (inv_anti₀ (show (0 : ℝ) < 1 / 2 by norm_num) h)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

/-- The fixed inverse-square reference multiplier applied to a radial
majorant, with the exact ordinary Leibniz coefficients. -/
def referenceInverseSquareLeibnizMajorant
    (D : ReferenceData) (R : ℕ → ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  ∑ a : Fin (n + 1), (n.choose a.val : ℝ) *
    |iteratedDeriv a.val (fun s => (D.w s)⁻¹ * (D.w s)⁻¹) r| * R (n - a.val)

/-- Every jet of the actual inverse-square reference multiplier has a
uniform envelope bound on the genuine radial cells. -/
theorem referenceInverseSquare_iteratedDeriv_le_E0
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) (n : ℕ) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m r, r ∈ D.cells m →
      |iteratedDeriv n (fun s => (D.w s)⁻¹ * (D.w s)⁻¹) r| ≤ B * T.E0 r ^ A := by
  have hD : RadialProfileGeometry D := hRef.choose_spec.1
  have hpart : RadialPartition D := hRef.choose_spec.2.1
  let X : Type := {p : ℕ × ℝ // p.2 ∈ D.cells p.1}
  have hcore (x : X) : x.1.2 ∈ Ioo D.a D.b := hpart.2.2.2.1 x.1.1 x.2
  let E : X → ℝ := fun x => T.E0 x.1.2
  let F : ℕ → X → ℝ := fun j x => |iteratedDeriv j (fun s => (D.w s)⁻¹) x.1.2|
  have hFB (j : ℕ) : ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ x : X, F j x ≤ B * 1 * E x ^ A := by
    obtain ⟨B, A, hB, hA, hb⟩ := referenceInverse_iteratedDeriv_le_E0 hT hRef hE j
    exact ⟨B, A, hB, hA, fun x => by
      simpa only [F, E, mul_one] using hb x.1.1 x.1.2 x.2⟩
  obtain ⟨B, A, hB, hA, hb⟩ := finiteLeibniz_envelope_bound
    (fun _ : X => 1) E (fun _ => zero_le_one) (fun x => hE _ (hcore x))
    F F (fun _ _ => abs_nonneg _) hFB hFB n
  refine ⟨B, A, hB, hA, fun m r hrm => ?_⟩
  have hr := hpart.2.2.2.1 m hrm
  have hInv : ContDiffAt ℝ ∞ (fun s => (D.w s)⁻¹) r :=
    hD.2.2.1.1.contDiffAt.inv (hD.2.2.2.2.1 r hr).ne'
  apply (abs_iteratedDeriv_mul_le_finSum hInv hInv n).trans
  simpa only [F, E, mul_one] using hb (⟨(m, r), hrm⟩ : X)

/-- Material bounds for primitive radial majorants are preserved by the
actual inverse-square reference multiplier. -/
theorem referenceInverseSquareLeibnizMajorant_material_bound
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (W : ℝ → ℝ) (hW : ∀ r ∈ Ioo D.a D.b, 0 ≤ W r)
    (R : ℕ → ∀ r, r ∈ Ioo D.a D.b → ℝ)
    (hR : ∀ j r hr, 0 ≤ R j r hr)
    (hRB : ∀ j, ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r (hr : r ∈ Ioo D.a D.b), r ∈ D.cells m →
        R j r hr ≤ B * W r * T.E0 r ^ A) (n : ℕ) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r (hr : r ∈ Ioo D.a D.b), r ∈ D.cells m →
        referenceInverseSquareLeibnizMajorant D (fun j => R j r hr) n r ≤
          B * W r * T.E0 r ^ A := by
  have hpart : RadialPartition D := hRef.choose_spec.2.1
  let X : Type := {p : ℕ × ℝ // p.2 ∈ D.cells p.1}
  have hcore (x : X) : x.1.2 ∈ Ioo D.a D.b := hpart.2.2.2.1 x.1.1 x.2
  let E : X → ℝ := fun x => T.E0 x.1.2
  let F : ℕ → X → ℝ := fun j x =>
    |iteratedDeriv j (fun s => (D.w s)⁻¹ * (D.w s)⁻¹) x.1.2|
  let G : ℕ → X → ℝ := fun j x => R j x.1.2 (hcore x)
  have hFB (j : ℕ) : ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ x : X, F j x ≤ B * 1 * E x ^ A := by
    obtain ⟨B, A, hB, hA, hb⟩ := referenceInverseSquare_iteratedDeriv_le_E0 hT hRef hE j
    exact ⟨B, A, hB, hA, fun x => by
      simpa only [F, E, mul_one] using hb x.1.1 x.1.2 x.2⟩
  have hGB (j : ℕ) : ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ x : X, G j x ≤ B * W x.1.2 * E x ^ A := by
    obtain ⟨B, A, hB, hA, hb⟩ := hRB j
    exact ⟨B, A, hB, hA, fun x => hb x.1.1 x.1.2 (hcore x) x.2⟩
  obtain ⟨B, A, hB, hA, hb⟩ := finiteLeibniz_envelope_bound
    (fun x : X => W x.1.2) E (fun x => hW _ (hcore x)) (fun x => hE _ (hcore x))
    F G (fun j x => hR j _ (hcore x)) hFB hGB n
  exact ⟨B, A, hB, hA, fun m r hr hrm => hb (⟨(m, r), hrm⟩ : X)⟩

private abbrev inverseBoundsStateTopology (S : PhysicalSpacesData) :
    TopologicalSpace (AnnularState S) := inferInstance
attribute [local instance] inverseBoundsStateTopology

private abbrev inverseBoundsStateGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := inferInstance
attribute [local instance] inverseBoundsStateGroup

private abbrev inverseBoundsStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := inferInstance
attribute [local instance] inverseBoundsStateModule

private abbrev inverseBoundsStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) :=
  (inverseBoundsStateModule S).toDistribMulAction.toDistribSMul.toSMul
attribute [local instance] inverseBoundsStateSMul

/-- The original lower ratio estimate bounds the reflected exponential.
Membership of the reflected state in the original ball is not used. -/
theorem n01PartB_reflectedProfileExponent_exp_le_two
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hD : RadialProfileGeometry D)
    (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) :
    Real.exp ((-z.1 : AnnularState S).2.1 * D.chi r + stateControlSum C (-z.1) r) ≤ 2 := by
  let L : AnnularState S →L[ℝ] ℝ :=
    stateProfileExponentCLM hS hT hA.1.1 hA.2.2.1 r hr
  have hw : D.w r ≠ 0 := (hD.2.2.2.2.1 r hr).ne'
  have hp : (r, (0 : ℝ)) ∈ annularOpen D := ⟨hr, mem_univ _⟩
  have hlo := (n01PartB_denominator_bounds hS hA.2.1 hB hz hp).1
  have hratio : stateProfile D S C z.1 r / D.w r = Real.exp (L z.1) :=
    (congrArg (fun a : ℝ => a / D.w r)
      (stateProfile_eq_exp_exponentCLM hS hT hA.1.1 hA.2.2.1 r hr z.1)).trans
        (mul_div_cancel_left₀ _ hw)
  have he : Real.exp (L (-z.1)) ≤ 2 :=
    exp_reflectedCLM_le_two L z.1 (hlo.trans_eq hratio)
  exact (congrArg Real.exp
    (stateProfileExponentCLM_apply hS hT hA.1.1 hA.2.2.1 r hr (-z.1))).symm.trans_le he

/-- The global profile raw estimate applies at the reflected state, with
the original neighbourhood used only to control its exponent and grading. -/
theorem stateProfileRadialJetSmoothDirections_reflected_rawProductBound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hD : RadialProfileGeometry D)
    (hχ : ContDiff ℝ ∞ D.chi) (hB : N01PartB D S C base ε)
    (n k : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (v : Fin k → AnnularState S) :
    |(stateProfileRadialJetSmoothDirections
      hS hT hA.1.1 hD hA.2.2.1 hχ n r hr).D k (-z.1) (fun i => -(v i))| ≤
      2 * profileParameterProductMajorant (fun j => |iteratedDeriv j D.w r|)
        (fun j => stateProfileExponentJetMajorant D T C hA.2.2.1 j r hr)
        (stateGrading S 0 C.referenceState + ε) n k * ∏ i, stateGrading S 0 (v i) := by
  let W : ℕ → ℝ := fun j => |iteratedDeriv j D.w r|
  let P : ℕ → ℝ := fun j => stateProfileExponentJetMajorant D T C hA.2.2.1 j r hr
  have hW (j : ℕ) : 0 ≤ W j := abs_nonneg _
  have hP (j : ℕ) : 0 ≤ P j :=
    stateProfileExponentJetMajorant_nonneg hT hA.1.1 hA.2.2.1 j r hr
  have hq : 0 ≤ stateGrading S 0 z.1 := apply_nonneg _ _
  have hraw :
      |(stateProfileRadialJetSmoothDirections
        hS hT hA.1.1 hD hA.2.2.1 hχ n r hr).D k (-z.1) (fun i => -(v i))| ≤
      Real.exp ((-z.1 : AnnularState S).2.1 * D.chi r + stateControlSum C (-z.1) r) *
        profileParameterProductMajorant W P (stateGrading S 0 z.1) n k *
          ∏ i, stateGrading S 0 (v i) := by
    simpa only [map_neg_eq_map] using stateProfileRadialJetSmoothDirections_rawProductBound
      hS hT hA.1.1 hD hA.2.2.1 hχ n k r hr (-z.1) (fun i => -(v i))
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul (n01PartB_reflectedProfileExponent_exp_le_two hS hT hA hD hB hz r hr)
      (profileParameterProductMajorant_mono W P hW hP hq
        (stateGrading_zero_le_reference_add_radius hz) n k)
      (profileParameterProductMajorant_nonneg W P _ hW hP hq n k) (by norm_num))
    (Finset.prod_nonneg (fun i _ => apply_nonneg (stateGrading S 0) (v i))))

/-- The corresponding ordinary reflected profile jets use the same fixed
base-state grading, without any height factor at parameter order zero. -/
theorem abs_iteratedDeriv_stateProfile_reflected_le_majorant
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hD : RadialProfileGeometry D)
    (hχ : ContDiff ℝ ∞ D.chi) (hB : N01PartB D S C base ε)
    (n : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε) :
    |iteratedDeriv n (stateProfile D S C (-z.1)) r| ≤
      2 * scaledExponentialJetMajorant (fun j => |iteratedDeriv j D.w r|)
        (fun j => stateProfileExponentJetMajorant D T C hA.2.2.1 j r hr)
        (stateGrading S 0 C.referenceState + ε) n := by
  let W : ℕ → ℝ := fun j => |iteratedDeriv j D.w r|
  let P : ℕ → ℝ := fun j => stateProfileExponentJetMajorant D T C hA.2.2.1 j r hr
  have hW (j : ℕ) : 0 ≤ W j := abs_nonneg _
  have hP (j : ℕ) : 0 ≤ P j :=
    stateProfileExponentJetMajorant_nonneg hT hA.1.1 hA.2.2.1 j r hr
  have hq : 0 ≤ stateGrading S 0 z.1 := apply_nonneg _ _
  have hraw : |iteratedDeriv n (stateProfile D S C (-z.1)) r| ≤
      Real.exp ((-z.1 : AnnularState S).2.1 * D.chi r + stateControlSum C (-z.1) r) *
        scaledExponentialJetMajorant W P (stateGrading S 0 z.1) n := by
    simpa only [map_neg_eq_map] using abs_iteratedDeriv_stateProfile_le_rawMajorant
      hS hT hA.1.1 hD hA.2.2.1 hχ n r hr (-z.1)
  exact hraw.trans (mul_le_mul
    (n01PartB_reflectedProfileExponent_exp_le_two hS hT hA hD hB hz r hr)
    (scaledExponentialJetMajorant_mono W P hW hP hq
      (stateGrading_zero_le_reference_add_radius hz) n)
    (scaledExponentialJetMajorant_nonneg W P _ hW hP hq n) (by norm_num))

/-- The exact reciprocal parameter tower is bounded by its finite
reference-multiplier convolution and the unchanged direction product. -/
theorem stateInverseProfileRadialJetSmoothDirections_rawProductBound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hD : RadialProfileGeometry D)
    (hχ : ContDiff ℝ ∞ D.chi) (hB : N01PartB D S C base ε)
    (n k : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (v : Fin k → AnnularState S) :
    |(stateInverseProfileRadialJetSmoothDirections
      hS hT hA.1.1 hD hA.2.2.1 hχ n r hr).D k z.1 v| ≤
      2 * referenceInverseSquareLeibnizMajorant D
        (fun j => profileParameterProductMajorant (fun a => |iteratedDeriv a D.w r|)
          (fun a => stateProfileExponentJetMajorant D T C hA.2.2.1 a r hr)
          (stateGrading S 0 C.referenceState + ε) j k) n r *
            ∏ i, stateGrading S 0 (v i) := by
  have h := abs_leibniz_reflectedSum_le n
    (fun j => iteratedDeriv j (fun s => (D.w s)⁻¹ * (D.w s)⁻¹) r)
    (fun j => profileParameterProductMajorant (fun a => |iteratedDeriv a D.w r|)
      (fun a => stateProfileExponentJetMajorant D T C hA.2.2.1 a r hr)
      (stateGrading S 0 C.referenceState + ε) j k)
    (fun a : Fin (n + 1) => (stateProfileRadialJetSmoothDirections
      hS hT hA.1.1 hD hA.2.2.1 hχ (n - a.val) r hr).D k (-z.1) (fun i => -(v i)))
    (∏ i, stateGrading S 0 (v i))
    (fun a => stateProfileRadialJetSmoothDirections_reflected_rawProductBound
      hS hT hA hD hχ hB (n - a.val) k r hr hz v)
  exact (congrArg abs (stateInverseProfileRadialJetSmoothDirections_D_apply
    hS hT hA.1.1 hD hA.2.2.1 hχ n k r hr z.1 v)).trans_le h

/-- Ordinary reciprocal-profile jets have the same genuine finite
convolution majorant, with no parameter direction factors. -/
theorem abs_iteratedDeriv_stateInverseProfile_le_majorant
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hD : RadialProfileGeometry D)
    (hχ : ContDiff ℝ ∞ D.chi) (hB : N01PartB D S C base ε)
    (n : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε) :
    |iteratedDeriv n (fun s => (stateProfile D S C z.1 s)⁻¹) r| ≤
      2 * referenceInverseSquareLeibnizMajorant D
        (fun j => scaledExponentialJetMajorant (fun a => |iteratedDeriv a D.w r|)
          (fun a => stateProfileExponentJetMajorant D T C hA.2.2.1 a r hr)
          (stateGrading S 0 C.referenceState + ε) j) n r := by
  have h := abs_leibniz_reflectedSum_le n
    (fun j => iteratedDeriv j (fun s => (D.w s)⁻¹ * (D.w s)⁻¹) r)
    (fun j => scaledExponentialJetMajorant (fun a => |iteratedDeriv a D.w r|)
      (fun a => stateProfileExponentJetMajorant D T C hA.2.2.1 a r hr)
      (stateGrading S 0 C.referenceState + ε) j)
    (fun a : Fin (n + 1) => iteratedDeriv (n - a.val) (stateProfile D S C (-z.1)) r)
    1 (fun a => by
      simpa only [mul_one] using abs_iteratedDeriv_stateProfile_reflected_le_majorant
        hS hT hA hD hχ hB (n - a.val) r hr hz)
  have he := congrArg abs (iteratedDeriv_stateProfile_inverse_eq_reflected_sum
    hS hT hA.1.1 hD hA.2.2.1 hχ n r hr z.1)
  exact he.trans_le (by
    simpa only [referenceInverseSquareLeibnizMajorant, mul_one] using h)

/-- Every positive parameter derivative of every radial reciprocal
profile jet retains the full material height weight on the original ball. -/
theorem stateInverseProfileRadialJetSmoothDirections_material_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hD : RadialProfileGeometry D)
    (hχ : ContDiff ℝ ∞ D.chi) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b) (n k : ℕ) (hk : 0 < k) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r (hr : r ∈ Ioo D.a D.b), r ∈ D.cells m →
      ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin k → AnnularState S,
        |(stateInverseProfileRadialJetSmoothDirections
          hS hT hA.1.1 hD hA.2.2.1 hχ n r hr).D k z.1 v| ≤
          (B * T.H r ^ (3 / 4 : ℝ) * T.E0 r ^ A) * ∏ i, stateGrading S 0 (v i) :=
  exists_material_bound_of_majorant
    (X := AnnularState S × ℝ) (V := Fin k → AnnularState S)
    (Ioo D.a D.b) D.cells (fun r => T.H r ^ (3 / 4 : ℝ)) T.E0
    (stateNeighborhood S C base ε)
    (fun r hr => referenceInverseSquareLeibnizMajorant D
      (fun j => profileParameterProductMajorant (fun a => |iteratedDeriv a D.w r|)
        (fun a => stateProfileExponentJetMajorant D T C hA.2.2.1 a r hr)
        (stateGrading S 0 C.referenceState + ε) j k) n r)
    (fun r hr z v =>
      (stateInverseProfileRadialJetSmoothDirections
        hS hT hA.1.1 hD hA.2.2.1 hχ n r hr).D k z.1 v)
    (fun _ v => ∏ i, stateGrading S 0 (v i))
    (fun _ v => Finset.prod_nonneg (fun i _ => apply_nonneg (stateGrading S 0) (v i)))
    (referenceInverseSquareLeibnizMajorant_material_bound hT hA.1.1 hE
      (fun r => T.H r ^ (3 / 4 : ℝ))
      (fun r hr => Real.rpow_nonneg (hT.2.1 r hr).2.1.le _)
      (fun j r hr => profileParameterProductMajorant (fun a => |iteratedDeriv a D.w r|)
        (fun a => stateProfileExponentJetMajorant D T C hA.2.2.1 a r hr)
        (stateGrading S 0 C.referenceState + ε) j k)
      (fun j r hr => profileParameterProductMajorant_nonneg _ _ _
        (fun _ => abs_nonneg _)
        (fun a => stateProfileExponentJetMajorant_nonneg hT hA.1.1 hA.2.2.1 a r hr)
        (add_nonneg (apply_nonneg (stateGrading S 0) C.referenceState) hε.le) j k)
      (fun j => profileParameterProductMajorant_material_bound hT hA hE hloc hχloc
        (add_nonneg (apply_nonneg (stateGrading S 0) C.referenceState) hε.le) j k hk) n)
    (fun r hr z hz v => stateInverseProfileRadialJetSmoothDirections_rawProductBound
      hS hT hA hD hχ hB n k r hr hz v)

/-- All ordinary radial reciprocal-profile jets, including order zero,
have a uniform E0 envelope bound on the same original neighbourhood. -/
theorem iteratedDeriv_stateInverseProfile_material_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hD : RadialProfileGeometry D)
    (hχ : ContDiff ℝ ∞ D.chi) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b) (n : ℕ) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r (hr : r ∈ Ioo D.a D.b), r ∈ D.cells m →
      ∀ z ∈ stateNeighborhood S C base ε,
        |iteratedDeriv n (fun s => (stateProfile D S C z.1 s)⁻¹) r| ≤ B * T.E0 r ^ A :=
  exists_scalar_envelope_bound_of_majorant (X := AnnularState S × ℝ)
    (Ioo D.a D.b) D.cells T.E0 (stateNeighborhood S C base ε)
    (fun r hr => referenceInverseSquareLeibnizMajorant D
      (fun j => scaledExponentialJetMajorant (fun a => |iteratedDeriv a D.w r|)
        (fun a => stateProfileExponentJetMajorant D T C hA.2.2.1 a r hr)
        (stateGrading S 0 C.referenceState + ε) j) n r)
    (fun r _ z => iteratedDeriv n (fun s => (stateProfile D S C z.1 s)⁻¹) r)
    (by
      simpa only [mul_one] using referenceInverseSquareLeibnizMajorant_material_bound
        hT hA.1.1 hE (fun _ => 1) (fun _ _ => zero_le_one)
        (fun j r hr => scaledExponentialJetMajorant (fun a => |iteratedDeriv a D.w r|)
          (fun a => stateProfileExponentJetMajorant D T C hA.2.2.1 a r hr)
          (stateGrading S 0 C.referenceState + ε) j)
        (fun j r hr => scaledExponentialJetMajorant_nonneg _ _ _
          (fun _ => abs_nonneg _)
          (fun a => stateProfileExponentJetMajorant_nonneg hT hA.1.1 hA.2.2.1 a r hr)
          (add_nonneg (apply_nonneg (stateGrading S 0) C.referenceState) hε.le) j)
        (fun j => by
          simpa only [mul_one] using scaledExponentialJetMajorant_material_bound
            hT hA hE hloc hχloc
            (add_nonneg (apply_nonneg (stateGrading S 0) C.referenceState) hε.le) j) n)
    (fun r hr z hz => abs_iteratedDeriv_stateInverseProfile_le_majorant
      hS hT hA hD hχ hB n r hr hz)

end ContinuousFlexibility.Statements
