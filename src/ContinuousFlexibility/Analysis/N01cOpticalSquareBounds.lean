import ContinuousFlexibility.Analysis.N01cOpticalSquareRootJets
import ContinuousFlexibility.Analysis.N01cInverseProfileBounds
import ContinuousFlexibility.Analysis.N01cRelativeControl
import ContinuousFlexibility.Analysis.N01cControlJetWeights

/-!
# Primitive radial bounds for the actual optical square

The reference and control factors retain their actual component, cell and
sample. Every estimate follows from the original reference/control jets.
No speed, coefficient, or optical-jet tame bound is an input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff BigOperators

theorem iteratedDeriv_mul_envelope_bound {X : Type*}
    (W E : X → ℝ) (hW : ∀ x, 0 ≤ W x) (hE : ∀ x, 1 ≤ E x)
    (point : X → ℝ) (f g : X → ℝ → ℝ)
    (hf : ∀ x, ContDiffAt ℝ ∞ (f x) (point x))
    (hg : ∀ x, ContDiffAt ℝ ∞ (g x) (point x))
    (hF : ∀ j, ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ x, |iteratedDeriv j (f x) (point x)| ≤ C * 1 * E x ^ A)
    (hG : ∀ j, ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ x, |iteratedDeriv j (g x) (point x)| ≤ C * W x * E x ^ A)
    (n : ℕ) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ x,
      |iteratedDeriv n (fun r => f x r * g x r) (point x)| ≤ C * W x * E x ^ A := by
  obtain ⟨C, A, hC, hA, hb⟩ := finiteLeibniz_envelope_bound W E hW hE
    (fun j x => |iteratedDeriv j (f x) (point x)|)
    (fun j x => |iteratedDeriv j (g x) (point x)|)
    (fun _ _ => abs_nonneg _) hF hG n
  exact ⟨C, A, hC, hA, fun x =>
    (abs_iteratedDeriv_mul_le_finSum (hf x) (hg x) n).trans (hb x)⟩

theorem inverseRadius_iteratedDeriv_bound {a b : ℝ} (ha : 0 < a) (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ r ∈ Icc a b,
      |iteratedDeriv n (fun t : ℝ => t⁻¹) r| ≤ B := by
  have hs (r : ℝ) (hr : r ∈ Icc a b) :
      ContDiffAt ℝ ∞ (fun t : ℝ => t⁻¹) r :=
    contDiffAt_id.inv (ha.trans_le hr.1).ne'
  have hc : ContinuousOn (fun r => |iteratedDeriv n (fun t : ℝ => t⁻¹) r|)
      (Icc a b) := by
    intro r hr
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
      ((hs r hr).continuousAt_iteratedFDeriv (k := n) (by simp)).norm.continuousWithinAt
  obtain ⟨B, hb⟩ := (isCompact_Icc : IsCompact (Icc a b)).bddAbove_image hc
  exact ⟨max 1 B, zero_lt_one.trans_le (le_max_left _ _),
    fun r hr => (hb ⟨r, hr, rfl⟩).trans (le_max_right _ _)⟩

/-- Scalar multiplication of a primitive endpoint estimate by a linear
evaluation estimate. The whole existential transport stays independent
of any representation of the state space. -/
theorem exists_opticalDirection_envelope_bound {V : Type*}
    (Ω : ℕ → Set ℝ) (δ : ℕ → ℝ → ℝ) (g : ℕ → ℝ → ℝ)
    (κ : V → ℕ → ℝ) (p : V → ℝ) (H₀ H E : ℕ → ℝ)
    (c : ℝ) (hc : 0 < c) (hp : ∀ v, 0 ≤ p v) (hH₀ : ∀ m, 0 ≤ H₀ m)
    (hδ : ∀ m r, r ∈ Ω m → 0 ≤ δ m r)
    (hκ : ∀ v m, |κ v m| ≤ (c * H₀ m) * p v)
    (hweight : ∀ A : ℝ, ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ m, H₀ m * E m ^ A ≤ C * H m * E m ^ K)
    (n : ℕ)
    (hg : ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m r, r ∈ Ω m →
      δ m r ^ n * |g m r| ≤ B * E m ^ A * δ m r) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m r, r ∈ Ω m → ∀ v : V,
      δ m r ^ n * |κ v m * g m r| ≤
        (B * H m * E m ^ A) * δ m r * p v := by
  obtain ⟨B, A, hB, _, hb⟩ := hg
  obtain ⟨C, K, hC, hK, hw⟩ := hweight A
  refine ⟨B * c * C, K, mul_pos (mul_pos hB hc) hC, hK, fun m r hr v => ?_⟩
  rw [abs_mul]
  calc
    _ = |κ v m| * (δ m r ^ n * |g m r|) := by ring
    _ ≤ ((c * H₀ m) * p v) * (B * E m ^ A * δ m r) :=
      mul_le_mul (hκ v m) (hb m r hr)
        (mul_nonneg (pow_nonneg (hδ m r hr) n) (abs_nonneg _))
        (mul_nonneg (mul_nonneg hc.le (hH₀ m)) (hp v))
    _ = (B * c) * (H₀ m * E m ^ A) * δ m r * p v := by ring
    _ ≤ (B * c) * (C * H m * E m ^ K) * δ m r * p v :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hw m) (mul_pos hB hc).le) (hδ m r hr)) (hp v)
    _ = _ := by ring

/-- The affine optical square inherits one envelope from its reference
part and a uniformly bounded material factor from its directional part. -/
theorem exists_opticalSquare_envelope_bound {V : Type*}
    (Ω : ℕ → Set ℝ) (δ : ℕ → ℝ → ℝ)
    (f : ℕ → ℝ → V → ℝ) (f₀ : ℕ → ℝ → ℝ) (g : ℕ → ℝ → ℝ)
    (κ : V → ℕ → ℝ) (p : V → ℝ) (H E : ℕ → ℝ)
    (hp : ∀ v, 0 ≤ p v) (hE : ∀ m, 1 ≤ E m)
    (hδ : ∀ m r, r ∈ Ω m → 0 ≤ δ m r)
    (heq : ∀ m r, r ∈ Ω m → ∀ v, f m r v = f₀ m r - κ v m * g m r)
    (hweight : ∀ K : ℝ, ∃ M : ℝ, 0 < M ∧ ∀ m, H m * E m ^ K ≤ M)
    (n : ℕ)
    (hbase : ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m r, r ∈ Ω m →
      δ m r ^ n * |f₀ m r| ≤ B * E m ^ A * δ m r)
    (hdir : ∃ B K : ℝ, 0 < B ∧ 0 < K ∧ ∀ m r, r ∈ Ω m → ∀ v,
      δ m r ^ n * |κ v m * g m r| ≤
        (B * H m * E m ^ K) * δ m r * p v) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m r, r ∈ Ω m → ∀ v : V,
      δ m r ^ n * |f m r v| ≤
        (B * E m ^ A) * δ m r * (1 + p v) := by
  obtain ⟨B₀, A, hB₀, hA, hb⟩ := hbase
  obtain ⟨B₁, K, hB₁, _, hd⟩ := hdir
  obtain ⟨M, hM, hm⟩ := hweight K
  refine ⟨B₀ + B₁ * M, A, add_pos hB₀ (mul_pos hB₁ hM), hA, fun m r hr v => ?_⟩
  have he : 1 ≤ E m ^ A := Real.one_le_rpow (hE m) hA.le
  have hw : B₁ * H m * E m ^ K ≤ B₁ * M := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hm m) hB₁.le
  rw [heq m r hr v]
  calc
    _ ≤ δ m r ^ n * (|f₀ m r| + |κ v m * g m r|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) (pow_nonneg (hδ m r hr) n)
    _ ≤ B₀ * E m ^ A * δ m r + B₁ * M * δ m r * p v := by
      rw [mul_add]
      exact add_le_add (hb m r hr) ((hd m r hr v).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw (hδ m r hr)) (hp v)))
    _ ≤ ((B₀ + B₁ * M) * E m ^ A) * δ m r * (1 + p v) := by
      nlinarith only [mul_nonneg hB₀.le
          (mul_nonneg (zero_le_one.trans he) (mul_nonneg (hδ m r hr) (hp v))),
        mul_nonneg (mul_nonneg hB₁.le hM.le)
          (mul_nonneg (sub_nonneg.mpr he) (mul_nonneg (hδ m r hr) (hp v))),
        mul_nonneg (mul_nonneg hB₁.le hM.le)
          (mul_nonneg (zero_le_one.trans he) (hδ m r hr))]

/-- Apply the affine power formula after scalar equalities have already
identified the actual value and all actual linear directions. -/
theorem affineRpowJets_apply_of_values
    {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
    (α q₀ : ℝ) (L : V →L[ℝ] ℝ) (k : ℕ) (x : V) (v : Fin k → V)
    (q : ℝ) (w : Fin k → ℝ) (hq : q₀ + L x = q) (hw : ∀ i, L (v i) = w i) :
    affineRpowJets α q₀ L k x v =
      rpowJetCoefficient α k * q ^ (α - (k : ℝ)) * ∏ i, w i := by
  rw [affineRpowJets_apply, hq]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => hw i)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

def referenceOpticalSquare (D : ReferenceData) (r : ℝ) : ℝ :=
  -deriv D.w r / (r * D.w r)

def controlOpticalFactor {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (m : ℕ) (r : ℝ) : ℝ :=
  deriv (C.control m) r / r

theorem referenceOpticalSquare_contDiffAt {D : ReferenceData}
    (hD : RadialProfileGeometry D) {r : ℝ} (hr : r ∈ Ioo D.a D.b) :
    ContDiffAt ℝ ∞ (referenceOpticalSquare D) r := by
  have hd : ContDiff ℝ ∞ (deriv D.w) := (contDiff_infty_iff_deriv.mp hD.2.2.1.1).2
  exact hd.contDiffAt.neg.div (contDiffAt_id.mul hD.2.2.1.1.contDiffAt)
    (mul_ne_zero (hD.1.trans hr.1).ne' (hD.2.2.2.2.1 r hr).ne')

theorem controlOpticalFactor_contDiffAt
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    (m : ℕ) {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    ContDiffAt ℝ ∞ (controlOpticalFactor C m) r := by
  have hd : ContDiff ℝ ∞ (deriv (C.control m)) :=
    (contDiff_infty_iff_deriv.mp (hC.2.2.2.2.2.1 m).1).2
  exact hd.contDiffAt.div contDiffAt_id (hD.1.trans ((hC.1 m).1.trans hr.1)).ne'

/-- Every reference optical jet is bounded in its actual cell sample.
The reciprocal-profile envelope and fixed positive inner radius pay all
denominators; the reference profile contributes only ordinary jets. -/
theorem referenceOpticalSquare_iteratedDeriv_sample_bound
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) (n : ℕ) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m r, r ∈ D.cells m →
      |iteratedDeriv n (referenceOpticalSquare D) r| ≤
        B * T.E0 (T.sample m) ^ A := by
  have hD := hRef.choose_spec.1
  have hpart := hRef.choose_spec.2.1
  let X : Type := {p : ℕ × ℝ // p.2 ∈ D.cells p.1}
  let point : X → ℝ := fun x => x.1.2
  let E : X → ℝ := fun x => T.E0 (point x)
  have hcore (x : X) : point x ∈ Ioo D.a D.b := hpart.2.2.2.1 x.1.1 x.2
  have hE₀ (x : X) : 1 ≤ E x := hE _ (hcore x)
  have hd : ContDiff ℝ ∞ (deriv D.w) := (contDiff_infty_iff_deriv.mp hD.2.2.1.1).2
  have hF (j : ℕ) : ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ x : X,
      |iteratedDeriv j (fun r => -deriv D.w r) (point x)| ≤ B * 1 * E x ^ A := by
    obtain ⟨B, A, hB, hA, hb⟩ := referenceProfile_iteratedDeriv_le_E0 hRef hE (j + 1)
    refine ⟨B, A, hB, hA, fun x => ?_⟩
    simpa only [iteratedDeriv_fun_neg, abs_neg, ← iteratedDeriv_succ', mul_one] using
      hb x.1.1 (point x) x.2
  have hG (j : ℕ) : ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ x : X,
      |iteratedDeriv j (fun r => (D.w r)⁻¹) (point x)| ≤ B * 1 * E x ^ A := by
    obtain ⟨B, A, hB, hA, hb⟩ := referenceInverse_iteratedDeriv_le_E0 hT hRef hE j
    exact ⟨B, A, hB, hA, fun x => by simpa only [mul_one] using hb x.1.1 (point x) x.2⟩
  have hInv (x : X) : ContDiffAt ℝ ∞ (fun r => (D.w r)⁻¹) (point x) :=
    hD.2.2.1.1.contDiffAt.inv (hD.2.2.2.2.1 _ (hcore x)).ne'
  have hFG := iteratedDeriv_mul_envelope_bound (fun _ : X => 1) E
    (fun _ => zero_le_one) hE₀ point (fun _ r => -deriv D.w r)
    (fun _ r => (D.w r)⁻¹) (fun _ => hd.contDiffAt.neg) hInv hF hG
  have hR (j : ℕ) : ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ x : X,
      |iteratedDeriv j (fun r : ℝ => r⁻¹) (point x)| ≤ B * 1 * E x ^ A := by
    obtain ⟨B, hB, hb⟩ := inverseRadius_iteratedDeriv_bound (b := D.b) hD.1 j
    refine ⟨B, 1, hB, zero_lt_one, fun x => ?_⟩
    simpa only [mul_one, Real.rpow_one] using
      (hb (point x) ⟨(hcore x).1.le, (hcore x).2.le⟩).trans
        (le_mul_of_one_le_right hB.le (hE₀ x))
  obtain ⟨B, A, hB, hA, hb⟩ := iteratedDeriv_mul_envelope_bound
    (fun _ : X => 1) E (fun _ => zero_le_one) hE₀ point
    (fun _ r => -deriv D.w r * (D.w r)⁻¹) (fun (_ : X) (r : ℝ) => r⁻¹)
    (fun x => hd.contDiffAt.neg.mul (hInv x))
    (fun x => contDiffAt_id.inv (hD.1.trans (hcore x).1).ne') hFG hR n
  obtain ⟨C, K, hC, hK, hcompare⟩ := materialCell_weight_comparison hT hRef 0 A
  have hfun : referenceOpticalSquare D =
      (fun r => (-deriv D.w r * (D.w r)⁻¹) * r⁻¹) := by
    funext r
    simp only [referenceOpticalSquare, div_eq_mul_inv, mul_inv_rev]
    ring
  refine ⟨B * C, K, mul_pos hB hC, hK, fun m r hr => ?_⟩
  have hp : T.E0 r ^ A ≤ C * T.E0 (T.sample m) ^ K := by
    simpa only [Real.rpow_zero, one_mul, mul_one] using (hcompare m r hr).1
  rw [hfun]
  calc
    _ ≤ B * T.E0 r ^ A := by simpa only [mul_one] using hb (⟨(m, r), hr⟩ : X)
    _ ≤ B * (C * T.E0 (T.sample m) ^ K) := mul_le_mul_of_nonneg_left hp hB.le
    _ = _ := by ring

/-- The original control factor, before multiplication by its actual
circle mean, has all radial jets bounded at the designated sample. -/
theorem controlOpticalFactor_iteratedDeriv_sample_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) (n : ℕ) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m r,
      r ∈ Ioo (C.left m) (C.right m) →
      |iteratedDeriv n (controlOpticalFactor C m) r| ≤
        B * T.E0 (T.sample (C.cell m)) ^ A := by
  have hD := hA.1.1.choose_spec.1
  have hpart := hA.1.1.choose_spec.2.1
  have hC := hA.2.2.1
  let X : Type := {p : ℕ × ℝ // p.2 ∈ Ioo (C.left p.1) (C.right p.1)}
  let point : X → ℝ := fun x => x.1.2
  let E : X → ℝ := fun x => T.E0 (T.sample (C.cell x.1.1))
  have hcore (x : X) : point x ∈ Ioo D.a D.b :=
    ⟨(hC.1 x.1.1).1.trans x.2.1, x.2.2.trans (hC.1 x.1.1).2.2⟩
  have hE₀ (x : X) : 1 ≤ E x :=
    hE _ (materialSample_mem_radialCore hT hpart (C.cell x.1.1))
  have hF (j : ℕ) : ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ x : X,
      |iteratedDeriv j (deriv (C.control x.1.1)) (point x)| ≤ B * 1 * E x ^ A := by
    obtain ⟨B, hB, hb⟩ := hA.2.2.2.2 (j + 1)
    exact ⟨B, B, hB, hB, fun x => by
      simpa only [← iteratedDeriv_succ', mul_one] using hb x.1.1 (point x) x.2⟩
  have hR (j : ℕ) : ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ x : X,
      |iteratedDeriv j (fun r : ℝ => r⁻¹) (point x)| ≤ B * 1 * E x ^ A := by
    obtain ⟨B, hB, hb⟩ := inverseRadius_iteratedDeriv_bound (b := D.b) hD.1 j
    refine ⟨B, 1, hB, zero_lt_one, fun x => ?_⟩
    simpa only [mul_one, Real.rpow_one] using
      (hb (point x) ⟨(hcore x).1.le, (hcore x).2.le⟩).trans
        (le_mul_of_one_le_right hB.le (hE₀ x))
  obtain ⟨B, A, hB, hA₀, hb⟩ := iteratedDeriv_mul_envelope_bound
    (fun _ : X => 1) E (fun _ => zero_le_one) hE₀ point
    (fun x => deriv (C.control x.1.1)) (fun (_ : X) (r : ℝ) => r⁻¹)
    (fun x => (contDiff_infty_iff_deriv.mp (hC.2.2.2.2.2.1 x.1.1).1).2.contDiffAt)
    (fun x => contDiffAt_id.inv (hD.1.trans (hcore x).1).ne') hF hR n
  refine ⟨B, A, hB, hA₀, fun m r hr => ?_⟩
  have he : controlOpticalFactor C m =
      (fun s : ℝ => deriv (C.control m) s * s⁻¹) := by
    funext s
    exact div_eq_mul_inv (deriv (C.control m) s) s
  have hbound := hb (⟨(m, r), hr⟩ : X)
  change |iteratedDeriv n (fun s : ℝ => deriv (C.control m) s * s⁻¹) r| ≤
    B * 1 * T.E0 (T.sample (C.cell m)) ^ A at hbound
  rw [he]
  simpa only [mul_one] using hbound

/-- All control-factor jets retain a full endpoint factor after the
radial derivative weight is inserted. The zero-order case uses the actual
vanishing endpoint jet; higher orders use only the bounded interval length. -/
theorem controlOpticalFactor_weighted_sample_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) (n : ℕ) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m r,
      r ∈ Ioo (C.left m) (C.right m) →
      min (r - C.left m) (C.right m - r) ^ n *
          |iteratedDeriv n (controlOpticalFactor C m) r| ≤
        B * T.E0 (T.sample (C.cell m)) ^ A *
          min (r - C.left m) (C.right m - r) := by
  have hD := hA.1.1.choose_spec.1
  have hC := hA.2.2.1
  cases n with
  | zero =>
      obtain ⟨B, hB, hb⟩ := n01_controlFirstJet_le_endpointDistance hT hA
      refine ⟨B / D.a, B, div_pos hB hD.1, hB, fun m r hr => ?_⟩
      have har : D.a < r := (hC.1 m).1.trans hr.1
      have hδ : 0 ≤ min (r - C.left m) (C.right m - r) :=
        (lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)).le
      have hs := materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m)
      have hp : 0 ≤ B * T.E0 (T.sample (C.cell m)) ^ B *
          min (r - C.left m) (C.right m - r) :=
        mul_nonneg (mul_nonneg hB.le
          (Real.rpow_nonneg (hT.2.1 _ hs).2.2.1.le _)) hδ
      simp only [pow_zero, one_mul, iteratedDeriv_zero, controlOpticalFactor,
        abs_div, abs_of_pos (hD.1.trans har)]
      calc
        _ ≤ (B * T.E0 (T.sample (C.cell m)) ^ B *
            min (r - C.left m) (C.right m - r)) / r :=
          div_le_div_of_nonneg_right (hb m r hr) (hD.1.trans har).le
        _ ≤ (B * T.E0 (T.sample (C.cell m)) ^ B *
            min (r - C.left m) (C.right m - r)) / D.a :=
          div_le_div_of_nonneg_left hp hD.1 har.le
        _ = _ := by ring
  | succ n =>
      obtain ⟨B, A, hB, hA₀, hb⟩ :=
        controlOpticalFactor_iteratedDeriv_sample_bound hT hA hE (n + 1)
      let L : ℝ := D.b - D.a
      have hL : 0 < L := sub_pos.mpr hD.2.1
      refine ⟨B * L ^ n, A, mul_pos hB (pow_pos hL n), hA₀, fun m r hr => ?_⟩
      let δ : ℝ := min (r - C.left m) (C.right m - r)
      have hδ : 0 ≤ δ := (lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)).le
      have hδL : δ ≤ L := by
        have hnear := min_le_left (r - C.left m) (C.right m - r)
        dsimp only [δ, L]
        linarith [(hC.1 m).1, (hC.1 m).2.2, hr.2]
      have hp : δ ^ n ≤ L ^ n := pow_le_pow_left₀ hδ hδL n
      have hs := materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m)
      have hEpos : 0 ≤ T.E0 (T.sample (C.cell m)) ^ A :=
        Real.rpow_nonneg (hT.2.1 _ hs).2.2.1.le _
      change δ ^ (n + 1) * _ ≤ _ * δ
      rw [pow_succ]
      calc
        _ ≤ (L ^ n * δ) * (B * T.E0 (T.sample (C.cell m)) ^ A) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hp hδ) (hb m r hr)
            (abs_nonneg _) (mul_nonneg (pow_nonneg hL.le _) hδ)
        _ = _ := by ring

/-- The actual optical square has an affine component formula as a germ,
so every radial jet is affine in the same decoded circle mean. -/
theorem n01_stateProfile_opticalSquare_iteratedDeriv_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hA : N01PartA D T S C)
    (x : AnnularState S) (m n : ℕ) {r : ℝ}
    (hr : r ∈ Ioo (C.left m) (C.right m)) :
    iteratedDeriv n
        (fun t => -deriv (stateProfile D S C x) t / (t * stateProfile D S C x t)) r =
      iteratedDeriv n (referenceOpticalSquare D) r -
        stateKappa S x m * iteratedDeriv n (controlOpticalFactor C m) r := by
  have hD := hA.1.1.choose_spec.1
  have hC := hA.2.2.1
  have hcore : r ∈ Ioo D.a D.b :=
    ⟨(hC.1 m).1.trans hr.1, hr.2.trans (hC.1 m).2.2⟩
  have he : (fun t => -deriv (stateProfile D S C x) t / (t * stateProfile D S C x t)) =ᶠ[𝓝 r]
      (fun t => referenceOpticalSquare D t - stateKappa S x m * controlOpticalFactor C m t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    simpa only [referenceOpticalSquare, controlOpticalFactor, mul_div_assoc] using
      n01_stateProfile_opticalSquare_eq hA x m ht
  rw [he.iteratedDeriv_eq n,
    iteratedDeriv_fun_sub ((referenceOpticalSquare_contDiffAt hD hcore).of_le (by simp))
      ((contDiffAt_const.mul (controlOpticalFactor_contDiffAt hD hC m hr)).of_le (by simp)),
    iteratedDeriv_const_mul_field]

/-- The reference optical square gains a true endpoint distance. The
first reference derivative vanishes at both original turning points. -/
theorem referenceOpticalSquare_endpoint_sample_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m)) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m r,
      r ∈ Ioo (C.left m) (C.right m) →
      |referenceOpticalSquare D r| ≤ B * T.E0 (T.sample (C.cell m)) ^ A *
        min (r - C.left m) (C.right m - r) := by
  have hD := hA.1.1.choose_spec.1
  have hC := hA.2.2.1
  have hd : ContDiff ℝ ∞ (deriv D.w) := (contDiff_infty_iff_deriv.mp hD.2.2.1.1).2
  have hdd : Continuous (fun r => |deriv (deriv D.w) r|) :=
    (contDiff_infty_iff_deriv.mp hd).2.continuous.abs
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc : IsCompact (Icc D.a D.b)).bddAbove_image hdd.continuousOn
  let M : ℝ := max 1 M₀
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  have hsecond (m : ℕ) (t : ℝ) (ht : t ∈ Icc (C.left m) (C.right m)) :
      ‖deriv (deriv D.w) t‖ ≤ M := by
    simpa only [Real.norm_eq_abs] using
      (hM₀ ⟨t, ⟨(hC.1 m).1.le.trans ht.1, ht.2.trans (hC.1 m).2.2.le⟩, rfl⟩).trans
        (le_max_right 1 M₀)
  have hfirst (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (C.left m) (C.right m)) :
      |deriv D.w r| ≤ M * min (r - C.left m) (C.right m - r) := by
    have hL := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun t (_ : t ∈ Icc (C.left m) (C.right m)) => hd.differentiable (by simp) t)
      (hsecond m) (convex_Icc (C.left m) (C.right m))
      (show C.left m ∈ Icc (C.left m) (C.right m) from ⟨le_rfl, (hC.1 m).2.1.le⟩)
      (Ioo_subset_Icc_self hr)
    have hR := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun t (_ : t ∈ Icc (C.left m) (C.right m)) => hd.differentiable (by simp) t)
      (hsecond m) (convex_Icc (C.left m) (C.right m))
      (show C.right m ∈ Icc (C.left m) (C.right m) from ⟨(hC.1 m).2.1.le, le_rfl⟩)
      (Ioo_subset_Icc_self hr)
    have hL' : |deriv D.w r| ≤ M * (r - C.left m) := by
      simpa only [(hC.2.1 m).1, sub_zero, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hr.1.le)] using hL
    have hR' : |deriv D.w r| ≤ M * (C.right m - r) := by
      simpa only [(hC.2.1 m).2.1, sub_zero, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr hr.2.le), neg_sub] using hR
    by_cases hnear : r - C.left m ≤ C.right m - r
    · simpa only [min_eq_left hnear] using hL'
    · simpa only [min_eq_right (le_of_not_ge hnear)] using hR'
  obtain ⟨B, A, hB, _, hb⟩ := referenceInverse_iteratedDeriv_le_E0 hT hA.1.1 hE 0
  obtain ⟨G, K, hG, hK, hg⟩ := materialCell_weight_comparison hT hA.1.1 0 A
  refine ⟨M * B * G / D.a, K, div_pos (mul_pos (mul_pos hM hB) hG) hD.1,
    hK, fun m r hr => ?_⟩
  have hcore : r ∈ Ioo D.a D.b :=
    ⟨(hC.1 m).1.trans hr.1, hr.2.trans (hC.1 m).2.2⟩
  have hrad : 0 < r := hD.1.trans hcore.1
  have hw : 0 < D.w r := hD.2.2.2.2.1 r hcore
  have hweight : T.E0 r ^ A ≤ G * T.E0 (T.sample (C.cell m)) ^ K := by
    simpa only [Real.rpow_zero, one_mul, mul_one] using (hg _ r (hloc m hr)).1
  have hinv : |(D.w r)⁻¹| ≤ (B * G) * T.E0 (T.sample (C.cell m)) ^ K := by
    calc
      _ ≤ B * T.E0 r ^ A := by simpa only [iteratedDeriv_zero] using hb _ r (hloc m hr)
      _ ≤ B * (G * T.E0 (T.sample (C.cell m)) ^ K) :=
        mul_le_mul_of_nonneg_left hweight hB.le
      _ = _ := by ring
  have hδ : 0 ≤ min (r - C.left m) (C.right m - r) :=
    (lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)).le
  have hrinv : |r⁻¹| ≤ D.a⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr hrad)]
    exact inv_anti₀ hD.1 hcore.1.le
  calc
    |referenceOpticalSquare D r| = |deriv D.w r| * |(D.w r)⁻¹| * |r⁻¹| := by
      simp only [referenceOpticalSquare, div_eq_mul_inv, mul_inv_rev, abs_mul, abs_neg]
      ring
    _ ≤ (M * min (r - C.left m) (C.right m - r)) *
        ((B * G) * T.E0 (T.sample (C.cell m)) ^ K) * D.a⁻¹ :=
      mul_le_mul
        (mul_le_mul (hfirst m r hr) hinv (abs_nonneg _) (mul_nonneg hM.le hδ))
        hrinv (abs_nonneg _) (mul_nonneg (mul_nonneg hM.le hδ)
          (abs_nonneg ((D.w r)⁻¹) |>.trans hinv))
    _ = _ := by ring

set_option backward.isDefEq.respectTransparency true

private abbrev opticalStateTopology (S : PhysicalSpacesData) :
    TopologicalSpace (AnnularState S) := inferInstance
attribute [local instance] opticalStateTopology
private abbrev opticalStateGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := inferInstance
attribute [local instance] opticalStateGroup
private abbrev opticalStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := inferInstance
attribute [local instance] opticalStateModule
private abbrev opticalStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) :=
  (opticalStateModule S).toDistribMulAction.toDistribSMul.toSMul
attribute [local instance] opticalStateSMul

/-- The original optical direction, including its exact radial jet and
circle-mean weight. The sample is the original designated component cell. -/
theorem stateOpticalDirection_weighted_sample_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) (n : ℕ) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m r,
      r ∈ Ioo (C.left m) (C.right m) → ∀ v : AnnularState S,
      min (r - C.left m) (C.right m - r) ^ n *
          |stateKappa S v m * iteratedDeriv n (controlOpticalFactor C m) r| ≤
        (B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ A) *
            min (r - C.left m) (C.right m - r) * stateGrading S 0 v :=
  exists_opticalDirection_envelope_bound
    (V := AnnularState S)
    (fun m => Ioo (C.left m) (C.right m))
    (fun m r => min (r - C.left m) (C.right m - r))
    (fun m r => iteratedDeriv n (controlOpticalFactor C m) r)
    (stateKappa S) (stateGrading S 0)
    (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ))
    (fun m => T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ))
    (fun m => T.E0 (T.sample (C.cell m)))
    ((1 / Real.pi) * Real.sqrt Real.pi)
    (mul_pos (div_pos zero_lt_one Real.pi_pos) (Real.sqrt_pos.mpr Real.pi_pos))
    (fun v => apply_nonneg (stateGrading S 0) v)
    (fun m => Real.rpow_nonneg
      (hT.2.1 _ (materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 m)).2.1.le _)
    (fun m r hr => (lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)).le)
    (fun v m => abs_stateKappa_le_weight_mul_stateGrading hS hT hA.1.1 v 0 m)
    (by
      intro A
      obtain ⟨J, hJ, hj⟩ := hA.2.2.2.1
      obtain ⟨C₀, K, hC₀, hK, hw⟩ :=
        materialSample_weight_bound_sameExponent hT hA.1.1 (3 / 4 : ℝ) A hJ.le
      have hs : ∀ j, T.sample j ∈ D.cells j := by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs, _⟩ := hT
        exact hs
      exact ⟨C₀, K, hC₀, hK, fun m =>
        hw m (C.cell m) (T.sample (C.cell m)) (hs (C.cell m))
          ((abs_sub_comm _ _).trans_le (hj m))⟩)
    n (controlOpticalFactor_weighted_sample_bound hT hA hE n)

/-- The actual optical square-root family has all parameter derivatives
on the same positive open state set. The square is affine in the original
decoded control mean, with no substituted profile or control family. -/
def stateOpticalRootSmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (m : ℕ) (r : ℝ)
    (hr : r ∈ Ioo (C.left m) (C.right m))
    {U : Set (AnnularState S)} (hU : IsOpen U)
    (hpos : ∀ x ∈ U,
      0 < -deriv (stateProfile D S C x) r / (r * stateProfile D S C x r)) :
    SmoothDirections U (fun x : AnnularState S =>
      Real.sqrt (-deriv (stateProfile D S C x) r / (r * stateProfile D S C x r))) := by
  let L : AnnularState S →L[ℝ] ℝ :=
    (-controlOpticalFactor C m r) • stateKappaCLM hS hT hA.1.1 m
  have he (x : AnnularState S) : referenceOpticalSquare D r + L x =
      -deriv (stateProfile D S C x) r / (r * stateProfile D S C x r) := by
    rw [n01_stateProfile_opticalSquare_eq hA x m hr]
    simp only [L, smul_apply, smul_eq_mul, stateKappaCLM_apply,
      referenceOpticalSquare, controlOpticalFactor]
    ring
  let J := smoothDirections_affineSqrt (referenceOpticalSquare D r) L hU
    (fun x hx => (he x).symm ▸ hpos x hx)
  exact J.congr (fun x _ => congrArg Real.sqrt (he x))

/-- The exact positive-parameter factors of the actual optical root.
Every direction is the original mean multiplied by the original control jet. -/
theorem stateOpticalRootSmoothDirections_D_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (m : ℕ) (r : ℝ)
    (hr : r ∈ Ioo (C.left m) (C.right m))
    {U : Set (AnnularState S)} (hU : IsOpen U)
    (hpos : ∀ x ∈ U,
      0 < -deriv (stateProfile D S C x) r / (r * stateProfile D S C x r))
    (k : ℕ) (x : AnnularState S) (v : Fin k → AnnularState S) :
    (stateOpticalRootSmoothDirections hS hT hA m r hr hU hpos).D k x v =
      rpowJetCoefficient (1 / 2) k *
        (-deriv (stateProfile D S C x) r / (r * stateProfile D S C x r)) ^
          ((1 / 2 : ℝ) - (k : ℝ)) *
            ∏ i, (-controlOpticalFactor C m r) * stateKappa S (v i) m := by
  let L : AnnularState S →L[ℝ] ℝ :=
    (-controlOpticalFactor C m r) • stateKappaCLM hS hT hA.1.1 m
  have hq : referenceOpticalSquare D r + L x =
      -deriv (stateProfile D S C x) r / (r * stateProfile D S C x r) := by
    rw [n01_stateProfile_opticalSquare_eq hA x m hr]
    simp only [L, smul_apply, smul_eq_mul, stateKappaCLM_apply,
      referenceOpticalSquare, controlOpticalFactor]
    ring
  have hv (i : Fin k) : L (v i) =
      (-controlOpticalFactor C m r) * stateKappa S (v i) m := by
    simp only [L, smul_apply, smul_eq_mul, stateKappaCLM_apply]
  change affineRpowJets (1 / 2) (referenceOpticalSquare D r) L k x v = _
  exact affineRpowJets_apply_of_values (1 / 2) (referenceOpticalSquare D r) L k x v
    _ _ hq hv

/-- All reference optical jets have the endpoint gain after radial weighting. -/
theorem referenceOpticalSquare_weighted_sample_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m)) (n : ℕ) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m r,
      r ∈ Ioo (C.left m) (C.right m) →
      min (r - C.left m) (C.right m - r) ^ n *
          |iteratedDeriv n (referenceOpticalSquare D) r| ≤
        B * T.E0 (T.sample (C.cell m)) ^ A * min (r - C.left m) (C.right m - r) := by
  cases n with
  | zero => simpa only [pow_zero, one_mul, iteratedDeriv_zero] using
      referenceOpticalSquare_endpoint_sample_bound hT hA hE hloc
  | succ n =>
      obtain ⟨B, A, hB, hA₀, hb⟩ := referenceOpticalSquare_iteratedDeriv_sample_bound hT hA.1.1 hE (n + 1)
      have hD := hA.1.1.choose_spec.1
      have hC := hA.2.2.1
      have hL : 0 < D.b - D.a := sub_pos.mpr hD.2.1
      refine ⟨B * (D.b - D.a) ^ n, A, mul_pos hB (pow_pos hL n), hA₀, fun m r hr => ?_⟩
      let δ : ℝ := min (r - C.left m) (C.right m - r)
      have hδ : 0 ≤ δ := (lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)).le
      have hδL : δ ≤ D.b - D.a := by
        have hh := min_le_left (r - C.left m) (C.right m - r)
        dsimp only [δ]; linarith [(hC.1 m).1, (hC.1 m).2.2, hr.2]
      change δ ^ (n + 1) * _ ≤ _ * δ
      rw [pow_succ]
      calc
        _ ≤ ((D.b - D.a) ^ n * δ) * (B * T.E0 (T.sample (C.cell m)) ^ A) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hδ hδL n) hδ)
            (hb _ r (hloc m hr)) (abs_nonneg _)
            (mul_nonneg (pow_nonneg hL.le _) hδ)
        _ = _ := by ring

/-- The actual perturbed optical square, at every radial order. This raw
bound uses only the level-zero state factor; the common ball bounds it uniformly. -/
theorem stateOpticalSquare_weighted_sample_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m)) (n : ℕ) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m r,
      r ∈ Ioo (C.left m) (C.right m) → ∀ x : AnnularState S,
      min (r - C.left m) (C.right m - r) ^ n *
          |iteratedDeriv n (fun t => -deriv (stateProfile D S C x) t /
            (t * stateProfile D S C x t)) r| ≤
        (B * T.E0 (T.sample (C.cell m)) ^ A) *
          min (r - C.left m) (C.right m - r) * (1 + stateGrading S 0 x) :=
  exists_opticalSquare_envelope_bound
    (V := AnnularState S)
    (fun m => Ioo (C.left m) (C.right m))
    (fun m r => min (r - C.left m) (C.right m - r))
    (fun _ r x => iteratedDeriv n (fun t =>
      -deriv (stateProfile D S C x) t / (t * stateProfile D S C x t)) r)
    (fun _ r => iteratedDeriv n (referenceOpticalSquare D) r)
    (fun m r => iteratedDeriv n (controlOpticalFactor C m) r)
    (stateKappa S) (stateGrading S 0)
    (fun m => T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ))
    (fun m => T.E0 (T.sample (C.cell m)))
    (fun v => apply_nonneg (stateGrading S 0) v)
    (fun m => hE _ (materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m)))
    (fun m r hr => (lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)).le)
    (fun m r hr x => n01_stateProfile_opticalSquare_iteratedDeriv_eq hA x m n hr)
    (by
      intro K
      obtain ⟨M, hM, hm⟩ :=
        materialHeight_E0_weight_bounded hT (γ := (3 / 4 : ℝ)) (by norm_num) K
      exact ⟨M, hM, fun m =>
        hm _ (materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m))⟩)
    n (referenceOpticalSquare_weighted_sample_bound hT hA hE hloc n)
    (stateOpticalDirection_weighted_sample_bound hS hT hA hE n)

end ContinuousFlexibility.Statements
