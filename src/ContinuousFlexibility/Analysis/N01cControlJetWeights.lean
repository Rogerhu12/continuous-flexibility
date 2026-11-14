module

public import ContinuousFlexibility.Analysis.N01cStateProfileProductBounds
public import ContinuousFlexibility.Analysis.N01cShiftedSampleWeights
public import ContinuousFlexibility.Analysis.StateControlDecay

/-!
# Pointwise material bounds for the actual profile exponent jets

The scalar border contribution is controlled on its genuine compact
support.  Pairwise disjoint control components reduce every finite
control-jet majorant to at most one active summand.  The component's
physical placement then permits the bounded-index material comparison.

The two placement hypotheses below are explicit inputs.  They are not
consequences asserted for the present definition of N01PartA.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology

/-- A smooth compactly supported scalar function has every ordinary jet
bounded by any continuous positive weight on an open region containing
its closed support. -/
theorem abs_iteratedDeriv_le_weight_of_compactSupport
    {f W : ℝ → ℝ} {U : Set ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ U) (hW : ContinuousOn W U)
    (hWpos : ∀ r ∈ U, 0 < W r) (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ r ∈ U, |iteratedDeriv n f r| ≤ B * W r := by
  have hratio : ContinuousOn (fun r => |iteratedDeriv n f r| / W r) (tsupport f) :=
    (hf.continuous_iteratedDeriv n (by simp)).abs.continuousOn.div
      (hW.mono hs) (fun r hr => (hWpos r (hs hr)).ne')
  obtain ⟨B₀, hB₀⟩ := hc.bddAbove_image hratio
  let B : ℝ := max 1 B₀
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨B, hB, fun r hr => ?_⟩
  by_cases hrf : r ∈ tsupport f
  · apply (div_le_iff₀ (hWpos r hr)).mp
    exact (hB₀ ⟨r, hrf, rfl⟩).trans (le_max_right _ _)
  · have he : f =ᶠ[𝓝 r] (0 : ℝ → ℝ) :=
      notMem_tsupport_iff_eventuallyEq.mp hrf
    have hz : iteratedDeriv n f r = 0 := by
      simpa only [iteratedDeriv_const_zero] using he.iteratedDeriv_eq n
    rw [hz, abs_zero]
    exact mul_nonneg hB.le (hWpos r hr).le

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

/-- Compactly supported scalar jets have the exact requested height
exponent.  No endpoint comparison or loss in that exponent is needed. -/
theorem compactScalarJet_materialWeight_bound
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioo D.a D.b) (γ A : ℝ) (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv n f r| ≤ B * T.H r ^ γ * T.E0 r ^ A := by
  have hH := (hT.1 T.H (by simp)).rpow_const_of_ne
    (fun r hr => (hT.2.1 r hr).2.1.ne') (p := γ)
  have hE := (hT.1 T.E0 (by simp)).rpow_const_of_ne
    (fun r hr => (hT.2.1 r hr).2.2.1.ne') (p := A)
  obtain ⟨B, hB, hbound⟩ := abs_iteratedDeriv_le_weight_of_compactSupport
    hf hc hs (hH.mul hE).continuousOn
    (fun r hr => mul_pos (Real.rpow_pos_of_pos (hT.2.1 r hr).2.1 γ)
      (Real.rpow_pos_of_pos (hT.2.1 r hr).2.2.1 A)) n
  exact ⟨B, hB, fun r hr => by simpa only [mul_assoc] using hbound r hr⟩

/-- Disjoint open components remove any dependence on the number of
indices in a local finite representation.  Endpoint jets vanish as well. -/
theorem finite_controlJetMajorant_le
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C)
    (I : Finset ℕ) (w : ℕ → ℝ) (n : ℕ) {r W : ℝ} (hW : 0 ≤ W)
    (hterm : ∀ m, r ∈ Ioo (C.left m) (C.right m) →
      |iteratedDeriv n (C.control m) r| * w m ≤ W) :
    (∑ m ∈ I, |iteratedDeriv n (C.control m) r| * w m) ≤ W := by
  classical
  obtain ⟨_, _, hdisjoint, _, _, hcontrol, _⟩ := hC
  by_cases h : ∃ m ∈ I, r ∈ Ioo (C.left m) (C.right m)
  · obtain ⟨m, hm, hmr⟩ := h
    rw [Finset.sum_eq_single_of_mem m hm]
    · exact hterm m hmr
    · intro i _ hi
      have hnot : r ∉ Ioo (C.left i) (C.right i) := fun hir =>
        Set.disjoint_left.mp (hdisjoint i m hi) hir hmr
      rw [iteratedDeriv_zero_off_open_interval (hcontrol i).1
        ((subset_tsupport (C.control i)).trans (hcontrol i).2.2) n hnot, abs_zero, zero_mul]
  · have hz : (∑ m ∈ I, |iteratedDeriv n (C.control m) r| * w m) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hnot : r ∉ Ioo (C.left m) (C.right m) := fun hmr => h ⟨m, hm, hmr⟩
      rw [iteratedDeriv_zero_off_open_interval (hcontrol m).1
        ((subset_tsupport (C.control m)).trans (hcontrol m).2.2) n hnot, abs_zero, zero_mul]
    rwa [hz]

/-- An original control derivative times its original decoded-mean
weight, transferred to the actual evaluation radius.  Physical component
placement is a separate hypothesis, not part of the input Part A bundle. -/
theorem controlJet_stateKappaWeight_material_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m)) (n : ℕ) :
    ∃ B K : ℝ, 0 < B ∧ 0 < K ∧ ∀ m r,
      r ∈ Ioo (C.left m) (C.right m) →
      |iteratedDeriv n (C.control m) r| * stateKappaSeminormWeight T m ≤
        B * T.H r ^ (3 / 4 : ℝ) * T.E0 r ^ K := by
  obtain ⟨B₀, hB₀, hindex⟩ := hA.2.2.2.1
  obtain ⟨J, hJ, hcontrol⟩ := hA.2.2.2.2 n
  obtain ⟨B₁, K, hB₁, hK, hweight⟩ :=
    materialSample_weight_bound_sameExponent hT hA.1.1 (3 / 4 : ℝ) J hB₀.le
  let c : ℝ := (1 / Real.pi) * Real.sqrt Real.pi
  have hc : 0 < c := mul_pos (div_pos zero_lt_one Real.pi_pos)
    (Real.sqrt_pos.2 Real.pi_pos)
  refine ⟨(J * c) * B₁, K, mul_pos (mul_pos hJ hc) hB₁, hK, fun m r hr => ?_⟩
  have hi : |(D.cellIndex m : ℝ) - D.cellIndex (C.cell m)| ≤ B₀ := by
    simpa only [abs_sub_comm] using hindex m
  calc
    |iteratedDeriv n (C.control m) r| * stateKappaSeminormWeight T m ≤
        (J * T.E0 (T.sample (C.cell m)) ^ J) * stateKappaSeminormWeight T m :=
      mul_le_mul_of_nonneg_right (hcontrol m r hr)
        (stateKappaSeminormWeight_nonneg hT hA.1.1 m)
    _ = (J * c) *
        (T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ J) := by
      dsimp only [stateKappaSeminormWeight, c]
      ring
    _ ≤ (J * c) * (B₁ * T.H r ^ (3 / 4 : ℝ) * T.E0 r ^ K) :=
      mul_le_mul_of_nonneg_left (hweight m (C.cell m) r (hloc m hr) hi)
        (mul_pos hJ hc).le
    _ = ((J * c) * B₁) * T.H r ^ (3 / 4 : ℝ) * T.E0 r ^ K := by ring

/-- The actual finite exponent-jet majorant has a uniform material bound.
The closed support of the border is explicitly placed inside the core,
as retained by the shared strict-support geometry. -/
theorem stateProfileExponentJetMajorant_material_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b) (n : ℕ) :
    ∃ B K : ℝ, 0 < B ∧ 0 < K ∧ ∀ r (hr : r ∈ Ioo D.a D.b),
      stateProfileExponentJetMajorant D T C hA.2.2.1 n r hr ≤
        B * T.H r ^ (3 / 4 : ℝ) * T.E0 r ^ K := by
  obtain ⟨B₀, K, hB₀, hK, hcontrol⟩ :=
    controlJet_stateKappaWeight_material_bound hT hA hloc n
  have hborder : RadialTrueBorder D := hA.1.2.2.2.1
  obtain ⟨B₁, hB₁, hborderBound⟩ := compactScalarJet_materialWeight_bound
    hT hborder.1 hborder.2.1 hχloc (3 / 4 : ℝ) K n
  refine ⟨B₁ + B₀, K, add_pos hB₁ hB₀, hK, fun r hr => ?_⟩
  have hweight : 0 ≤ B₀ * T.H r ^ (3 / 4 : ℝ) * T.E0 r ^ K :=
    mul_nonneg (mul_nonneg hB₀.le (Real.rpow_nonneg (hT.2.1 r hr).2.1.le _))
      (Real.rpow_nonneg (hT.2.1 r hr).2.2.1.le _)
  have hsum := finite_controlJetMajorant_le hA.2.2.1
    (stateControlLocalIndices hA.2.2.1 r hr) (stateKappaSeminormWeight T) n
    hweight (fun m hm => hcontrol m r hm)
  calc
    stateProfileExponentJetMajorant D T C hA.2.2.1 n r hr ≤
        B₁ * T.H r ^ (3 / 4 : ℝ) * T.E0 r ^ K +
          B₀ * T.H r ^ (3 / 4 : ℝ) * T.E0 r ^ K :=
      add_le_add (hborderBound r hr) hsum
    _ = (B₁ + B₀) * T.H r ^ (3 / 4 : ℝ) * T.E0 r ^ K := by ring

private theorem exists_bound_mul_nonneg
    {X : Type*} (U : Set ℝ)
    (f : ∀ r, r ∈ U → X → ℝ) (p : X → ℝ)
    (P : ∀ r, r ∈ U → ℝ) (W : ℝ → ℝ → ℝ → ℝ)
    (hp : ∀ x, 0 ≤ p x)
    (hf : ∀ r hr x, |f r hr x| ≤ P r hr * p x)
    (hP : ∃ B K : ℝ, 0 < B ∧ 0 < K ∧ ∀ r hr, P r hr ≤ W B K r) :
    ∃ B K : ℝ, 0 < B ∧ 0 < K ∧
      ∀ r hr x, |f r hr x| ≤ W B K r * p x := by
  obtain ⟨B, K, hB, hK, hbound⟩ := hP
  exact ⟨B, K, hB, hK, fun r hr x =>
    (hf r hr x).trans (mul_le_mul_of_nonneg_right (hbound r hr) (hp x))⟩

private abbrev controlWeightStateTopology (S : PhysicalSpacesData) :
    TopologicalSpace (AnnularState S) := inferInstance
attribute [local instance] controlWeightStateTopology

private abbrev controlWeightStateGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := inferInstance
attribute [local instance] controlWeightStateGroup

private abbrev controlWeightStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := inferInstance
attribute [local instance] controlWeightStateModule

private abbrev controlWeightStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) :=
  (controlWeightStateModule S).toDistribMulAction.toDistribSMul.toSMul
attribute [local instance] controlWeightStateSMul

/-- The bound is an estimate for the actual continuous linear exponent
jet at the original level-zero grading, uniformly over all states. -/
theorem stateProfileExponentJetCLM_material_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b) (n : ℕ) :
    ∃ B K : ℝ, 0 < B ∧ 0 < K ∧ ∀ r (hr : r ∈ Ioo D.a D.b)
      (x : AnnularState S),
      |stateProfileExponentJetCLM hS hT hA.1.1 hA.2.2.1 n r hr x| ≤
        (B * T.H r ^ (3 / 4 : ℝ) * T.E0 r ^ K) * stateGrading S 0 x :=
  exists_bound_mul_nonneg (X := AnnularState S) (Ioo D.a D.b)
    (fun r hr x => stateProfileExponentJetCLM hS hT hA.1.1 hA.2.2.1 n r hr x)
    (fun x => stateGrading S 0 x)
    (fun r hr => stateProfileExponentJetMajorant D T C hA.2.2.1 n r hr)
    (fun B K r => B * T.H r ^ (3 / 4 : ℝ) * T.E0 r ^ K)
    (fun x => apply_nonneg (stateGrading S 0) x)
    (fun r hr x => abs_stateProfileExponentJetCLM_le hS hT hA.1.1 hA.2.2.1 n r hr x)
    (stateProfileExponentJetMajorant_material_bound hT hA hloc hχloc n)

end ContinuousFlexibility.Statements
