module

public import ContinuousFlexibility.Analysis.N06CurrentJetBounds
public import ContinuousFlexibility.Radial.ReferenceCellL2

/-!
# Actual coefficient differences on a fixed compact radial set

The original profile partition covers every radial core point. Its own
compact finiteness turns the proved N01 weighted coefficient estimate
into one fixed seminorm bound on any compact radial support. No atlas
comparison, current chart regularity, or proposed operator estimate is
an input.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped BigOperators

set_option backward.isDefEq.respectTransparency true

def N06CompactCoefficientDifferenceBound
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε : ℝ) (J : Set ℝ) (s : ℕ) (Q : ℝ) : Prop :=
  ∀ (i : Fin 3) a b (p : PolarPoint), a + b ≤ s → p.1 ∈ J →
    ∀ z ∈ stateNeighborhood S C base ε,
      stateGrading S base (z.1 - C.referenceState) + |z.2| ≤ 1 →
      |coefficientFamily D S C i a b p z| ≤ Q *
        (stateGrading S (max base (s + loss)) (z.1 - C.referenceState) + |z.2|)

private theorem n06_profile_compact_coefficient_cover
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {J : Set ℝ} (hJ : IsCompact J) (hJD : J ⊆ radialCore D) :
    {m : ℕ | (D.cells m ∩ J).Nonempty}.Finite ∧
      ∀ r ∈ J, ∃ m, r ∈ D.cells m := by
  have hprofile := hD.choose_spec
  have hpartition : RadialPartition D := hprofile.2.1
  refine ⟨hprofile.2.2.2.2.2.1 J hJ hJD, ?_⟩
  intro r hr
  obtain ⟨m, hm⟩ := hpartition.exists_localizer_ne_zero (hJD hr)
  exact ⟨m, hpartition.2.2.1 m hm⟩

private theorem n06_compact_scalar_family_bound
    {Z : Type*} (cells : ℕ → Set ℝ) (J : Set ℝ) (s : ℕ)
    (family : Fin 3 → ℕ → ℕ → PolarPoint → Z → ℝ)
    (size : Z → ℝ) (Ad₁ Ad₂ : Z → Prop) (weight : ℝ → ℕ → ℝ)
    (hfinite : {m : ℕ | (cells m ∩ J).Nonempty}.Finite)
    (hcover : ∀ r ∈ J, ∃ m, r ∈ cells m) (hsize : ∀ z, 0 ≤ size z)
    (hbound : ∃ B : ℝ, 0 < B ∧ ∀ m i a b (p : PolarPoint),
      a + b ≤ s → p.1 ∈ cells m → ∀ z, Ad₁ z → Ad₂ z →
      |family i a b p z| ≤ weight B m * size z) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ i a b (p : PolarPoint),
      a + b ≤ s → p.1 ∈ J → ∀ z, Ad₁ z → Ad₂ z →
      |family i a b p z| ≤ Q * size z := by
  classical
  obtain ⟨B, _hB, hactual⟩ := hbound
  let I : Finset ℕ := hfinite.toFinset
  let Q : ℝ := ∑ m ∈ I, |weight B m|
  refine ⟨Q, Finset.sum_nonneg (fun m _ => abs_nonneg (weight B m)), ?_⟩
  intro i a b p hab hp z hz₁ hz₂
  obtain ⟨m, hpm⟩ := hcover p.1 hp
  have hmI : m ∈ I := hfinite.mem_toFinset.mpr ⟨p.1, hpm, hp⟩
  have hweight : weight B m ≤ Q := (le_abs_self (weight B m)).trans
    (Finset.single_le_sum (fun k _ => abs_nonneg (weight B k)) hmI)
  exact (hactual m i a b p hab hpm z hz₁ hz₂).trans
    (mul_le_mul_of_nonneg_right hweight (hsize z))

theorem n06_N01_compactCoefficientDifference_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    {J : Set ℝ} (hJ : IsCompact J) (hJD : J ⊆ radialCore D) (s : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧
      N06CompactCoefficientDifferenceBound D S C base loss ε J s Q := by
  obtain ⟨hfinite, hcover⟩ := n06_profile_compact_coefficient_cover h01.1.1 hJ hJD
  exact n06_compact_scalar_family_bound (Z := AnnularState S × ℝ)
    D.cells J s (coefficientFamily D S C)
    (fun z => stateGrading S (max base (s + loss)) (z.1 - C.referenceState) + |z.2|)
    (fun z => z ∈ stateNeighborhood S C base ε)
    (fun z => stateGrading S base (z.1 - C.referenceState) + |z.2| ≤ 1)
    (fun B m => 3 * (B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B))
    hfinite hcover
    (fun z => add_nonneg
      (apply_nonneg (stateGrading S (max base (s + loss))) (z.1 - C.referenceState))
      (abs_nonneg z.2))
    (n06_N01_currentCoefficient_bound hT h01 s)

end ContinuousFlexibility.Statements
