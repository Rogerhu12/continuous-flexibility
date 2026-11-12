import ContinuousFlexibility.Analysis.N05CanonicalGraphDensity

/-!
# A dense common core for every canonical volume level

A genuine smooth single-cell test has realizations at every finite
angular order. A scalar ratio of the two positive sample weights makes
their forgotten physical sequence identical. The intersection of all
such actual ranges is a submodule containing the smooth graph core,
hence it is dense in each canonical volume level.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

def n05CanonicalAllLevelCore (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γ t : ℝ) (s : ℕ) :
    Submodule ℝ (n05CanonicalClosedSubmodule S K s) :=
  ⨅ (γ' : ℝ) (t' : ℝ) (s' : ℕ),
    ((n05CanonicalVolumeModel T S K).forget γ' t' s').range.comap
      ((n05CanonicalVolumeModel T S K).forget γ t s)

set_option backward.isDefEq.respectTransparency false in
theorem n05CanonicalAllLevelCore_mem_iff (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γ t : ℝ) (s : ℕ) (v : n05CanonicalClosedSubmodule S K s) :
    v ∈ n05CanonicalAllLevelCore T S K γ t s ↔
      ∀ (γ' t' : ℝ) (s' : ℕ), VolumeMember S K (n05CanonicalVolumeModel T S K) γ' t' s'
        ((n05CanonicalVolumeModel T S K).forget γ t s v) := by
  simp only [n05CanonicalAllLevelCore, Submodule.mem_iInf]
  constructor
  · intro hv γ' t' s'
    have hmem : (n05CanonicalVolumeModel T S K).forget γ t s v ∈
        ((n05CanonicalVolumeModel T S K).forget γ' t' s').range :=
      (Submodule.mem_comap
        (f := (n05CanonicalVolumeModel T S K).forget γ t s)
        (p := ((n05CanonicalVolumeModel T S K).forget γ' t' s').range)).mp (hv γ' t' s')
    exact (LinearMap.mem_range
      (f := (n05CanonicalVolumeModel T S K).forget γ' t' s')).mp hmem
  · intro hv γ' t' s'
    exact (Submodule.mem_comap
      (f := (n05CanonicalVolumeModel T S K).forget γ t s)
      (p := ((n05CanonicalVolumeModel T S K).forget γ' t' s').range)).mpr
        ((LinearMap.mem_range
          (f := (n05CanonicalVolumeModel T S K).forget γ' t' s')).mpr (hv γ' t' s'))

theorem n05CanonicalSmoothSingle_forget (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γ t : ℝ) (m s : ℕ)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ)
    (he : ∀ p : PolarPoint, φ (p.1, Real.pi - p.2) = φ p) :
    (n05CanonicalVolumeModel T S K).forget γ t s
      (n05CanonicalSmoothSingle S K m s hφ.1 hφ.2.1 he) m =
        n05CanonicalSampleWeight T S K γ t m • n05CanonicalTestL2 hφ := by
  refine (n05CanonicalVolumeModel_forget T S K γ t s
    (n05CanonicalSmoothSingle S K m s hφ.1 hφ.2.1 he) m).trans ?_
  simpa only [n05CanonicalSampleWeight] using
    congrArg (fun z : CanonicalL2 S K m => n05CanonicalSampleWeight T S K γ t m • z)
      (n05CanonicalSmoothSingle_zero_test hφ he s)

theorem n05CanonicalSmoothSingle_forget_ne (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γ t : ℝ) (m s : ℕ)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ)
    (he : ∀ p : PolarPoint, φ (p.1, Real.pi - p.2) = φ p) {l : ℕ} (hl : l ≠ m) :
    (n05CanonicalVolumeModel T S K).forget γ t s
      (n05CanonicalSmoothSingle S K m s hφ.1 hφ.2.1 he) l = 0 := by
  refine (n05CanonicalVolumeModel_forget T S K γ t s
    (n05CanonicalSmoothSingle S K m s hφ.1 hφ.2.1 he) l).trans ?_
  change (T.M (T.sample (K.cell l)) ^ (-t) * T.H (T.sample (K.cell l)) ^ γ) •
    n05CanonicalSmoothSingleRaw S K m s hφ.1 l 0 = 0
  rw [n05CanonicalSmoothSingleRaw_ne S K m s hφ.1 hl, smul_zero]

theorem n05CanonicalSmoothSingle_allLevelMember {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hPart : RadialPartition D) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γ t γ' t' : ℝ) (m s r : ℕ)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ)
    (he : ∀ p : PolarPoint, φ (p.1, Real.pi - p.2) = φ p) :
    VolumeMember S K (n05CanonicalVolumeModel T S K) γ' t' r
      ((n05CanonicalVolumeModel T S K).forget γ t s
        (n05CanonicalSmoothSingle S K m s hφ.1 hφ.2.1 he)) := by
  have hf : ContDiff ℝ ∞ φ := hφ.1
  have hp : Function.Periodic φ (0, Real.pi) := hφ.2.1
  change ∃ v : n05CanonicalClosedSubmodule S K r,
    (n05CanonicalVolumeModel T S K).forget γ' t' r v =
      (n05CanonicalVolumeModel T S K).forget γ t s
        (n05CanonicalSmoothSingle S K m s hf hp he)
  let c : ℝ := n05CanonicalSampleWeight T S K γ t m /
    n05CanonicalSampleWeight T S K γ' t' m
  refine ⟨c • n05CanonicalSmoothSingle S K m r hf hp he, ?_⟩
  refine (map_smul ((n05CanonicalVolumeModel T S K).forget γ' t' r) c
    (n05CanonicalSmoothSingle S K m r hf hp he)).trans ?_
  funext l
  change c • ((n05CanonicalVolumeModel T S K).forget γ' t' r
    (n05CanonicalSmoothSingle S K m r hf hp he) l) =
      (n05CanonicalVolumeModel T S K).forget γ t s
        (n05CanonicalSmoothSingle S K m s hf hp he) l
  by_cases hl : l = m
  · subst l
    have hleft : (n05CanonicalVolumeModel T S K).forget γ' t' r
        (n05CanonicalSmoothSingle S K m r hf hp he) m =
          n05CanonicalSampleWeight T S K γ' t' m • n05CanonicalTestL2 hφ :=
      n05CanonicalSmoothSingle_forget T S K γ' t' m r hφ he
    have hright : (n05CanonicalVolumeModel T S K).forget γ t s
        (n05CanonicalSmoothSingle S K m s hf hp he) m =
          n05CanonicalSampleWeight T S K γ t m • n05CanonicalTestL2 hφ :=
      n05CanonicalSmoothSingle_forget T S K γ t m s hφ he
    rw [hleft, hright, smul_smul]
    apply congrArg (fun z : ℝ => z • n05CanonicalTestL2 hφ)
    exact div_mul_cancel₀ _ (n05CanonicalSampleWeight_pos hT hPart S K γ' t' m).ne'
  · have hleft : (n05CanonicalVolumeModel T S K).forget γ' t' r
        (n05CanonicalSmoothSingle S K m r hf hp he) l = 0 :=
      n05CanonicalSmoothSingle_forget_ne T S K γ' t' m r hφ he hl
    have hright : (n05CanonicalVolumeModel T S K).forget γ t s
        (n05CanonicalSmoothSingle S K m s hf hp he) l = 0 :=
      n05CanonicalSmoothSingle_forget_ne T S K γ t m s hφ he hl
    rw [hleft, hright, smul_zero]

theorem n05CanonicalSmoothSingle_mem_allLevelCore {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hPart : RadialPartition D) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γ t : ℝ) (m s : ℕ)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ)
    (he : ∀ p : PolarPoint, φ (p.1, Real.pi - p.2) = φ p) :
    n05CanonicalSmoothSingle S K m s hφ.1 hφ.2.1 he ∈ n05CanonicalAllLevelCore T S K γ t s := by
  apply (n05CanonicalAllLevelCore_mem_iff T S K γ t s _).mpr
  intro γ' t' r
  exact n05CanonicalSmoothSingle_allLevelMember hT hPart S K γ t γ' t' m s r hφ he

theorem n05CanonicalSmoothCore_le_allLevelCore {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hPart : RadialPartition D) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γ t : ℝ) (s : ℕ) :
    n05CanonicalSmoothCoreSubmodule S K s ≤ n05CanonicalAllLevelCore T S K γ t s := by
  apply Submodule.span_le.mpr
  rintro v ⟨m, φ, hφ, he, rfl⟩
  exact n05CanonicalSmoothSingle_mem_allLevelCore hT hPart S K γ t m s hφ he

theorem n05CanonicalAllLevelCore_dense {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hPart : RadialPartition D) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γ t : ℝ) (s : ℕ) :
    Dense (n05CanonicalAllLevelCore T S K γ t s : Set (n05CanonicalClosedSubmodule S K s)) :=
  (n05CanonicalSmoothCoreSubmodule_dense S K s).mono
    (n05CanonicalSmoothCore_le_allLevelCore hT hPart S K γ t s)

end ContinuousFlexibility.Statements
