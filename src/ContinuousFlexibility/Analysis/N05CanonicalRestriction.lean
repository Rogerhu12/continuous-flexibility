module

public import ContinuousFlexibility.Analysis.N05CanonicalEmbeddings

/-!
# Forgetting angular derivatives in the actual canonical volume model

The restriction retains the initial angular coordinates on every piece.
It is a contraction for the finite Hilbert products and hence for the
outer Hilbert sequence. Its zero coordinate is unchanged, so it commutes
with the prescribed weighted forget maps.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators Topology

def n05CanonicalJetIndexOfLE {s r : ℕ} (hsr : s ≤ r) :
    Fin (s + 1) ↪ Fin (r + 1) where
  toFun := Fin.castLE (Nat.succ_le_succ hsr)
  inj' := by
    intro j k hjk
    apply Fin.ext
    exact congrArg (fun a : Fin (r + 1) => a.val) hjk

@[simp] theorem n05CanonicalJetIndexOfLE_val {s r : ℕ} (hsr : s ≤ r)
    (j : Fin (s + 1)) : (n05CanonicalJetIndexOfLE hsr j).val = j.val := rfl

@[simp] theorem n05CanonicalJetIndexOfLE_zero {s r : ℕ} (hsr : s ≤ r) :
    n05CanonicalJetIndexOfLE hsr 0 = 0 :=
  Fin.castLE_zero (Nat.succ_le_succ hsr)

def n05CanonicalJetRestrictCoordinate (S : PhysicalSpacesData) (K : CanonicalData S)
    {s r : ℕ} (hsr : s ≤ r) (m : ℕ) :
    PiLp 2 (fun _ : Fin (r + 1) => CanonicalL2 S K m) →ₗ[ℝ]
      PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m) where
  toFun v := WithLp.toLp 2 (fun j => v (n05CanonicalJetIndexOfLE hsr j))
  map_add' := by
    intro u v
    apply (WithLp.ext_iff 2).mpr
    funext j
    rfl
  map_smul' := by
    intro c v
    apply (WithLp.ext_iff 2).mpr
    funext j
    rfl

@[simp] theorem n05CanonicalJetRestrictCoordinate_apply (S : PhysicalSpacesData)
    (K : CanonicalData S) {s r : ℕ} (hsr : s ≤ r) (m : ℕ)
    (v : PiLp 2 (fun _ : Fin (r + 1) => CanonicalL2 S K m))
    (j : Fin (s + 1)) :
    n05CanonicalJetRestrictCoordinate S K hsr m v j =
      v (n05CanonicalJetIndexOfLE hsr j) := rfl

theorem n05CanonicalJetRestrictCoordinate_bound (S : PhysicalSpacesData)
    (K : CanonicalData S) {s r : ℕ} (hsr : s ≤ r) (m : ℕ)
    (v : PiLp 2 (fun _ : Fin (r + 1) => CanonicalL2 S K m)) :
    ‖n05CanonicalJetRestrictCoordinate S K hsr m v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  calc
    (∑ j : Fin (s + 1), ‖n05CanonicalJetRestrictCoordinate S K hsr m v j‖ ^ 2) =
        ∑ j ∈ Finset.univ.map (n05CanonicalJetIndexOfLE hsr), ‖v j‖ ^ 2 := by
      simp only [Finset.sum_map, n05CanonicalJetRestrictCoordinate_apply]
    _ ≤ ∑ j : Fin (r + 1), ‖v j‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)

def n05CanonicalJetRestrictRaw (S : PhysicalSpacesData) (K : CanonicalData S)
    {s r : ℕ} (hsr : s ≤ r) :
    CanonicalVolumeJets S K r →L[ℝ] CanonicalVolumeJets S K s :=
  n05LpMapCLM (n05CanonicalJetRestrictCoordinate S K hsr) 1 zero_le_one (by
    intro m v
    simpa only [one_mul] using n05CanonicalJetRestrictCoordinate_bound S K hsr m v)

@[simp] theorem n05CanonicalJetRestrictRaw_apply (S : PhysicalSpacesData)
    (K : CanonicalData S) {s r : ℕ} (hsr : s ≤ r)
    (v : CanonicalVolumeJets S K r) (m : ℕ) (j : Fin (s + 1)) :
    n05CanonicalJetRestrictRaw S K hsr v m j = v m (n05CanonicalJetIndexOfLE hsr j) := by
  rw [n05CanonicalJetRestrictRaw, n05LpMapCLM_apply,
    n05CanonicalJetRestrictCoordinate_apply]

theorem n05CanonicalJetRestrictRaw_bound (S : PhysicalSpacesData)
    (K : CanonicalData S) {s r : ℕ} (hsr : s ≤ r) (v : CanonicalVolumeJets S K r) :
    ‖n05CanonicalJetRestrictRaw S K hsr v‖ ≤ ‖v‖ := by
  simpa only [n05CanonicalJetRestrictRaw, one_mul] using n05LpMapCLM_bound
    (n05CanonicalJetRestrictCoordinate S K hsr) 1 zero_le_one (by
      intro m u
      simpa only [one_mul] using n05CanonicalJetRestrictCoordinate_bound S K hsr m u) v

theorem n05CanonicalJetRestrictRaw_preserves_graph (S : PhysicalSpacesData)
    (K : CanonicalData S) {s r : ℕ} (hsr : s ≤ r) {v : CanonicalVolumeJets S K r}
    (hv : v ∈ canonicalVolumeGraph S K r) :
    n05CanonicalJetRestrictRaw S K hsr v ∈ canonicalVolumeGraph S K s := by
  refine ⟨?_, ?_⟩
  · intro m
    simpa only [n05CanonicalJetRestrictRaw_apply, n05CanonicalJetIndexOfLE_zero]
      using hv.1 m
  · intro m j
    simpa only [n05CanonicalJetRestrictRaw_apply, n05CanonicalJetIndexOfLE_zero,
      n05CanonicalJetIndexOfLE_val] using hv.2 m (n05CanonicalJetIndexOfLE hsr j)

def n05CanonicalJetRestrict (S : PhysicalSpacesData) (K : CanonicalData S)
    {s r : ℕ} (hsr : s ≤ r) :
    n05CanonicalClosedSubmodule S K r →L[ℝ] n05CanonicalClosedSubmodule S K s :=
  ((n05CanonicalJetRestrictRaw S K hsr).comp
    (n05CanonicalClosedSubmodule S K r).subtypeL).codRestrict
      (n05CanonicalClosedSubmodule S K s) (by
        intro v
        rw [← SetLike.mem_coe, n05CanonicalClosedSubmodule_carrier]
        apply n05CanonicalJetRestrictRaw_preserves_graph S K hsr
        rw [← n05CanonicalClosedSubmodule_carrier]
        exact v.property)

@[simp] theorem n05CanonicalJetRestrict_apply (S : PhysicalSpacesData)
    (K : CanonicalData S) {s r : ℕ} (hsr : s ≤ r)
    (v : n05CanonicalClosedSubmodule S K r) (m : ℕ) (j : Fin (s + 1)) :
    (n05CanonicalJetRestrict S K hsr v).val m j =
      v.val m (n05CanonicalJetIndexOfLE hsr j) :=
  n05CanonicalJetRestrictRaw_apply S K hsr v.val m j

theorem n05CanonicalJetRestrict_bound (S : PhysicalSpacesData)
    (K : CanonicalData S) {s r : ℕ} (hsr : s ≤ r) (v : n05CanonicalClosedSubmodule S K r) :
    ‖n05CanonicalJetRestrict S K hsr v‖ ≤ ‖v‖ :=
  n05CanonicalJetRestrictRaw_bound S K hsr v.val

def n05CanonicalVolumeRestrict (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γ t : ℝ) {s r : ℕ} (hsr : s ≤ r) :
    (n05CanonicalVolumeModel T S K).level γ t r →L[ℝ]
      (n05CanonicalVolumeModel T S K).level γ t s :=
  n05CanonicalJetRestrict S K hsr

theorem n05CanonicalVolumeRestrict_forget (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γ t : ℝ) {s r : ℕ} (hsr : s ≤ r)
    (v : (n05CanonicalVolumeModel T S K).level γ t r) :
    (n05CanonicalVolumeModel T S K).forget γ t s
      (n05CanonicalVolumeRestrict T S K γ t hsr v) =
        (n05CanonicalVolumeModel T S K).forget γ t r v := by
  funext m
  simp only [n05CanonicalVolumeModel_forget, n05CanonicalVolumeRestrict]
  have hj := n05CanonicalJetRestrict_apply S K hsr
    (show n05CanonicalClosedSubmodule S K r from v) m 0
  rw [n05CanonicalJetIndexOfLE_zero] at hj
  exact congrArg (fun z : CanonicalL2 S K m =>
    (T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ) • z) hj

theorem n05CanonicalVolumeMember_restrict (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γ t : ℝ) {s r : ℕ} (hsr : s ≤ r)
    {f : CanonicalSequence S K}
    (hf : VolumeMember S K (n05CanonicalVolumeModel T S K) γ t r f) :
    VolumeMember S K (n05CanonicalVolumeModel T S K) γ t s f := by
  obtain ⟨v, hv⟩ := hf
  exact ⟨n05CanonicalVolumeRestrict T S K γ t hsr v,
    (n05CanonicalVolumeRestrict_forget T S K γ t hsr v).trans hv⟩

theorem n05CanonicalVolumeMember_embed {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hPart : RadialPartition D) (S : PhysicalSpacesData)
    (K : CanonicalData S) {γlo γhi : ℝ} (hγ : γlo < γhi) (tlo thi : ℝ) (s : ℕ)
    {f : CanonicalSequence S K}
    (hf : VolumeMember S K (n05CanonicalVolumeModel T S K) γhi thi s f) :
    VolumeMember S K (n05CanonicalVolumeModel T S K) γlo tlo s f := by
  obtain ⟨v, hv⟩ := hf
  exact ⟨n05CanonicalVolumeEmbed hT hPart S K hγ tlo thi s v,
    (n05CanonicalVolumeEmbed_forget hT hPart S K hγ tlo thi s v).trans hv⟩

end ContinuousFlexibility.Statements
