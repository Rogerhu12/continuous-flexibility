import ContinuousFlexibility.Analysis.N05CanonicalUniqueness

/-!
# The canonical volume model with its prescribed forget map

The weighted levels use the actual closed weak angular graph. Multiplication
by the positive piece weights recovers the unweighted sequence. Uniqueness
of weak derivatives makes this recovery injective at each finite level.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

def n05CanonicalForget (T : MaterialData) (S : PhysicalSpacesData) (K : CanonicalData S)
    (γ t : ℝ) (s : ℕ) :
    n05CanonicalClosedSubmodule S K s →ₗ[ℝ] CanonicalSequence S K :=
  LinearMap.pi fun m =>
    (T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ) •
      (n05CanonicalJetCoordinate S K s m 0).toLinearMap.comp
        (n05CanonicalClosedSubmodule S K s).subtype

theorem n05CanonicalForget_apply (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γ t : ℝ) (s : ℕ)
    (v : n05CanonicalClosedSubmodule S K s) (m : ℕ) :
    n05CanonicalForget T S K γ t s v m =
      (T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ) •
        (v.val m 0) := by
  simp only [n05CanonicalForget, LinearMap.pi_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, Submodule.subtype_apply, ContinuousLinearMap.coe_coe,
    n05CanonicalJetCoordinate_apply]

theorem n05CanonicalForget_injective (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (hM : ∀ m, 0 < T.M (T.sample m))
    (hH : ∀ m, 0 < T.H (T.sample m)) (γ t : ℝ) (s : ℕ) :
    Function.Injective (n05CanonicalForget T S K γ t s) := by
  intro u v huv
  have hu : u.val ∈ canonicalVolumeGraph S K s := by
    rw [← n05CanonicalClosedSubmodule_carrier S K s]
    exact u.property
  have hv : v.val ∈ canonicalVolumeGraph S K s := by
    rw [← n05CanonicalClosedSubmodule_carrier S K s]
    exact v.property
  apply Subtype.ext
  apply lp.ext
  funext m
  apply (WithLp.ext_iff 2).mpr
  funext j
  have hzero : u.val m 0 = v.val m 0 := by
    let w : ℝ := T.M (T.sample (K.cell m)) ^ (-t) *
      T.H (T.sample (K.cell m)) ^ γ
    have hw : w ≠ 0 :=
      (mul_pos (Real.rpow_pos_of_pos (hM (K.cell m)) (-t))
        (Real.rpow_pos_of_pos (hH (K.cell m)) γ)).ne'
    have hm := congrFun huv m
    rw [n05CanonicalForget_apply, n05CanonicalForget_apply] at hm
    change w • u.val m 0 = w • v.val m 0 at hm
    have hc := congrArg (fun z : CanonicalL2 S K m => w⁻¹ • z) hm
    simpa only [smul_smul, inv_mul_cancel₀ hw, one_smul] using hc
  have hd := hu.2 m j
  rw [hzero] at hd
  exact n05WeakCanonicalAngularDerivative_unique hd (hv.2 m j)

def n05CanonicalVolumeModel (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) : VolumeModelData S K where
  level := fun _ _ s => n05CanonicalClosedSubmodule S K s
  forget := n05CanonicalForget T S K

theorem n05CanonicalVolumeModel_forget (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γ t : ℝ) (s : ℕ)
    (v : (n05CanonicalVolumeModel T S K).level γ t s) (m : ℕ) :
    (n05CanonicalVolumeModel T S K).forget γ t s v m =
      (T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ) •
        (v.val m 0) :=
  n05CanonicalForget_apply T S K γ t s v m

theorem n05CanonicalVolumeModel_isVolumeModel (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (hM : ∀ m, 0 < T.M (T.sample m))
    (hH : ∀ m, 0 < T.H (T.sample m)) :
    IsVolumeModel T S K (n05CanonicalVolumeModel T S K) := by
  refine ⟨fun _ _ s => n05CanonicalClosedSubmodule_carrier S K s,
    fun _ _ s => n05CanonicalClosedSubmodule_isClosed S K s,
    fun γ t s => n05CanonicalForget_injective T S K hM hH γ t s,
    fun γ t s v m => n05CanonicalVolumeModel_forget T S K γ t s v m⟩

theorem exists_n05CanonicalVolumeModel {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (S : PhysicalSpacesData) (K : CanonicalData S) :
    ∃ V : VolumeModelData S K, IsVolumeModel T S K V := by
  rcases hT with ⟨_, hpos, _, _, _, _, _, _, _, _, _, _, _, _, _, hsample, _⟩
  have hpart : RadialPartition D := hD.choose_spec.2.1
  have hs (m : ℕ) : T.sample m ∈ Ioo D.a D.b :=
    hpart.2.2.2.1 m (hsample m)
  refine ⟨n05CanonicalVolumeModel T S K,
    n05CanonicalVolumeModel_isVolumeModel T S K ?_ ?_⟩
  · intro m
    exact zero_lt_one.trans_le (hpos (T.sample m) (hs m)).2.2.2
  · intro m
    exact (hpos (T.sample m) (hs m)).2.1

end ContinuousFlexibility.Statements
