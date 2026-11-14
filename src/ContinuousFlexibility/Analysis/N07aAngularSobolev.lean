module

public import ContinuousFlexibility.Analysis.N07aAngularHilbert
public import ContinuousFlexibility.Analysis.N07aAngularBandNorm

/-!
# The full prescribed angular source scale and spectral Sobolev regularity

Every higher source level maps to the corresponding spectral Sobolev
domain. Conversely, a spectrally regular vector in the base source level
is reconstructed in the original higher weak graph. Both norm bounds
refer to the actual prescribed source norms, and their constants are
independent of the base order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

variable {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
  {V : VolumeModelData S K}
  (hV : IsVolumeModel T S K V) (γ w : ℝ)
  (hK : ∀ m, K.left m < K.right m)

local instance (s : ℕ) : NormedAddCommGroup (V.level γ w s) := Submodule.normedAddCommGroup _
local instance (s : ℕ) : NormedSpace ℝ (V.level γ w s) := Submodule.normedSpace _
local instance (s : ℕ) : InnerProductSpace ℝ (V.level γ w s) := Submodule.innerProductSpace _
local instance (s n : ℕ) : NormedAddCommGroup (n07aAngularBandSpace hV γ w hK s n) :=
  Submodule.normedAddCommGroup _
local instance (s n : ℕ) : NormedSpace ℝ (n07aAngularBandSpace hV γ w hK s n) :=
  Submodule.normedSpace _
local instance (s n : ℕ) : InnerProductSpace ℝ (n07aAngularBandSpace hV γ w hK s n) :=
  Submodule.innerProductSpace _
local instance (s : ℕ) : NormedAddCommGroup
    (lp (fun n => n07aAngularBandSpace hV γ w hK s n) 2) := lp.normedAddCommGroup
local instance (s : ℕ) : NormedSpace ℝ
    (lp (fun n => n07aAngularBandSpace hV γ w hK s n) 2) := lp.instNormedSpace
local instance (s : ℕ) : InnerProductSpace ℝ
    (lp (fun n => n07aAngularBandSpace hV γ w hK s n) 2) := lp.instInnerProductSpace

theorem n07aAngularHilbertEquiv_coordinate_norm (s : ℕ) (u : V.level γ w s) (n : ℕ) :
    ‖n07aAngularHilbertEquiv hV γ w hK s u n‖ =
      ‖n07aAngularLevelBand hV γ w hK s n u‖ :=
  (Submodule.norm_coe (n07aAngularHilbertEquiv hV γ w hK s u n)).symm.trans
    (congrArg (fun v : V.level γ w s => ‖v‖)
      (n07aAngularHilbertEquiv_apply_val hV γ w hK s u n))

theorem n07aAngularTruncatedBand_norm_le (b p : ℕ) (u : V.level γ w (b + p)) (n : ℕ) :
    angularWeight n ^ p *
        ‖n07aAngularHilbertEquiv hV γ w hK b
          (n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p) u) n‖ ≤
      ‖n07aAngularHilbertEquiv hV γ w hK (b + p) u n‖ := by
  calc
    angularWeight n ^ p *
        ‖n07aAngularHilbertEquiv hV γ w hK b
          (n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p) u) n‖ =
        angularWeight n ^ p * ‖n07aAngularLevelBand hV γ w hK b n
          (n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p) u)‖ :=
      congrArg (fun x : ℝ => angularWeight n ^ p * x)
        (n07aAngularHilbertEquiv_coordinate_norm hV γ w hK b _ n)
    _ ≤ ‖n07aAngularLevelLift hV γ w hK b (b + p) n
        (n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p) u)‖ :=
      n07aAngularLevelLift_norm_lower hV γ w hK b p n _
    _ = ‖n07aAngularLevelBand hV γ w hK (b + p) n u‖ :=
      congrArg (fun v : V.level γ w (b + p) => ‖v‖)
        (n07aAngularLevelLift_of_truncate hV γ w hK (Nat.le_add_right b p) n u)
    _ = _ := (n07aAngularHilbertEquiv_coordinate_norm hV γ w hK (b + p) u n).symm

theorem n07aAngularTruncate_memSobolev (b p : ℕ) (u : V.level γ w (b + p)) :
    MemAngularSobolev (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b
      (n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p) u)) := by
  apply (lp.memℓp (n07aAngularHilbertEquiv hV γ w hK (b + p) u)).mono'
  intro n
  simpa only [RCLike.ofReal_real_eq_id, id_eq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (angularWeight_nonneg n) p)] using
    n07aAngularTruncatedBand_norm_le hV γ w hK b p u n

theorem n07aAngularTruncate_sobolevNorm_le (b p : ℕ) (u : V.level γ w (b + p)) :
    angularSobolevNorm (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b
      (n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p) u)) ≤ ‖u‖ := by
  let z := angularWeightedVector p
    (n07aAngularHilbertEquiv hV γ w hK b
      (n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p) u))
    (n07aAngularTruncate_memSobolev hV γ w hK b p u)
  have hnorm : ‖z‖ ≤ ‖n07aAngularHilbertEquiv hV γ w hK (b + p) u‖ := by
    apply lp.norm_mono (by norm_num)
    intro n
    simpa only [z, angularWeightedVector_apply, RCLike.ofReal_real_eq_id, id_eq, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (angularWeight_nonneg n) p)] using
      n07aAngularTruncatedBand_norm_le hV γ w hK b p u n
  simpa only [z, norm_angularWeightedVector, LinearIsometryEquiv.norm_map] using hnorm

def n07aAngularHigherBand (b p n : ℕ) (u : n07aAngularBandSpace hV γ w hK b n) :
    n07aAngularBandSpace hV γ w hK (b + p) n :=
  ⟨n07aAngularLevelLift hV γ w hK b (b + p) n u.val,
    (n07aAngularBandSpace_mem_iff hV γ w hK (b + p) n _).mpr
      (n07aAngularLevelLift_band hV γ w hK b (b + p) n u.val)⟩

@[simp] theorem n07aAngularHigherBand_val (b p n : ℕ)
    (u : n07aAngularBandSpace hV γ w hK b n) :
    (n07aAngularHigherBand hV γ w hK b p n u).val =
      n07aAngularLevelLift hV γ w hK b (b + p) n u.val := rfl

theorem n07aAngularHigherBand_truncate (b p n : ℕ)
    (u : n07aAngularBandSpace hV γ w hK b n) :
    n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p)
      (n07aAngularHigherBand hV γ w hK b p n u).val = u.val :=
  (n07aAngularLevelLift_truncate hV γ w hK (Nat.le_add_right b p) n u.val).trans
    ((n07aAngularBandSpace_mem_iff hV γ w hK b n u.val).mp u.property)

theorem n07aAngularHigherBand_norm_le (b p n : ℕ)
    (u : n07aAngularBandSpace hV γ w hK b n) :
    ‖n07aAngularHigherBand hV γ w hK b p n u‖ ≤
      n07aAngularLiftConstant p * angularWeight n ^ p * ‖u‖ := by
  have hu := (n07aAngularBandSpace_mem_iff hV γ w hK b n u.val).mp u.property
  calc
    ‖n07aAngularHigherBand hV γ w hK b p n u‖ =
        ‖n07aAngularLevelLift hV γ w hK b (b + p) n u.val‖ :=
      (Submodule.norm_coe (n07aAngularHigherBand hV γ w hK b p n u)).symm
    _ ≤ n07aAngularLiftConstant p * angularWeight n ^ p *
        ‖n07aAngularLevelBand hV γ w hK b n u.val‖ :=
      n07aAngularLevelLift_norm_upper hV γ w hK b p n u.val
    _ = n07aAngularLiftConstant p * angularWeight n ^ p * ‖u.val‖ :=
      congrArg (fun v : V.level γ w b => n07aAngularLiftConstant p * angularWeight n ^ p * ‖v‖) hu
    _ = _ := congrArg (fun x : ℝ => n07aAngularLiftConstant p * angularWeight n ^ p * x)
      (Submodule.norm_coe u)

/-- Spectral regularity constructs an actual vector in the higher frozen weak graph. -/
theorem n07aAngularSobolev_exists_lift (b p : ℕ) (u : V.level γ w b)
    (hu : MemAngularSobolev (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b u)) :
    ∃ v : V.level γ w (b + p),
      n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p) v = u ∧
      ‖v‖ ≤ n07aAngularLiftConstant p *
        angularSobolevNorm (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b u) := by
  let c := n07aAngularHilbertEquiv hV γ w hK b u
  let z := angularWeightedVector p c hu
  let d : (n : ℕ) → n07aAngularBandSpace hV γ w hK (b + p) n := fun n =>
    n07aAngularHigherBand hV γ w hK b p n (c n)
  have hd (n : ℕ) : ‖d n‖ ≤ n07aAngularLiftConstant p * ‖z n‖ := by
    simpa only [d, z, angularWeightedVector_apply, RCLike.ofReal_real_eq_id, id_eq,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (angularWeight_nonneg n) p),
      mul_assoc] using n07aAngularHigherBand_norm_le hV γ w hK b p n (c n)
  have hdmem : Memℓp d 2 :=
    (lp.memℓp (n07aAngularLiftConstant p • z)).mono' (fun n => by
      simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (n07aAngularLiftConstant_nonneg p)] using hd n)
  let D : lp (fun n => n07aAngularBandSpace hV γ w hK (b + p) n) 2 := ⟨d, hdmem⟩
  let v := (n07aAngularHilbertEquiv hV γ w hK (b + p)).symm D
  refine ⟨v, ?_, ?_⟩
  · have hsum := (n07aAngularHilbertEquiv_symm_hasSum hV γ w hK (b + p) D).map
      (n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p))
      (n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p)).continuous
    have hsum' : HasSum (fun n => (c n).val)
        (n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p) v) := by
      convert hsum using 1
      funext n
      dsimp only [Function.comp_apply, D, d]
      exact (n07aAngularHigherBand_truncate hV γ w hK b p n (c n)).symm
    have hbase : HasSum (fun n => (c n).val) u := by
      simpa only [c, LinearIsometryEquiv.symm_apply_apply] using
        n07aAngularHilbertEquiv_symm_hasSum hV γ w hK b (n07aAngularHilbertEquiv hV γ w hK b u)
    exact hsum'.unique hbase
  · have hnorm : ‖D‖ ≤ ‖n07aAngularLiftConstant p • z‖ := by
      apply lp.norm_mono (by norm_num)
      intro n
      simpa only [D, lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (n07aAngularLiftConstant_nonneg p)] using hd n
    simpa only [v, LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (n07aAngularLiftConstant_nonneg p), z,
      norm_angularWeightedVector, c] using hnorm

theorem n07aAngularSobolev_iff (b p : ℕ) (u : V.level γ w b) :
    MemAngularSobolev (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b u) ↔
      ∃ v : V.level γ w (b + p), n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p) v = u := by
  constructor
  · intro hu
    obtain ⟨v, hv, _⟩ := n07aAngularSobolev_exists_lift hV γ w hK b p u hu
    exact ⟨v, hv⟩
  · rintro ⟨v, rfl⟩
    exact n07aAngularTruncate_memSobolev hV γ w hK b p v

theorem n07aAngularSobolev_volume_iff (b p : ℕ) (u : V.level γ w b) :
    MemAngularSobolev (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b u) ↔
      VolumeMember S K V γ w (b + p) (V.forget γ w b u) := by
  rw [n07aAngularSobolev_iff]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    rw [← n07aAngularLevelTruncate_forget hV γ w (Nat.le_add_right b p) v, hv]
  · rintro ⟨v, hv⟩
    refine ⟨v, hV.2.2.1 γ w b ?_⟩
    rw [n07aAngularLevelTruncate_forget]
    exact hv

end ContinuousFlexibility.Statements
