module

public import ContinuousFlexibility.Analysis.N05CanonicalZeroExtension
public import ContinuousFlexibility.Analysis.CylinderTestPeriodization
public import ContinuousFlexibility.Analysis.SpacesCylinderEvenJets

/-!
# A fixed even periodic representative of each canonical source coordinate

Zero extension to the actual cylinder and its genuine periodic extension
supply a representative without any smoothness assumption. Reflection
averaging makes its angular symmetries pointwise. On the reflection-fixed
canonical subspace this representative is the original L² equivalence class.
The construction depends only on that class, not on a weight or jet order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory

def n05CanonicalPeriodicRepresentative (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) (u : CanonicalL2 S K m) :
    PolarPoint → ℝ :=
  cylinderPeriodicExtension (n05CanonicalZeroExtension S K m u)

theorem n05CanonicalPeriodicRepresentative_periodic (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) (u : CanonicalL2 S K m) :
    Function.Periodic (n05CanonicalPeriodicRepresentative S K m u) (0, Real.pi) :=
  cylinderPeriodicExtension_periodic _

theorem n05CanonicalPeriodicRepresentative_ae (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) (u : CanonicalL2 S K m) :
    n05CanonicalPeriodicRepresentative S K m u
      =ᵐ[canonicalMeasure S K m] (u : PolarPoint → ℝ) := by
  have he := (cylinderPeriodicExtension_ae (n05CanonicalZeroExtension S K m u)).trans
    (n05CanonicalZeroExtension_ae S K m u)
  have hfilter : ae (canonicalMeasure S K m) =
      ae (materialCylinderMeasure.restrict (n05CanonicalRadialWindow S K m)) :=
    congrArg (fun μ : Measure PolarPoint => ae μ)
      (n05CanonicalMeasure_eq_cylinder_restrict S K m).symm
  rw [hfilter]
  filter_upwards [he.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem (n05CanonicalRadialWindow_measurable S K m)] with p hp hw
  simpa only [n05CanonicalPeriodicRepresentative, indicator_of_mem hw] using hp

/-- One fixed representative for all material weights and angular orders. -/
def n05CanonicalEvenPeriodicRepresentative (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) (u : CanonicalL2 S K m) :
    PolarPoint → ℝ :=
  spacesCylinderEvenFunction (n05CanonicalPeriodicRepresentative S K m u)

theorem n05CanonicalEvenPeriodicRepresentative_periodic (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) (u : CanonicalL2 S K m) :
    Function.Periodic (n05CanonicalEvenPeriodicRepresentative S K m u) (0, Real.pi) :=
  spacesCylinderEvenFunction_periodic (n05CanonicalPeriodicRepresentative_periodic S K m u)

theorem n05CanonicalEvenPeriodicRepresentative_reflection (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) (u : CanonicalL2 S K m) (p : PolarPoint) :
    n05CanonicalEvenPeriodicRepresentative S K m u (p.1, Real.pi - p.2) =
      n05CanonicalEvenPeriodicRepresentative S K m u p :=
  spacesCylinderEvenFunction_reflection _ p

theorem n05CanonicalEvenPeriodicRepresentative_even (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) (u : CanonicalL2 S K m) (r : ℝ) :
    Function.Even (fun θ => n05CanonicalEvenPeriodicRepresentative S K m u (r, θ)) := by
  intro θ
  have hp := n05CanonicalEvenPeriodicRepresentative_periodic S K m u (r, -θ)
  simp only [Prod.mk_add_mk, add_zero] at hp
  calc
    _ = n05CanonicalEvenPeriodicRepresentative S K m u (r, Real.pi - θ) := by
      rw [show Real.pi - θ = -θ + Real.pi by ring]
      exact hp.symm
    _ = _ := n05CanonicalEvenPeriodicRepresentative_reflection S K m u (r, θ)

theorem n05CanonicalEvenPeriodicRepresentative_ae_average (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) (u : CanonicalL2 S K m) :
    n05CanonicalEvenPeriodicRepresentative S K m u =ᵐ[canonicalMeasure S K m]
      spacesCylinderEvenFunction (u : PolarPoint → ℝ) := by
  have he := n05CanonicalPeriodicRepresentative_ae S K m u
  have hr := (n05CanonicalReflection_measurePreserving S K m).quasiMeasurePreserving.ae_eq_comp he
  filter_upwards [he, hr] with p hp hr
  change n05CanonicalPeriodicRepresentative S K m u (p.1, Real.pi - p.2) =
    u (p.1, Real.pi - p.2) at hr
  simp only [n05CanonicalEvenPeriodicRepresentative, spacesCylinderEvenFunction, hp, hr]

/-- The zero-order symmetry in the frozen graph is exactly the hypothesis
needed for the representative to recover the actual canonical L² class. -/
theorem n05CanonicalEvenPeriodicRepresentative_ae {S : PhysicalSpacesData}
    {K : CanonicalData S} {m : ℕ} (u : CanonicalL2 S K m)
    (hu : (fun p : PolarPoint => u (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (u : PolarPoint → ℝ)) :
    n05CanonicalEvenPeriodicRepresentative S K m u
      =ᵐ[canonicalMeasure S K m] (u : PolarPoint → ℝ) := by
  filter_upwards [n05CanonicalEvenPeriodicRepresentative_ae_average S K m u, hu]
    with p hp he
  rw [hp]
  dsimp only [spacesCylinderEvenFunction]
  rw [he]
  ring

theorem n05CanonicalEvenPeriodicRepresentative_memLp {S : PhysicalSpacesData}
    {K : CanonicalData S} {m : ℕ} (u : CanonicalL2 S K m)
    (hu : (fun p : PolarPoint => u (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (u : PolarPoint → ℝ)) :
    MemLp (n05CanonicalEvenPeriodicRepresentative S K m u) 2 (canonicalMeasure S K m) :=
  MemLp.ae_eq (n05CanonicalEvenPeriodicRepresentative_ae u hu).symm (Lp.memLp u)

/-- Every forgotten source in an actual volume level has the required
zero-order reflection symmetry, including its prescribed sample weight. -/
theorem n05_volumeMember_reflection {T : MaterialData} {S : PhysicalSpacesData}
    {K : CanonicalData S} {V : VolumeModelData S K}
    (hV : IsVolumeModel T S K V) {γ t : ℝ} {s : ℕ}
    {F : CanonicalSequence S K} (hF : VolumeMember S K V γ t s F) (m : ℕ) :
    (fun p : PolarPoint => F m (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (F m : PolarPoint → ℝ) := by
  obtain ⟨v, hv⟩ := hF
  have hgraph : v.val ∈ canonicalVolumeGraph S K s := by
    rw [← hV.1 γ t s]
    exact v.prop
  have hfixed : n05CanonicalReflection S K m (v.val m 0) = v.val m 0 :=
    (n05CanonicalReflection_fixed_iff S K m _).mpr (hgraph.1 m)
  have hweighted : n05CanonicalReflection S K m (V.forget γ t s v m) =
      V.forget γ t s v m := by
    rw [hV.2.2.2 γ t s v m, map_smul, hfixed]
  rw [← hv]
  exact (n05CanonicalReflection_fixed_iff S K m _).mp hweighted

end ContinuousFlexibility.Statements
