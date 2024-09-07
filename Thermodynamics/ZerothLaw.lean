import Mathlib.Data.Real.EReal

/-!
# The ZEROTH Law

This file defines
* the notion of mutual thermal equilibriumm (`mutualEquil`)
* the notion of abstract heat `Reservoir`
and states
* the axioms of the zeroth law, including
  `mutualEquil.iseqv` : `mutualEquil` is an equivalence relation, and
  `Reservoir.linearOrder` : there is a linear order defined on `Reservoir`
-/

namespace Thermodynamics

axiom EquilSystem : Type
axiom waterTriplePoint : EquilSystem
axiom CO2TriplePoint : EquilSystem
noncomputable instance : Inhabited EquilSystem := ⟨waterTriplePoint⟩

axiom mutualEquil : EquilSystem → EquilSystem → Prop
/--
* The core axiom is the transitivity of `mutualEquil`.
-/
axiom mutualEquil.iseqv : Equivalence mutualEquil
instance EquilSystem.setoid : Setoid EquilSystem :=
  ⟨mutualEquil, mutualEquil.iseqv⟩

/-- Identify the equivalence classes of `mutualEquil` with heat `Reservoir`s.
    `Reservoir` is abbreviated as `rsv`.
    `Reservoir`s are denoted by uppercase script letters like `𝓣`. -/
@[reducible] def Reservoir := Quotient EquilSystem.setoid
/--
* `<` means "colder than".
* The core axiom is the existence of an order and its transitivity.
-/
@[instance] axiom Reservoir.linearOrder : LinearOrder Reservoir
axiom triple_point_CO2_lt_water : (⟦CO2TriplePoint⟧:Reservoir) < ⟦waterTriplePoint⟧

end Thermodynamics
