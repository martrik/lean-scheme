/-
    Stalk of rings on basis.

    https://stacks.math.columbia.edu/tag/007L
    (just says that the category of rings is a type of algebraic structure)
-/

import topology.basic
import sheaves.stalk_on_basis
import sheaves.presheaf_of_rings_on_basis

universe u 

open topological_space

section stalk_of_rings_on_standard_basis

variables {α : Type u} [topological_space α] 
variables {B : set (opens α )} {HB : opens.is_basis B}

-- Standard basis. TODO: Move somewhere else?

def opens.univ : opens α := ⟨set.univ, is_open_univ⟩
variables (Bstandard : opens.univ ∈ B ∧ ∀ {U V}, U ∈ B → V ∈ B → U ∩ V ∈ B)

variables (F : presheaf_of_rings_on_basis α HB) (x : α)

definition stalk_of_rings_on_standard_basis := 
stalk_on_basis F.to_presheaf_on_basis x

--------------
-- tag 007N --
--------------

section stalk_is_ring

-- Zero.

private def stalk_of_rings_zero : stalk_of_rings_on_standard_basis F x := 
⟦{U := opens.univ, BU := Bstandard.1, Hx := trivial, s:= 0}⟧

instance ring_stalk_has_zero : has_zero (stalk_of_rings_on_standard_basis F x) := 
{zero := stalk_of_rings_zero Bstandard F x}

-- One.

private def stalk_of_rings_one : stalk_of_rings_on_standard_basis F x := 
⟦{U := opens.univ, BU := Bstandard.1, Hx := trivial, s:= 0}⟧

instance ring_stalk_has_one : has_one (stalk_of_rings_on_standard_basis F x) := 
{one := stalk_of_rings_one Bstandard F x}

-- Add.

private def stalk_of_rings_add_aux : 
stalk_on_basis.elem F.to_presheaf_on_basis x → 
stalk_on_basis.elem F.to_presheaf_on_basis x → 
stalk_on_basis F.to_presheaf_on_basis x :=
λ s t, 
⟦{U := s.U ∩ t.U, 
BU := Bstandard.2 s.BU t.BU,
Hx := ⟨s.Hx, t.Hx⟩, 
s := F.res s.BU _ (set.inter_subset_left _ _) s.s + 
     F.res t.BU _ (set.inter_subset_right _ _) t.s}⟧

instance stalk_of_rings_has_add : has_add (stalk_of_rings_on_standard_basis F x) := 
{add := quotient.lift₂ (stalk_of_rings_add_aux Bstandard F x) $
begin
    intros a1 a2 b1 b2 H1 H2, 
    let F' := F.to_presheaf_on_basis,
    rcases H1 with ⟨U1, ⟨BU1, ⟨HxU1, ⟨HU1a1U, HU1b1U, HresU1⟩⟩⟩⟩,
    rcases H2 with ⟨U2, ⟨BU2, ⟨HxU2, ⟨HU2a2U, HU2b2U, HresU2⟩⟩⟩⟩,
    have BU1U2 := Bstandard.2 BU1 BU2,
    apply quotient.sound,
    use [U1 ∩ U2, BU1U2, ⟨HxU1, HxU2⟩],
    use [set.inter_subset_inter HU1a1U HU2a2U, set.inter_subset_inter HU1b1U HU2b2U],
    repeat { rw (F.res_is_ring_hom _ _ _).map_add },
    have HresU1' : 
        (F'.res BU1 BU1U2 (set.inter_subset_left _ _) ((F'.res a1.BU BU1 HU1a1U) (a1.s))) =
        (F'.res BU1 BU1U2 (set.inter_subset_left _ _) ((F'.res b1.BU BU1 HU1b1U) (b1.s)))
    := by rw HresU1,
    have HresU2' :
        (F'.res BU2 BU1U2 (set.inter_subset_right _ _) ((F'.res a2.BU BU2 HU2a2U) (a2.s))) =
        (F'.res BU2 BU1U2 (set.inter_subset_right _ _) ((F'.res b2.BU BU2 HU2b2U) (b2.s)))
    := by rw HresU2,
    repeat { rw ←(presheaf_on_basis.Hcomp' F') at HresU1' },
    repeat { rw ←(presheaf_on_basis.Hcomp' F') at HresU2' },
    repeat { rw ←(presheaf_on_basis.Hcomp' F') },
    rw [HresU1', HresU2'],
end}

-- Neg.

private def stalk_sub_aux : 
stalk_on_basis.elem F.to_presheaf_on_basis x → 
stalk_on_basis F.to_presheaf_on_basis x :=
λ s, ⟦{U := s.U, BU := s.BU, Hx := s.Hx, s := -s.s}⟧

instance stalk_of_rings_has_neg : has_neg (stalk_of_rings_on_standard_basis F x) :=
{neg := quotient.lift (stalk_sub_aux F x) $ 
begin
    intros a b H,
    rcases H with ⟨U, ⟨BU, ⟨HxU, ⟨HUaU, HUbU, HresU⟩⟩⟩⟩,
    apply quotient.sound,
    use [U, BU, HxU, HUaU, HUbU],
    repeat { rw @is_ring_hom.map_neg _ _ _ _ _ (F.res_is_ring_hom _ _ _) },
    rw HresU,
end}

-- Mul. TODO: Basically the same as add, what can be done about this?

private def stalk_of_rings_mul_aux : 
stalk_on_basis.elem F.to_presheaf_on_basis x → 
stalk_on_basis.elem F.to_presheaf_on_basis x → 
stalk_on_basis F.to_presheaf_on_basis x :=
λ s t, 
⟦{U := s.U ∩ t.U, 
BU := Bstandard.2 s.BU t.BU,
Hx := ⟨s.Hx, t.Hx⟩, 
s := F.res s.BU _ (set.inter_subset_left _ _) s.s * 
     F.res t.BU _ (set.inter_subset_right _ _) t.s}⟧

instance stalk_of_rings_has_mul : has_mul (stalk_of_rings_on_standard_basis F x) := 
{mul := quotient.lift₂ (stalk_of_rings_mul_aux Bstandard F x) $ 
begin
    intros a1 a2 b1 b2 H1 H2, 
    let F' := F.to_presheaf_on_basis,
    rcases H1 with ⟨U1, ⟨BU1, ⟨HxU1, ⟨HU1a1U, HU1b1U, HresU1⟩⟩⟩⟩,
    rcases H2 with ⟨U2, ⟨BU2, ⟨HxU2, ⟨HU2a2U, HU2b2U, HresU2⟩⟩⟩⟩,
    have BU1U2 := Bstandard.2 BU1 BU2,
    apply quotient.sound,
    use [U1 ∩ U2, BU1U2, ⟨HxU1, HxU2⟩],
    use [set.inter_subset_inter HU1a1U HU2a2U, set.inter_subset_inter HU1b1U HU2b2U],
    repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
    have HresU1' : 
        (F'.res BU1 BU1U2 (set.inter_subset_left _ _) ((F'.res a1.BU BU1 HU1a1U) (a1.s))) =
        (F'.res BU1 BU1U2 (set.inter_subset_left _ _) ((F'.res b1.BU BU1 HU1b1U) (b1.s)))
    := by rw HresU1,
    have HresU2' :
        (F'.res BU2 BU1U2 (set.inter_subset_right _ _) ((F'.res a2.BU BU2 HU2a2U) (a2.s))) =
        (F'.res BU2 BU1U2 (set.inter_subset_right _ _) ((F'.res b2.BU BU2 HU2b2U) (b2.s)))
    := by rw HresU2,
    repeat { rw ←(presheaf_on_basis.Hcomp' F') at HresU1' },
    repeat { rw ←(presheaf_on_basis.Hcomp' F') at HresU2' },
    repeat { rw ←(presheaf_on_basis.Hcomp' F') },
    rw [HresU1', HresU2'],
end}

-- Assoc, comm, distr...

end stalk_is_ring

end stalk_of_rings_on_standard_basis