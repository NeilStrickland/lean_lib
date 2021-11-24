/- Experiments with coercion of linear maps to maps -/

import data.rat.basic linear_algebra.basic

section zog

parameters {V : Type} [add_comm_group V] [module ℚ V]

def f : V →ₗ[ℚ] V := 
{ to_fun := λ (v : V), v, 
  map_add' := λ (v w : V), rfl,
  map_smul' := λ (c : ℚ) (v : V), rfl }  

#check linear_map.map_add'
#check linear_map.map_add
#check f

def f1 : V → V := (f : V →ₗ[ℚ] V)

#check f1

def f2 (v : V) : V := (f : V →ₗ[ℚ] V) v

#check f2

def f3 (v : V) : V := (f : V → V) v

#check f3

def f4 (v : V) : V := v

def g : V →ₗ[ℚ] V := 
{ to_fun := λ (v : V), v, 
  map_add' := λ (v w : V), rfl,
  map_smul' := λ (c : ℚ) (v : V), rfl }  

def gg (v : V) : V := g v

end zog

